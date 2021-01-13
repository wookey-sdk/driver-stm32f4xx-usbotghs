/*
 *
 * Copyright 2019 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published
 * the Free Software Foundation; either version 3 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
     * with this package; if not, write to the Free Software Foundation, Inc., 51
     * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
     *
     */
#include "autoconf.h"

#include "libc/syscall.h"
#include "libc/stdio.h"
#include "libc/sync.h"
#include "libc/nostd.h"
#include "libc/string.h"

#include "api/libusbotghs.h"
#include "usbotghs.h"
#include "usbotghs_init.h"
#include "usbotghs_fifos.h"
#include "usbotghs_handler.h"
#include "usbotghs_regs.h"
#include "ulpi.h"
#include "generated/usb_otg_hs.h"

#if defined(__FRAMAC__)
#include "socs/stm32f439/usbctrl_backend.h"
#include "libusbctrl.h"
#else
#include "libs/usbctrl/api/libusbctrl.h"
#endif/*!__FRAMAC__*/


#define ZERO_LENGTH_PACKET 0
#define OUT_NAK     0x01
#define DataOUT     0x02
#define Data_Done   0x03
#define SETUP_Done  0x04
#define SETUP       0x06

#define USB_REG_CHECK_TIMEOUT 50
#define MAX_EPx_PKT_SIZE 512

#define USBOTG_HS_RX_FIFO_SZ    512
#define USBOTG_HS_TX_FIFO_SZ    512

#define USBOTG_HS_DEBUG 0






/******************************************************************
 * Defining functional API
 */

static const char *devname = "usb-otg-hs";
/* buffer for setup packets */
// TODO to use static uint8_t   setup_packet[8];

/* local context. Only one as there is one USB OTG device per SoC */

#ifndef __FRAMAC__
/* the static keyword may be removed in replacement with MetACSL anotations specifying
 * that the lonely function handling direct access to this variable is usbotghs_get_context
 */
static usbotghs_context_t usbotghs_ctx = { 0 };
#endif/*!__FRAMAC__*/

/*@
  @ assigns \nothing ;
  @ ensures \result == &usbotghs_ctx ;
  */
usbotghs_context_t *usbotghs_get_context(void)
{
    return &usbotghs_ctx;
}

/* TODO : memset & memcpy with framac */
/*@
  @ requires \separated(&GHOST_nopublicvar, &usbotghs_ctx);
  @ assigns usbotghs_ctx.dev ;
  */
mbed_error_t usbotghs_declare(void)
{
    e_syscall_ret ret = 0;
    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    log_printf("[USBOTG][HS] Declaring device\n");

#if defined(__FRAMAC__)
    /* TODO : memset & memcpy with framac */
#else
    memset((void*)&(usbotghs_ctx.dev), 0, sizeof(device_t));
    memcpy((void*)usbotghs_ctx.dev.name, devname, strlen(devname));
#endif/*!__FRAMAC__*/

    usbotghs_ctx.dev.address = usb_otg_hs_dev_infos.address;
    usbotghs_ctx.dev.size = usb_otg_hs_dev_infos.size;
    usbotghs_ctx.dev.irq_num = 1;
    /* device is mapped voluntary and will be activated after the full
     * authentication sequence
     */
    usbotghs_ctx.dev.map_mode = DEV_MAP_VOLUNTARY;

    /* IRQ configuration */
    usbotghs_ctx.dev.irqs[0].handler = USBOTGHS_IRQHandler;
    usbotghs_ctx.dev.irqs[0].irq = OTG_HS_IRQ; /* starting with STACK */
    usbotghs_ctx.dev.irqs[0].mode = IRQ_ISR_FORCE_MAINTHREAD; /* if ISR force MT immediat execution, use FORCE_MAINTHREAD instead of STANDARD, and activate FISR permission */

    /*
     * IRQ posthook configuration
     * The posthook is executed at the end of the IRQ handler mode, *before* the ISR.
     * It permit to clean potential status registers (or others) that may generate IRQ loops
     * while the ISR has not been executed.
     * register read can be saved into 'status' and 'data' and given to the ISR in 'sr' and 'dr' argument
     */
    usbotghs_ctx.dev.irqs[0].posthook.status = 0x0014; /* SR is first read */
    usbotghs_ctx.dev.irqs[0].posthook.data = 0x0018; /* Data reg  is 2nd read */


    usbotghs_ctx.dev.irqs[0].posthook.action[0].instr = IRQ_PH_READ;
    usbotghs_ctx.dev.irqs[0].posthook.action[0].read.offset = 0x0014;


    usbotghs_ctx.dev.irqs[0].posthook.action[1].instr = IRQ_PH_READ;
    usbotghs_ctx.dev.irqs[0].posthook.action[1].read.offset = 0x0018;


    usbotghs_ctx.dev.irqs[0].posthook.action[2].instr = IRQ_PH_MASK;
    usbotghs_ctx.dev.irqs[0].posthook.action[2].mask.offset_dest = 0x14; /* MASK register offset */
    usbotghs_ctx.dev.irqs[0].posthook.action[2].mask.offset_src = 0x14; /* MASK register offset */
    usbotghs_ctx.dev.irqs[0].posthook.action[2].mask.offset_mask = 0x18; /* MASK re Here, ACK syncrhonously (or not, in main thread for e.g. is under
                                                                            the responsability of the upper stack implementation, depending
                                                                            on the way it is written. gister offset */
    usbotghs_ctx.dev.irqs[0].posthook.action[2].mask.mode = 0; /* no binary inversion */


    /* mask only for bits that are 'r', other bits of GINTSTS are rc_w1, handle by MASK PH */
    usbotghs_ctx.dev.irqs[0].posthook.action[3].instr = IRQ_PH_AND;
    usbotghs_ctx.dev.irqs[0].posthook.action[3].and.offset_dest = 0x18; /* MASK register offset */
    usbotghs_ctx.dev.irqs[0].posthook.action[3].and.offset_src = 0x14; /* MASK register offset */
    usbotghs_ctx.dev.irqs[0].posthook.action[3].and.mask =
        USBOTG_HS_GINTMSK_OEPINT_Msk   |
        USBOTG_HS_GINTMSK_IEPINT_Msk   |
        USBOTG_HS_GINTMSK_NPTXFEM_Msk  |
        USBOTG_HS_GINTMSK_PTXFEM_Msk   |
        USBOTG_HS_GINTMSK_RXFLVLM_Msk;
    usbotghs_ctx.dev.irqs[0].posthook.action[3].and.mode = 1; /* binary inversion */



    /* Now let's configure the GPIOs */
    usbotghs_ctx.dev.gpio_num = 13;

    /* ULPI_D0 */
    usbotghs_ctx.dev.gpios[0].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;
    usbotghs_ctx.dev.gpios[0].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_D0].port;
    usbotghs_ctx.dev.gpios[0].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_D0].pin; /* 3 */
    usbotghs_ctx.dev.gpios[0].mode         = GPIO_PIN_ALTERNATE_MODE;
    usbotghs_ctx.dev.gpios[0].pupd         = GPIO_NOPULL;
    usbotghs_ctx.dev.gpios[0].type         = GPIO_PIN_OTYPER_PP;
    usbotghs_ctx.dev.gpios[0].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    usbotghs_ctx.dev.gpios[0].afr          = GPIO_AF_OTG_HS;

    /* ULPI_CLK */
    usbotghs_ctx.dev.gpios[1].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;
    usbotghs_ctx.dev.gpios[1].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_CLK].port;
    usbotghs_ctx.dev.gpios[1].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_CLK].pin; /* 3 */
    usbotghs_ctx.dev.gpios[1].mode         = GPIO_PIN_ALTERNATE_MODE;
    usbotghs_ctx.dev.gpios[1].pupd         = GPIO_NOPULL;
    usbotghs_ctx.dev.gpios[1].type         = GPIO_PIN_OTYPER_PP;
    usbotghs_ctx.dev.gpios[1].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    usbotghs_ctx.dev.gpios[1].afr          = GPIO_AF_OTG_HS;

    /*@
      @ loop invariant 0 <= i <= (USB_HS_ULPI_D7+1) ;
      @ loop invariant \valid(usbotghs_ctx.dev.gpios + (0..(USB_HS_ULPI_D7))) ;
      @ loop assigns i, usbotghs_ctx.dev.gpios[0 .. USB_HS_ULPI_D7] ;
      @ loop variant ((USB_HS_ULPI_D7+1) - i) ;
      */

    for (uint8_t i = USB_HS_ULPI_D1; i <= USB_HS_ULPI_D7; ++i) {
        /* INFO: for this loop to work, USBOTG_HS_ULPI_D1 must start at index 2
         * in the JSON file */
        /* ULPI_Di */
        usbotghs_ctx.dev.gpios[i].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;
        usbotghs_ctx.dev.gpios[i].kref.port    = usb_otg_hs_dev_infos.gpios[i].port;
        usbotghs_ctx.dev.gpios[i].kref.pin     = usb_otg_hs_dev_infos.gpios[i].pin;
        usbotghs_ctx.dev.gpios[i].mode         = GPIO_PIN_ALTERNATE_MODE;
        usbotghs_ctx.dev.gpios[i].pupd         = GPIO_NOPULL;
        usbotghs_ctx.dev.gpios[i].type         = GPIO_PIN_OTYPER_PP;
        usbotghs_ctx.dev.gpios[i].speed        = GPIO_PIN_VERY_HIGH_SPEED;
        usbotghs_ctx.dev.gpios[i].afr          = GPIO_AF_OTG_HS;
    }

    /* ULPI_STP */
    usbotghs_ctx.dev.gpios[9].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;
    usbotghs_ctx.dev.gpios[9].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_STP].port;
    usbotghs_ctx.dev.gpios[9].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_STP].pin; /* 3 */
    usbotghs_ctx.dev.gpios[9].mode         = GPIO_PIN_ALTERNATE_MODE;
    usbotghs_ctx.dev.gpios[9].pupd         = GPIO_NOPULL;
    usbotghs_ctx.dev.gpios[9].type         = GPIO_PIN_OTYPER_PP;
    usbotghs_ctx.dev.gpios[9].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    usbotghs_ctx.dev.gpios[9].afr          = GPIO_AF_OTG_HS;

    /* ULPI_DIR */
    usbotghs_ctx.dev.gpios[10].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;
    usbotghs_ctx.dev.gpios[10].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_DIR].port;
    usbotghs_ctx.dev.gpios[10].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_DIR].pin; /* 3 */
    usbotghs_ctx.dev.gpios[10].mode         = GPIO_PIN_ALTERNATE_MODE;
    usbotghs_ctx.dev.gpios[10].pupd         = GPIO_NOPULL;
    usbotghs_ctx.dev.gpios[10].type         = GPIO_PIN_OTYPER_PP;
    usbotghs_ctx.dev.gpios[10].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    usbotghs_ctx.dev.gpios[10].afr          = GPIO_AF_OTG_HS;

    /* ULPI_NXT */
    usbotghs_ctx.dev.gpios[11].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;

    usbotghs_ctx.dev.gpios[11].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_NXT].port;
    usbotghs_ctx.dev.gpios[11].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_NXT].pin; /* 3 */
    usbotghs_ctx.dev.gpios[11].mode         = GPIO_PIN_ALTERNATE_MODE;
    usbotghs_ctx.dev.gpios[11].pupd         = GPIO_NOPULL;
    usbotghs_ctx.dev.gpios[11].type         = GPIO_PIN_OTYPER_PP;
    usbotghs_ctx.dev.gpios[11].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    usbotghs_ctx.dev.gpios[11].afr          = GPIO_AF_OTG_HS;

    /* Reset */
    usbotghs_ctx.dev.gpios[12].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;

    usbotghs_ctx.dev.gpios[12].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_RESET].port;
    usbotghs_ctx.dev.gpios[12].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_RESET].pin; /* 3 */
    usbotghs_ctx.dev.gpios[12].mode         = GPIO_PIN_OUTPUT_MODE;
    usbotghs_ctx.dev.gpios[12].pupd         = GPIO_PULLUP;//GPIO_PULLDOWN;
    usbotghs_ctx.dev.gpios[12].type         = GPIO_PIN_OTYPER_PP;
    usbotghs_ctx.dev.gpios[12].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    usbotghs_ctx.dev.gpios[12].afr          = GPIO_AF_OTG_HS;

    if ((ret == sys_init(INIT_DEVACCESS, (device_t*)&(usbotghs_ctx.dev), (int*)&(usbotghs_ctx.dev_desc))) != SYS_E_DONE) {
        return MBED_ERROR_UNKNOWN;
    }
    return MBED_ERROR_NONE;
}


/*
 * This function initialize the USB OTG HS Core.
 *
 * The driver must meet the following conditions to set up the device core to handle traffic:
 *
 *  -  In Slave mode, GINTMSK.NPTxFEmpMsk, and GINTMSK.RxFLvlMsk must be unset.
 *  -  In DMA mode, the GINTMSK.NPTxFEmpMsk, and GINTMSK.RxFLvlMsk interrupts must be masked.
 *
 * The driver must perform the following steps to initialize the core at device on, power on, or after a
 * mode change from Host to Device.
 *
 * 1. Program the following fields in DCFG register.
 *  -  DescDMA bit (applicable only if OTG_EN_DESC_DMA parameter is set to high)
 *  -  Device Speed
 *  -  NonZero Length Status OUT Handshake
 *  - Periodic Frame Interval (If Periodic Endpoints are supported)
 *
 * 2. Program the Device threshold control register.
 *    This is required only if you are using DMA mode and you are planning to enable thresholding.
 *
 * 3. Clear the DCTL.SftDiscon bit. The core issues a connect after this bit is cleared.
 *
 * 4. Program the GINTMSK register to unmask the following interrupts.
 * -  USB Reset
 * -  Enumeration Done
 * -  Early Suspend
 * -  USB Suspend
 * -  SOF
 *
 * 5. Wait for the GINTSTS.USBReset interrupt, which indicates a reset has been detected on the USB and
 *    lasts for about 10 ms. On receiving this interrupt, the application must perform the steps listed in
 *    "Initialization on USB Reset" on page 157.
 *
 * 6. Wait for the GINTSTS.EnumerationDone interrupt. This interrupt indicates the end of reset on the
 * USB. On receiving this interrupt, the application must read the DSTS register to determine the
 * enumeration speed and perform the steps listed in “Initialization on Enumeration Completion” on
 * page 158.
 *
 * At this point, the device is ready to accept SOF packets and perform control transfers on control endpoint 0.
 */

/*@
  @ requires \separated(GHOST_in_eps+(0 .. USBOTGHS_MAX_IN_EP-1), GHOST_out_eps+(0 .. USBOTGHS_MAX_OUT_EP-1),&GHOST_nopublicvar, ((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), &usbotghs_ctx);
  @ assigns usbotghs_ctx \from indirect:mode;
  @ assigns usbotghs_ctx,  *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END));
  */
mbed_error_t usbotghs_configure(usbotghs_dev_mode_t mode,
        usbotghs_ioep_handler_t ieph,
        usbotghs_ioep_handler_t oeph)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    /* First, reset the PHY device connected to the core through ULPI interface */
    log_printf("[USB HS] Mapping device\n");
    /*sanitize */
    if (mode != USBOTGHS_MODE_DEVICE && mode != USBOTGHS_MODE_HOST) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* INFO: the driver does not requires ieph & oeph to be valid (i.e. != NULL), as the upper handler call is
     * for EP0 is under the responsability of the upper stack. */

    if (sys_cfg(CFG_DEV_MAP, usbotghs_ctx.dev_desc)) {
        log_printf("[USB HS] Unable to map USB device !!!\n");
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }
    if ((errcode = usbotghs_ulpi_reset()) != MBED_ERROR_NONE) {
        goto err;
    }
    usbotghs_ctx.mode = mode;
    /* first, we need to initialize the core */
    log_printf("[USB HS] initialize the Core\n");
    if ((errcode = usbotghs_initialize_core(mode)) != MBED_ERROR_NONE) {
        goto err;
    }
    /* host/device mode */
    switch (mode) {
        case USBOTGHS_MODE_HOST: {
                                     log_printf("[USB HS][HOST] initialize in Host mode\n");
                                     if ((errcode = usbotghs_initialize_host()) != MBED_ERROR_NONE) {
                                         goto err;
                                     }
                                     /* IT Indicates that Periodic TxFIFO is half empty */
                                     break;
                                 }
        case USBOTGHS_MODE_DEVICE: {
                                       log_printf("[USB HS][DEVICE] initialize in Device mode\n");
                                       if ((errcode = usbotghs_initialize_device()) != MBED_ERROR_NONE) {
                                           goto err;
                                       }
                                       break;
                                   }
        default:
                                   errcode = MBED_ERROR_INVPARAM;
                                   goto err;
                                   break;
    }

    usbotghs_ctx.fifo_idx = 0;
    /* initialize EP0, which is both IN & OUT EP */
    usbotghs_ctx.in_eps[0].id = 0;
    usbotghs_ctx.in_eps[0].configured = true; /* wait for reset, but EP0 ctrl is ready to recv
XXX: shouldn't it be false, without FIFO as RXFLVL should not be received before
reset ? */
    usbotghs_ctx.in_eps[0].mpsize = USBOTG_HS_EPx_MPSIZE_64BYTES;
    usbotghs_ctx.in_eps[0].type = USBOTG_HS_EP_TYPE_CONTROL;
    usbotghs_ctx.in_eps[0].state = USBOTG_HS_EP_STATE_IDLE;
    //@ ghost GHOST_in_eps[0].state = usbotghs_ctx.in_eps[0].state;
    //@ assert GHOST_in_eps[0].state == usbotghs_ctx.in_eps[0].state;
    usbotghs_ctx.in_eps[0].handler = ieph;
    usbotghs_ctx.in_eps[0].fifo = NULL; /* not yet configured */
    usbotghs_ctx.in_eps[0].fifo_idx = 0; /* not yet configured */
    usbotghs_ctx.in_eps[0].fifo_size = 0; /* not yet configured */
    usbotghs_ctx.in_eps[0].fifo_lck = false;
    usbotghs_ctx.in_eps[0].dir = USBOTG_HS_EP_DIR_IN;
    if (mode == USBOTGHS_MODE_DEVICE) {
        usbotghs_ctx.in_eps[0].core_txfifo_empty = true;
    }

    usbotghs_ctx.out_eps[0].id = 0;
    usbotghs_ctx.out_eps[0].configured = true; /* wait for reset */
    usbotghs_ctx.out_eps[0].mpsize = USBOTG_HS_EPx_MPSIZE_64BYTES;
    usbotghs_ctx.out_eps[0].type = USBOTG_HS_EP_TYPE_CONTROL;
    usbotghs_ctx.out_eps[0].state = USBOTG_HS_EP_STATE_IDLE;
    //@ ghost GHOST_out_eps[0].state = usbotghs_ctx.out_eps[0].state;
    //@ assert GHOST_out_eps[0].state == usbotghs_ctx.out_eps[0].state;
    usbotghs_ctx.out_eps[0].handler = oeph;
    usbotghs_ctx.out_eps[0].dir = USBOTG_HS_EP_DIR_OUT;
    usbotghs_ctx.out_eps[0].fifo = 0; /* not yet configured */
    usbotghs_ctx.out_eps[0].fifo_idx = 0; /* not yet configured */
    usbotghs_ctx.out_eps[0].fifo_size = 0; /* not yet configured */
    usbotghs_ctx.in_eps[0].fifo_lck = false;

    usbotghs_ctx.speed = USBOTG_HS_SPEED_HS; /* default. In device mode, wait for enumeration */

err:
    return errcode;
}

/*
 * Returns, for the current IP, the max data endpoint (not control) packet size
 * supported
 */

/*@
  @ assigns \nothing;
  @ ensures \result == MAX_EPx_PKT_SIZE ;
  */

uint16_t usbotghs_get_ep_mpsize(void)
{
    return MAX_EPx_PKT_SIZE;
}



/*
 * Sending data put content in the USB OTG FIFO and ask the EP to read from it to
 * send the data on the line (by activating the EP (field USBAEP of out EPs))
 * We must wait data sent IT to be sure that content is effectively transmitted
 */


/*
TODO : add specification for !CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
*/

/*@
 @ requires \separated(GHOST_in_eps+(0 .. USBOTGHS_MAX_IN_EP - 1),&GHOST_nopublicvar, src,&usbotghs_ctx, (uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END));

 @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.in_eps[ep_id], *(usbotghs_ctx.in_eps[ep_id].fifo+(usbotghs_ctx.in_eps[ep_id].fifo_idx..(usbotghs_ctx.in_eps[ep_id].fifo_idx + (512 - 1))));
 @ assigns usbotghs_ctx.in_eps[ep_id].state,  *((uint32_t *)((int)(0x40040000 + (int)(0x1000 * (int)((int)usbotghs_ctx.in_eps[usbotghs_ctx.in_eps[ep_id].id].id + 1))))), *((uint32_t *)((0x40040000 + 0x910) + (int)(usbotghs_ctx.in_eps[ep_id].id * 0x20))), usbotghs_ctx.in_eps[usbotghs_ctx.in_eps[ep_id].id].fifo_idx, usbotghs_ctx.in_eps[usbotghs_ctx.in_eps[ep_id].id].fifo_lck, usbotghs_ctx.in_eps[usbotghs_ctx.in_eps[ep_id].id].fifo[\at(usbotghs_ctx.in_eps[usbotghs_ctx.in_eps[ep_id].id].fifo_idx,Pre)];

    @  @   assigns  usbotghs_ctx.in_eps[ep_id].fifo,usbotghs_ctx.in_eps[ep_id].fifo_lck,usbotghs_ctx.in_eps[ep_id].fifo_idx, usbotghs_ctx.in_eps[ep_id].fifo_size, *((uint32_t *)((0x40040000 + 0x910) + (int)ep_id * 0x20)), *((uint32_t *)((0x40040000 + 0x900) + (int)ep_id * 0x20)) , usbotghs_ctx.in_eps[ep_id].state;


 // private function contract
 @ ensures ((ep_id < USBOTGHS_MAX_IN_EP) && src != NULL && size > 0 && ((usbotghs_ctx.in_eps[ep_id].configured != \true) || (usbotghs_ctx.in_eps[ep_id].mpsize == 0))) ==> \result == MBED_ERROR_INVSTATE ;

 @ ensures ( (ep_id < USBOTGHS_MAX_IN_EP) && src != NULL && size > 0 && ((usbotghs_ctx.in_eps[ep_id].configured == \true) && (usbotghs_ctx.in_eps[ep_id].mpsize > 0)) && usbotghs_ctx.in_eps[ep_id].fifo_lck == \true) ==> \result == MBED_ERROR_INVSTATE  ;

 @ ensures ((ep_id < USBOTGHS_MAX_IN_EP) && src != NULL && size > 0 && ((usbotghs_ctx.in_eps[ep_id].configured == \true) && (usbotghs_ctx.in_eps[ep_id].mpsize > 0)) && usbotghs_ctx.in_eps[ep_id].fifo_lck != \true) ==> \result == MBED_ERROR_INVPARAM || \result == MBED_ERROR_BUSY || \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE ;

 */
mbed_error_t usbotghs_send_data(uint8_t *src, uint32_t size, uint8_t ep_id)
{
    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    uint32_t packet_count = 0;
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint32_t fifo_size = 0;
    usbotghs_context_t *ctx = usbotghs_get_context();

    usbotghs_ep_t *ep = NULL;

#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE

    if(ep_id >= USBOTGHS_MAX_IN_EP)
    {
        errcode = MBED_ERROR_INVPARAM;
        goto err_init;
    }
    /*@ assert ep_id <USBOTGHS_MAX_IN_EP; */
    ep = &ctx->in_eps[ep_id];
    /* @ assert ep == &usbotghs_ctx.in_eps[ep_id] ; */
#else

    if(ep_id >= USBOTGHS_MAX_OUT_EP)
    {
        errcode = MBED_ERROR_INVPARAM;
        goto err_init
    }
     /*@ assert ep_id <UYBOTGHS_MAX_OUT_EP; */
    ep = &ctx->out_eps[ep_id];
    /* @ assert ep == &usbotghs_ctx.out_eps[ep_id] ; */
#endif


    if (src == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /*@ assert src !=\null;*/
    if (size == 0) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /*@ assert size !=0;*/
    if (ep->configured != true || ep->mpsize == 0) {
        log_printf("[USBOTG][HS] ep %d not configured\n", ep->id);
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /*@ assert ep->configured == true && ep->mpsize >0 ;*/
    fifo_size = USBOTG_HS_TX_CORE_FIFO_SZ;

    /* configure EP FIFO internal informations */

    if ((errcode = usbotghs_set_xmit_fifo(src, size, ep_id)) != MBED_ERROR_NONE) {
      log_printf("[USBOTG][HS] failed to set EP%d TxFIFO!\n", ep_id);
      /*@ assert  errcode== MBED_ERROR_INVSTATE && \at(usbotghs_ctx.in_eps,Pre)[ep_id].fifo_lck == \true; */
      goto err_init;
    }

    /* giving these three assertions, next call to usbotghs_write_epx_fifo() should has its
     * preconditions granted. */
    /* Here are the precodntions of a **valid** set_xmit_fifo() execution: */
    /*@ assert \at(usbotghs_ctx.in_eps,Pre)[ep_id].fifo_lck == \false; */
    /* Here are the postconditions of a **valid** set_xmit_fifo() execution: */
    /*@ assert \valid(ep->fifo+(0..ep->fifo_size-1));*/
    /*@ assert ep->fifo_lck == \false && ep->fifo == src && ep->fifo_idx==0 && ep->fifo_size==size; */
    /*@ assert ep->mpsize <= fifo_size; */


    /*
     * Here, we have to split the src content, taking into account the
     * current EP mpsize, and schedule transmission into the Core TxFIFO.
     */

    /* XXX: Here we assume fifo size == mpsize, which is bad..., fifo is bigger */
    uint32_t residual_size = size;

    /*
     * We can configure the core to handle the transmission of upto:
     * - 1024 packets (independently of their size)
     * - 1048575 bytes (2^19 - 1, independently of the number of packets)
     *
     * We consider here, that there is not request bigger than the max packet
     * size in bytes (i.e. ~1Mbytes), and no request bigger than 1024 packets
     * (in "data" EP such as mass storage where MPSize is 512, we can transmit
     * upto 512*1024 = 512KBytes per transfer, which is huge).
     */

    /*
     * First we configure the number of packets to transfer and the number of
     * bytes to transfer
     */
    packet_count = (size / ep->mpsize) + ((size % ep->mpsize) ? 1: 0);

    log_printf("[USBOTG][HS] need to write %d pkt on ep %d, init_size: %d\n", packet_count, ep_id, size);
#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
    /* 1. Program the OTG_HS_DIEPTSIZx register for the transfer size
     * and the corresponding packet count. */
    /* EP 0 is not able to handle more than one packet of mpsize size per transfer. For bigger
     * transfers, the driver must fragment data transfer transparently */


    if (ep_id > 0 || size <= ep->mpsize) {
        set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id), packet_count, USBOTG_HS_DIEPTSIZ_PKTCNT_Msk(ep_id), USBOTG_HS_DIEPTSIZ_PKTCNT_Pos(ep_id));
        set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),size,USBOTG_HS_DIEPTSIZ_XFRSIZ_Msk(ep_id),USBOTG_HS_DIEPTSIZ_XFRSIZ_Pos(ep_id));
    } else {
        log_printf("[USBOTG][HS] need to write more data than the EP is able in a single transfer\n");
        set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),1,USBOTG_HS_DIEPTSIZ_PKTCNT_Msk(ep_id),USBOTG_HS_DIEPTSIZ_PKTCNT_Pos(ep_id));
        set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),ep->mpsize,USBOTG_HS_DIEPTSIZ_XFRSIZ_Msk(ep_id), USBOTG_HS_DIEPTSIZ_XFRSIZ_Pos(ep_id));
    }
    set_u8_with_membarrier(&ep->state, USBOTG_HS_EP_STATE_DATA_IN_WIP);
    //@ ghost GHOST_in_eps[ep_id].state = usbotghs_ctx.in_eps[ep_id].state;

    /* 2. Enable endpoint for transmission. */
    set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id),USBOTG_HS_DIEPCTL_CNAK_Msk | USBOTG_HS_DIEPCTL_EPENA_Msk);

#else
    /* EP 0 is not able to handle more than one packet of mpsize size per transfer. For bigger
     * transfers, the driver must fragment data transfer transparently */
    if (ep_id > 0 || size <= ep->mpsize) {
        /* 1. Program the OTG_HS_DOEPTSIZx register for the transfer size
         * and the corresponding packet count. */
        set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(ep_id),packet_count,USBOTG_HS_DOEPTSIZ_PKTCNT_Msk(ep_id),USBOTG_HS_DOEPTSIZ_PKTCNT_Pos(ep_id));
        set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(ep_id),size,USBOTG_HS_DOEPTSIZ_XFRSIZ_Msk(ep_id),USBOTG_HS_DOEPTSIZ_XFRSIZ_Pos(ep_id));
    } else {
        set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(ep_id),1,USBOTG_HS_DOEPTSIZ_PKTCNT_Msk(ep_id),USBOTG_HS_DOEPTSIZ_PKTCNT_Pos(ep_id));
        set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(ep_id),ep->mpsize,USBOTG_HS_DOEPTSIZ_XFRSIZ_Msk(ep_id),USBOTG_HS_DOEPTSIZ_XFRSIZ_Pos(ep_id));
    }
    set_u8_with_membarrier(&ep->state, USBOTG_HS_EP_STATE_DATA_OUT_WIP);
    //@ ghost GHOST_out_eps[ep_id].state = usbotghs_ctx.out_eps[ep_id].state;
#endif

    /* Fragmentation on EP0 case: we don't loop on the input FIFO to
     * synchronously transmit the data, we just write the first packet
     * into the FIFO, and we wait for IEPINT. The successive next
     * contents will be transmitted by iepint by detecting that
     * ep->fifo_idx is smaller than ep->fifo_size (data transmission
     * not finished) */

    if (ep_id == 0 && size > ep->mpsize) {
        log_printf("[USBOTG][HS] fragment: initiate the first fragment to send (MPSize) on EP0\n");
        /* wait for enough space in TxFIFO */

#ifndef __FRAMAC__
        /* we can't rely on contrôled timeout for xFIFU flush, as the flush time depend on multiple HW constraints which are hard to dimension.
         * In nominal case, we wait for the TxFIFO to be flushed, except in case of busy error. In FramaC case, we must provide a loop terminaison. */
        while (get_reg(r_CORTEX_M_USBOTG_HS_DTXFSTS(ep_id), USBOTG_HS_DTXFSTS_INEPTFSAV) < (ep->mpsize / 4)) {
            if (get_reg(r_CORTEX_M_USBOTG_HS_DSTS, USBOTG_HS_DSTS_SUSPSTS)){
                log_printf("[USBOTG][HS] Suspended!\n");
                errcode = MBED_ERROR_BUSY;
                goto err;
            }
        }
#else
        /*@
          @ loop invariant 0<=cpt<= CPT_HARD;
          @ loop assigns cpt;
          @ loop variant CPT_HARD - cpt ;
          */
        for (uint8_t cpt=0; cpt<CPT_HARD; cpt++)
        {
            if (get_reg(r_CORTEX_M_USBOTG_HS_DTXFSTS(ep_id), USBOTG_HS_DTXFSTS_INEPTFSAV) < (ep->mpsize / 4)) {
                if (get_reg(r_CORTEX_M_USBOTG_HS_DSTS, USBOTG_HS_DSTS_SUSPSTS)){
                    log_printf("[USBOTG][HS] Suspended!\n");
                    errcode = MBED_ERROR_BUSY;
                    goto err;
                }
            }
        }
#endif

#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
        set_u8_with_membarrier(&ep->state, USBOTG_HS_EP_STATE_DATA_IN);
    //@ ghost GHOST_in_eps[ep_id].state = usbotghs_ctx.in_eps[ep_id].state;
#else
        set_u8_with_membarrier(&ep->state, USBOTG_HS_EP_STATE_DATA_OUT);
    //@ ghost GHOST_out_eps[ep_id].state = usbotghs_ctx.out_eps[ep_id].state;
#endif
        /* write data from SRC to FIFO */
        errcode = usbotghs_write_epx_fifo(ep->mpsize, ep->id);
        goto err;
    }

    /*
     * Case of packets WITHOUT fragmentation
     * Now, we need to loop on the FIFO write and transmit, while there is
     * data to send. The Core FIFO will handle the decrement of XFRSIZ and
     * PKTCNT automatically, and will rise the XFRC interrupt when both reach
     * 0.
     */
    /*
     * First, we push FIFO size multiple into the FIFO
     */
#ifdef __FRAMAC__
    uint8_t cpt = 0;
#endif
    //
    /* this loop doesn't have loop invariant for loop counters as there is no sequencial decrement upto 0 with a step of 1 */
    /*@
      @ loop invariant \valid(ep->fifo+(0..ep->fifo_size));
      @ loop invariant fifo_size >0 ;
      @ loop assigns  errcode, cpt,usbotghs_ctx.in_eps[ep_id].state, residual_size, *((uint32_t *)((int)(0x40040000 + (int)(0x1000 * (int)((int)usbotghs_ctx.in_eps[usbotghs_ctx.in_eps[ep_id].id].id + 1))))), *((uint32_t *)((0x40040000 + 0x910) + (int)(usbotghs_ctx.in_eps[ep_id].id * 0x20))), usbotghs_ctx.in_eps[usbotghs_ctx.in_eps[ep_id].id].fifo_idx, usbotghs_ctx.in_eps[usbotghs_ctx.in_eps[ep_id].id].fifo_lck, usbotghs_ctx.in_eps[usbotghs_ctx.in_eps[ep_id].id].fifo[\at(usbotghs_ctx.in_eps[usbotghs_ctx.in_eps[ep_id].id].fifo_idx,LoopEntry)];
      @ loop variant residual_size ;
      */
    while (residual_size >= fifo_size) {
      /*@ assert residual_size >= fifo_size; */
#ifndef __FRAMAC__
        while (get_reg(r_CORTEX_M_USBOTG_HS_DTXFSTS(ep_id), USBOTG_HS_DTXFSTS_INEPTFSAV) < (fifo_size / 4)) {
            if (get_reg(r_CORTEX_M_USBOTG_HS_DSTS, USBOTG_HS_DSTS_SUSPSTS)){
                log_printf("[USBOTG][HS] Suspended!\n");
                errcode = MBED_ERROR_BUSY;
                goto err;
            }
        }
#else

        /*@
          @ loop invariant \valid(ep->fifo+(0..ep->fifo_size));
          @ loop invariant 0<=cpt<= CPT_HARD ;
          @ loop assigns cpt ;
          @ loop variant CPT_HARD - cpt ;
          */
        for(cpt=0; cpt<CPT_HARD; cpt++)
        {
            if (get_reg(r_CORTEX_M_USBOTG_HS_DTXFSTS(ep_id), USBOTG_HS_DTXFSTS_INEPTFSAV) < (fifo_size / 4)) {
                if (get_reg(r_CORTEX_M_USBOTG_HS_DSTS, USBOTG_HS_DSTS_SUSPSTS)){
                    log_printf("[USBOTG][HS] Suspended!\n");
                    errcode = MBED_ERROR_BUSY;
                    goto err;
                }
            }
        }
#endif

        if (residual_size == fifo_size) {
            /* last block, no more WIP */
#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
            set_u8_with_membarrier(&ep->state, USBOTG_HS_EP_STATE_DATA_IN);
            //@ ghost GHOST_in_eps[ep_id].state = usbotghs_ctx.in_eps[ep_id].state;
#else
            set_u8_with_membarrier(&ep->state, USBOTG_HS_EP_STATE_DATA_OUT);
            //@ ghost GHOST_out_eps[ep_id].state = usbotghs_ctx.out_eps[ep_id].state;
#endif
        }

        /* @ assert \separated(&usbotghs_ctx,r_CORTEX_M_USBOTG_HS_DTXFSTS(ep_id),r_CORTEX_M_USBOTG_HS_GINTMSK, USBOTG_HS_DEVICE_FIFO(usbotghs_ctx.in_eps[ep_id].id), &num_ctx, &ctx_list+(..))  ; */
        /* write data from SRC to FIFO */
        usbotghs_write_epx_fifo(fifo_size, ep->id);


        /* wait for XMIT data to be transfered (wait for iepint (or oepint in
         * host mode) to set the EP in correct state */

        //usbotghs_wait_for_xmit_complete(ep);
        residual_size -= fifo_size;
	/*@ assert residual_size >= 0; */
	/*@ assert residual_size == \at(residual_size,LoopCurrent) - fifo_size ;*/
        log_printf("[USBOTG][HS] EP: %d: residual: %d\n", ep_id, residual_size);
    }
    /* Now, if there is residual size shorter than FIFO size, just send it */
    if (residual_size > 0) {
        /* wait while there is enough space in TxFIFO */
#ifndef __FRAMAC__
        while (get_reg(r_CORTEX_M_USBOTG_HS_DTXFSTS(ep_id), USBOTG_HS_DTXFSTS_INEPTFSAV)  < ((residual_size / 4) + (residual_size & 3 ? 1 : 0))) {
#else

            /*@
              @ loop invariant \valid(ep->fifo+(0..ep->fifo_size));
              @ loop invariant 0<=cpt<= CPT_HARD ;
              @ loop assigns cpt ;
              @ loop variant CPT_HARD - cpt;
              */

        for(cpt=0; cpt<CPT_HARD; cpt++){
            if (get_reg(r_CORTEX_M_USBOTG_HS_DTXFSTS(ep_id), USBOTG_HS_DTXFSTS_INEPTFSAV)  < ((residual_size / 4) + (residual_size & 3 ? 1 : 0))) {
#endif
               if (get_reg(r_CORTEX_M_USBOTG_HS_DSTS, USBOTG_HS_DSTS_SUSPSTS)){
                    log_printf("[USBOTG][HS] Suspended!\n");
                    errcode = MBED_ERROR_BUSY;
                    goto err;
                }
#ifdef __FRAMAC__
            }
#endif
        }
        /* last block, no more WIP */
#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
        set_u8_with_membarrier(&ep->state, USBOTG_HS_EP_STATE_DATA_IN);
            //@ ghost GHOST_in_eps[ep_id].state = usbotghs_ctx.in_eps[ep_id].state;
#else
        set_u8_with_membarrier(&ep->state, USBOTG_HS_EP_STATE_DATA_OUT);
            //@ ghost GHOST_out_eps[ep_id].state = usbotghs_ctx.out_eps[ep_id].state;
#endif
        /* set the EP state to DATA OUT WIP (not yet transmitted) */
        log_printf("[USBOTGHS] write %d len data on ep %d core fifo\n", residual_size, ep->id);
        /*@ assert residual_size <= fifo_size; */
        usbotghs_write_epx_fifo(residual_size, ep->id);
        /* wait for XMIT data to be transfered (wait for iepint (or oepint in
         * host mode) to set the EP in correct state */
        residual_size = 0;
    }

    if(get_reg(r_CORTEX_M_USBOTG_HS_DSTS, USBOTG_HS_DSTS_SUSPSTS)) {
        errcode = MBED_ERROR_BUSY;
        goto err;
    }
    return errcode;
err:
    /* From whatever we come from to this point, the current transfer is complete
     * (with failure or not on upper level). IEPINT can inform the upper layer */
    set_u8_with_membarrier(&ep->state, USBOTG_HS_EP_STATE_IDLE);
#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
    //@ ghost GHOST_in_eps[ep_id].state = usbotghs_ctx.in_eps[ep_id].state;
#else
    //@ ghost GHOST_out_eps[ep_id].state = usbotghs_ctx.out_eps[ep_id].state;
#endif
err_init:
    return errcode;
}


/*
 * Send a Zero-length packet into EP 'ep'
 */

/*@
  @ requires \separated(&GHOST_nopublicvar, ((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), &usbotghs_ctx);
   @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;


   // private, more precise, behaviors
   @ ensures (CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE && ep_id < USBOTGHS_MAX_IN_EP && usbotghs_ctx.in_eps[ep_id].configured == \false)
   <==> \result == MBED_ERROR_INVSTATE ;
   @ ensures (!CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE && ep_id < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep_id].configured == \false)
   ==> \result == MBED_ERROR_INVSTATE ;
   @ ensures (CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE && ep_id < USBOTGHS_MAX_IN_EP && usbotghs_ctx.in_eps[ep_id].configured == \true)
   <==> \result == MBED_ERROR_BUSY || \result == MBED_ERROR_NONE ;
   @ ensures (!CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE && ep_id < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep_id].configured == \true)
   ==> \result == MBED_ERROR_BUSY || \result == MBED_ERROR_NONE ;
 */
mbed_error_t usbotghs_send_zlp(uint8_t ep_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    usbotghs_ep_t *ep = NULL;

    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
    if (ep_id >= USBOTGHS_MAX_IN_EP) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    ep = &ctx->in_eps[ep_id];
#else
    if (ep_id >= USBOTGHS_MAX_OUT_EP) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    ep = &ctx->out_eps[ep_id];
#endif
    if (!ep->configured) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }

    /*
     * Be sure that previous transmission is finished before configuring another one
     */

    /*@
      @ loop invariant \valid(r_CORTEX_M_USBOTG_HS_DTXFSTS(ep_id));
      @ loop invariant 0<=cpt<= CPT_HARD ;
      @ loop assigns cpt ;
      @ loop variant CPT_HARD - cpt ;
      */

    for(uint8_t cpt=0; cpt<CPT_HARD; cpt++){
        if (get_reg(r_CORTEX_M_USBOTG_HS_DTXFSTS(ep_id), USBOTG_HS_DTXFSTS_INEPTFSAV) <
                USBOTG_HS_TX_CORE_FIFO_SZ / 4) {
            // Are we suspended?
            if (get_reg(r_CORTEX_M_USBOTG_HS_DSTS, USBOTG_HS_DSTS_SUSPSTS)){
                log_printf("[USBOTG][HS] Suspended!\n");
                errcode = MBED_ERROR_BUSY;
                goto err;
            }
        }
    }

    log_printf("[USBOTG][HS] Sending ZLP on ep %d\n", ep_id);
    /* device mode ONLY */
    /* EP is now in DATA_OUT state */
    // XXX: needed for ZLP ? ep->state = USBOTG_HS_EP_STATE_DATA_OUT;
    /* 1. Program the OTG_HS_DIEPTSIZx register for the transfer size
     * and the corresponding packet count. */
    set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),1,USBOTG_HS_DIEPTSIZ_PKTCNT_Msk(ep_id),USBOTG_HS_DIEPTSIZ_PKTCNT_Pos(ep_id));
    set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),0,USBOTG_HS_DIEPTSIZ_XFRSIZ_Msk(ep_id),USBOTG_HS_DIEPTSIZ_XFRSIZ_Pos(ep_id));
    /* 2. Enable endpoint for transmission. */
    set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id),USBOTG_HS_DIEPCTL_CNAK_Msk | USBOTG_HS_DIEPCTL_EPENA_Msk);

err:
    return errcode;
}
/*
 * Set the STALL mode for the device. Per-EP STALL mode can still override
 */
mbed_error_t usbotghs_global_stall(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    return errcode;
}

/*@
  @ requires \separated(&GHOST_nopublicvar,((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
  */
mbed_error_t usbotghs_endpoint_set_nak(uint8_t ep_id, usbotghs_ep_dir_t dir)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    uint32_t count = 0;

    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    /*
     * FIXME: For IN endpoint, implicit fallthrough to IN+OUT NAK
     * It seems that in the other case, the USB Core stalls.
     * This behavior may be the consequence of an invalid use of _nak/_ack calls in the
     * upper stacks. For EP0, though, these two functions must **not** fallthrough and
     * behave properly, as EP0 is a FULL DUPLEX endpoint. A fallthrough would generate
     * a border effect on the other direction.
     */
    switch (dir) {
        case USBOTG_HS_EP_DIR_IN:
            if (ep_id >= USBOTGHS_MAX_IN_EP) {
                errcode = MBED_ERROR_INVPARAM;
                goto err;
            }
            if (ctx->in_eps[ep_id].configured == false) {
                errcode = MBED_ERROR_INVSTATE;
                goto err;
            }
            /* wait for end of current transmission */
            /*@
              @ loop invariant 0<=cpt<= CPT_HARD ;
              @ loop assigns  cpt, count ;
              @ loop variant CPT_HARD - cpt ;
              */

            for(uint8_t cpt=0; cpt<CPT_HARD; cpt++){
                if (get_reg_value(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id), USBOTG_HS_DIEPCTL_EPENA_Msk, USBOTG_HS_DIEPCTL_EPENA_Pos))  {
                    if (++count > USBOTGHS_REG_CHECK_TIMEOUT){
                        log_printf("[USBOTG][HS] HANG! DIEPCTL:EPENA\n");
                        errcode = MBED_ERROR_BUSY;
                        goto err;
                    }
                }
            }

            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id), USBOTG_HS_DIEPCTL_SNAK_Msk);
            if (ep_id == 0) {
                break;
            }
            __explicit_fallthrough
        case USBOTG_HS_EP_DIR_OUT:
                if (ep_id >= USBOTGHS_MAX_OUT_EP) {
                    errcode = MBED_ERROR_INVPARAM;
                    goto err;
                }
                if (ctx->out_eps[ep_id].configured == false) {
                    errcode = MBED_ERROR_INVSTATE;
                    goto err;
                }
                /* wait for end of current transmission */
                /*@
                  @ loop invariant 0<=cpt<= CPT_HARD ;
                  @ loop assigns cpt;
                  @ loop variant CPT_HARD - cpt ;
                  */

                for(uint8_t cpt=0; cpt<CPT_HARD; cpt++){
                    if (get_reg_value(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_EPENA_Msk, USBOTG_HS_DOEPCTL_EPENA_Pos))  {
                        if (cpt > USBOTGHS_REG_CHECK_TIMEOUT) {
                            log_printf("[USBOTG][HS] HANG! DOEPCTL:EPENA\n");
                            errcode = MBED_ERROR_BUSY;
                            goto err;
                        }
                    }
                }

                set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DIEPCTL_SNAK_Msk);
                break;
        default:
                errcode = MBED_ERROR_INVPARAM;
                goto err;
    }
err:
    return errcode;
}

/*@
  @ // specification private part: local globals constraints (usbotghs is a library)
  @   requires \separated(&GHOST_nopublicvar, &usbotghs_ctx,((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ) ;
  @   assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;


  // test: private function contract (fonctional)
  @ ensures (dir == USBOTG_HS_EP_DIR_IN && ep_id < USBOTGHS_MAX_IN_EP && usbotghs_ctx.in_eps[ep_id].configured == \true) ==> \result == MBED_ERROR_NONE;
  @ ensures (dir == USBOTG_HS_EP_DIR_IN && ep_id < USBOTGHS_MAX_IN_EP && usbotghs_ctx.in_eps[ep_id].configured == \false) ==> \result == MBED_ERROR_INVSTATE;

  @ ensures (dir == USBOTG_HS_EP_DIR_OUT && ep_id < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep_id].configured == \true) ==> \result == MBED_ERROR_NONE;
  @ ensures (dir == USBOTG_HS_EP_DIR_OUT && ep_id < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep_id].configured == \false) ==> \result == MBED_ERROR_INVSTATE;

  */
mbed_error_t usbotghs_endpoint_clear_nak(uint8_t ep_id, usbotghs_ep_dir_t dir)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;


    usbotghs_context_t *ctx = usbotghs_get_context();

    /*
     * FIXME: For IN endpoint, implicit fallthrough to IN+OUT ACK
     * It seems that in the other case, the USB Core stalls.
     * This behavior may be the consequence of an invalid use of _nak/_ack calls in the
     * upper stacks. For EP0, though, these two functions must **not** fallthrough and
     * behave properly, as EP0 is a FULL DUPLEX endpoint. A fallthrough would generate
     * a border effect on the other direction.
     */
    switch (dir) {
        case USBOTG_HS_EP_DIR_IN:
            log_printf("[USBOTG][HS] CNAK on IN ep %d\n", ep_id);
            if (ep_id >= USBOTGHS_MAX_IN_EP) {
                log_printf("[USBOTG][HS] invalid IN EP %d\n", ep_id);
                errcode = MBED_ERROR_INVPARAM;
                goto err;
            }
            if (ctx->in_eps[ep_id].configured == false) {
                log_printf("[USBOTG][HS] invalid IN EP %d: not configured\n", ep_id);
                errcode = MBED_ERROR_INVSTATE;
                goto err;
            }
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id), USBOTG_HS_DIEPCTL_CNAK_Msk);
            if (ep_id == 0) {
                break;
            }
            /* FIXME: this seems to be a functional bug in upper layer(s): clear nak on invalid direction */
            /* TODO: to be investigate in order to set break here */
            __explicit_fallthrough
        case USBOTG_HS_EP_DIR_OUT:
                log_printf("[USBOTG][HS] CNAK on OUT ep %d\n", ep_id);
                if (ep_id >= USBOTGHS_MAX_OUT_EP) {
                    log_printf("[USBOTG][HS] invalid OUT EP %d\n", ep_id);
                    errcode = MBED_ERROR_INVPARAM;
                    goto err;
                }
                if (ctx->out_eps[ep_id].configured == false) {
                    log_printf("[USBOTG][HS] invalid OUT EP %d: not configured\n", ep_id);
                    errcode = MBED_ERROR_INVSTATE;
                    goto err;
                }
                set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_CNAK_Msk);
                break;
        default:
                log_printf("[USBOTG][HS] CNAK: invalid direction for ep %d\n", ep_id);
                errcode = MBED_ERROR_INVPARAM;
                goto err;
    }
err:
    return errcode;
}


/*
 * Clear the global STALL mode for the device
 */
mbed_error_t usbotghs_global_stall_clear(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    return errcode;
}


/*
 * Set the STALL mode for the given EP. This mode has priority on the global STALL mode
 */
/*@
  @ requires \separated(&GHOST_nopublicvar, ((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
 */
mbed_error_t usbotghs_endpoint_stall(uint8_t ep_id, usbotghs_ep_dir_t dir)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    uint32_t count = 0;

    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    /* sanitize */
    switch (dir) {
        case USBOTG_HS_EP_DIR_IN:
            if (ep_id >= USBOTGHS_MAX_IN_EP) {
                errcode = MBED_ERROR_INVPARAM;
                goto err;
            }
            if (ctx->in_eps[ep_id].configured == false) {
                errcode = MBED_ERROR_INVSTATE;
                goto err;
            }
            /* wait for end of current transmission */

            /*@
              @ loop invariant 0<=cpt<= CPT_HARD ;
              @ loop assigns count, cpt ;
              @ loop variant CPT_HARD - cpt;
              */

            for(uint8_t cpt=0; cpt<CPT_HARD; cpt++){
                if (get_reg_value(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id), USBOTG_HS_DIEPCTL_EPENA_Msk, USBOTG_HS_DIEPCTL_EPENA_Pos))  {
                    if (++count > USBOTGHS_REG_CHECK_TIMEOUT){
                        log_printf("[USBOTG][HS] HANG! DIEPCTL:EPENA\n");
                        errcode = MBED_ERROR_BUSY;
                        goto err;
                    }

                    continue; //FIXME TIMEOUT
                }
            }

            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id), USBOTG_HS_DIEPCTL_EPDIS_Msk);
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id), USBOTG_HS_DIEPCTL_STALL_Msk);
            break;
        case USBOTG_HS_EP_DIR_OUT:
            if (ep_id >= USBOTGHS_MAX_OUT_EP) {
                errcode = MBED_ERROR_INVPARAM;
                goto err;
            }
            if (ctx->out_eps[ep_id].configured == false) {
                errcode = MBED_ERROR_INVSTATE;
                goto err;
            }
            /* wait for end of current transmission */
            /*@
              @ loop invariant 0<=cpt<= CPT_HARD ;
              @ loop assigns count, cpt ;
              @ loop variant CPT_HARD - cpt;
              */

            for(uint8_t cpt=0; cpt<CPT_HARD; cpt++){
                if (get_reg_value(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_EPENA_Msk, USBOTG_HS_DOEPCTL_EPENA_Pos))  {
                    if (++count > USBOTGHS_REG_CHECK_TIMEOUT){
                        log_printf("[USBOTG][HS] HANG! DIEPCTL:EPENA\n");
                        errcode = MBED_ERROR_BUSY;
                        goto err;
                    }
                }
            }
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_EPDIS_Msk);
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_STALL_Msk);
            break;
        default:
            errcode = MBED_ERROR_INVPARAM;
            goto err;
    }

err:
    return errcode;
}

/*
 * Clear the STALL mode for the given EP
 */
mbed_error_t usbotghs_endpoint_stall_clear(uint8_t ep, usbotghs_ep_dir_t dir)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    ep = ep;
    dir = dir;
    return errcode;
}

/*
 * Activate EP (for e.g. before sending data). It can also be used in order to
 * configure a new endpoint with the given configuration (type, mode, data toggle,
 * FIFO informations)
 */
/*@
  @ requires \separated(GHOST_in_eps+(0 .. USBOTGHS_MAX_IN_EP - 1), GHOST_out_eps+(0 .. USBOTGHS_MAX_OUT_EP - 1), &GHOST_nopublicvar,&usbotghs_ctx.out_eps[0..(USBOTGHS_MAX_OUT_EP-1)], &usbotghs_ctx.in_eps[0..(USBOTGHS_MAX_IN_EP-1)],((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.in_eps[0..(USBOTGHS_MAX_IN_EP-1)], usbotghs_ctx, usbotghs_ctx.out_eps[0..(USBOTGHS_MAX_OUT_EP-1)] ;

  */
mbed_error_t usbotghs_configure_endpoint(uint8_t                 ep,
        usbotghs_ep_type_t      type,
        usbotghs_ep_dir_t       dir,
        usbotghs_epx_mpsize_t   mpsize,
        usbotghs_ep_toggle_t    dtoggle,
        usbotghs_ioep_handler_t handler)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    log_printf("[USBOTGHS] configure EP %d: dir %d, mpsize %d, type %x\n", ep, dir, mpsize, type);
    usbotghs_context_t *ctx = usbotghs_get_context();
    if (mpsize < 8 || mpsize > USBOTG_HS_TX_CORE_FIFO_SZ) {
        log_printf("[USBOTGHS] configure EP %d: mpsize to big for HW\n", ep);
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    /* sanitize */
    switch (dir) {
        case USBOTG_HS_EP_DIR_IN:
            log_printf("[USBOTGHS] enable EP %d: dir IN, mpsize %d, type %x\n", ep, mpsize, type);
            if (ep >= USBOTGHS_MAX_IN_EP) {
                errcode = MBED_ERROR_NOSTORAGE;
                goto err;
            }

            ctx->in_eps[ep].id = ep;
            ctx->in_eps[ep].dir = dir;
            ctx->in_eps[ep].configured = true;
            ctx->in_eps[ep].mpsize = mpsize;
            ctx->in_eps[ep].type = type;
            ctx->in_eps[ep].state = USBOTG_HS_EP_STATE_IDLE;
            //@ ghost GHOST_in_eps[ep].state = usbotghs_ctx.in_eps[ep].state;
            ctx->in_eps[ep].handler = handler;
            if (ep < USBOTGHS_MAX_OUT_EP) {
                ctx->out_eps[ep].configured = false;
            }

            /* set EP configuration */
            set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep), type,USBOTG_HS_DIEPCTL_EPTYP_Msk,USBOTG_HS_DIEPCTL_EPTYP_Pos);

            /* Maximum packet size */
            set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep), mpsize,USBOTG_HS_DIEPCTL_MPSIZ_Msk(ep),USBOTG_HS_DIEPCTL_MPSIZ_Pos(ep));

            if (type == USBOTG_HS_EP_TYPE_BULK || type == USBOTG_HS_EP_TYPE_INT) {
                set_reg(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep), dtoggle, USBOTG_HS_DIEPCTL_SD0PID);
            }
            /* set EP FIFO */
            usbotghs_reset_epx_fifo(&(ctx->in_eps[ep]));

            /* Enable endpoint */
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep), USBOTG_HS_DIEPCTL_USBAEP_Msk);
            set_reg(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep), ep, USBOTG_HS_DIEPCTL_CNAK);
            //PTH: set_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK, USBOTG_HS_GINTMSK_IEPINT_Msk);
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DAINTMSK, USBOTG_HS_DAINTMSK_IEPM(ep));
            break;


        case USBOTG_HS_EP_DIR_OUT:
            log_printf("[USBOTGHS] enable EP %d: dir OUT, mpsize %d, type %x\n", ep, mpsize, type);
            if (ep >= USBOTGHS_MAX_OUT_EP) {
                errcode = MBED_ERROR_NOSTORAGE;
                goto err;
            }

            ctx->out_eps[ep].id = ep;
            ctx->out_eps[ep].dir = dir;
            ctx->out_eps[ep].configured = true;
            ctx->out_eps[ep].mpsize = mpsize;
            ctx->out_eps[ep].type = type;
            ctx->out_eps[ep].state = USBOTG_HS_EP_STATE_IDLE;
            //@ ghost GHOST_out_eps[ep].state = usbotghs_ctx.out_eps[ep].state;
            ctx->out_eps[ep].handler = handler;
            if (ep < USBOTGHS_MAX_IN_EP) {
                ctx->in_eps[ep].configured = false;
            }

            /* Maximum packet size */
            set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep),mpsize, USBOTG_HS_DOEPCTL_MPSIZ_Msk(ep),USBOTG_HS_DOEPCTL_MPSIZ_Pos(ep));

            /*  USB active endpoint */
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep), USBOTG_HS_DOEPCTL_USBAEP_Msk);

            /* FIXME Start data toggle */
            if (type == USBOTG_HS_EP_TYPE_BULK || type == USBOTG_HS_EP_TYPE_INT) {
                set_reg(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep), dtoggle, USBOTG_HS_DOEPCTL_SD0PID);
            }

            /* Endpoint type */
            set_reg(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep), type, USBOTG_HS_DOEPCTL_EPTYP);
            /* set EP FIFO */
            usbotghs_reset_epx_fifo(&(ctx->out_eps[ep]));

            set_reg_bits(r_CORTEX_M_USBOTG_HS_DAINTMSK, USBOTG_HS_DAINTMSK_OEPM(ep));
            break;



        case USBOTG_HS_EP_DIR_BOTH:
            log_printf("[USBOTGHS] enable EP %d: dir IN/OUT, mpsize %d, type %x\n", ep, mpsize, type);
            if (ep >= USBOTGHS_MAX_OUT_EP || ep >= USBOTGHS_MAX_IN_EP) {
                errcode = MBED_ERROR_NOSTORAGE;
                goto err;
            }

            ctx->out_eps[ep].id = ep;
            ctx->out_eps[ep].dir = USBOTG_HS_EP_DIR_OUT;
            ctx->out_eps[ep].configured = true;
            ctx->out_eps[ep].mpsize = mpsize;
            ctx->out_eps[ep].type = type;
            ctx->out_eps[ep].state = USBOTG_HS_EP_STATE_IDLE;
            //@ ghost GHOST_out_eps[ep].state = usbotghs_ctx.out_eps[ep].state;
            ctx->out_eps[ep].handler = handler;

            ctx->in_eps[ep].id = ep;
            ctx->in_eps[ep].dir =  USBOTG_HS_EP_DIR_IN;
            ctx->in_eps[ep].configured = true;
            ctx->in_eps[ep].mpsize = mpsize;
            ctx->in_eps[ep].type = type;
            ctx->in_eps[ep].state = USBOTG_HS_EP_STATE_IDLE;
            //@ ghost GHOST_in_eps[ep].state = usbotghs_ctx.in_eps[ep].state;
            ctx->in_eps[ep].handler = handler;

            /* Maximum packet size */
            set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep),mpsize, USBOTG_HS_DOEPCTL_MPSIZ_Msk(ep),USBOTG_HS_DOEPCTL_MPSIZ_Pos(ep));
            set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep),mpsize, USBOTG_HS_DIEPCTL_MPSIZ_Msk(ep),USBOTG_HS_DIEPCTL_MPSIZ_Pos(ep));

            /*  USB active endpoint */
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep), USBOTG_HS_DOEPCTL_USBAEP_Msk);
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep), USBOTG_HS_DIEPCTL_USBAEP_Msk);

            /* FIXME Start data toggle */
            if (type == USBOTG_HS_EP_TYPE_BULK || type == USBOTG_HS_EP_TYPE_INT) {
                set_reg(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep), dtoggle, USBOTG_HS_DOEPCTL_SD0PID);
                set_reg(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep), dtoggle, USBOTG_HS_DIEPCTL_SD0PID);
            }

            /* Endpoint type */
            set_reg(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep), type, USBOTG_HS_DOEPCTL_EPTYP);
            set_reg(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep), type, USBOTG_HS_DIEPCTL_EPTYP);
            /* set EP FIFO */
            usbotghs_reset_epx_fifo(&(ctx->out_eps[ep]));
            usbotghs_reset_epx_fifo(&(ctx->in_eps[ep]));

            /* unmask out */
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DAINTMSK, USBOTG_HS_DAINTMSK_OEPM(ep));

            /* activate and unmask in */
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep), USBOTG_HS_DIEPCTL_USBAEP_Msk);
            set_reg(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep), ep, USBOTG_HS_DIEPCTL_CNAK);
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DAINTMSK, USBOTG_HS_DAINTMSK_IEPM(ep));
            break;

        default:
            errcode = MBED_ERROR_INVPARAM;
            break;
    }
err:
    return errcode;
}

/*
 * Dectivate EP.
 * This can be requested on SetConfiguration or SetInterface, when
 * a configuration change is required, which implies that some old EPs need to be
 * removed before creating new ones.
 */

/*@
  @ requires \separated(&GHOST_nopublicvar, &usbotghs_ctx,((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END));

  //@ ensures ((ep < USBOTGHS_MAX_IN_EP) && (ep >= USBOTGHS_MAX_OUT_EP) && (usbotghs_ctx.in_eps[ep].configured == \true)) ==> \result == MBED_ERROR_NONE;
  //@ ensures ((ep < USBOTGHS_MAX_IN_EP) && (ep >= USBOTGHS_MAX_OUT_EP) && (usbotghs_ctx.in_eps[ep].configured == \false)) ==> \result == MBED_ERROR_INVPARAM;
  //@ ensures ((ep < USBOTGHS_MAX_OUT_EP) && (usbotghs_ctx.in_eps[ep].configured == \false) && (usbotghs_ctx.out_eps[ep].configured == \false)) ==> \result == MBED_ERROR_INVPARAM;
  //@ ensures ((ep < USBOTGHS_MAX_OUT_EP) && ((usbotghs_ctx.in_eps[ep].configured == \true) || (usbotghs_ctx.out_eps[ep].configured == \true))) ==> \result == MBED_ERROR_NONE;
  */
mbed_error_t usbotghs_deconfigure_endpoint(uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_INVPARAM;
    usbotghs_context_t *ctx = usbotghs_get_context();

    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    /*@ assert ctx == &usbotghs_ctx; */

    clear_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK, USBOTG_HS_GINTMSK_NPTXFEM_Msk | USBOTG_HS_GINTMSK_RXFLVLM_Msk);

    if(ep < USBOTGHS_MAX_IN_EP) {
        if (ctx->in_eps[ep].configured == true) {
            /* FIX: flushing fifo for each EP */
            usbotghs_txfifo_flush(ep);

            clear_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep),
                    USBOTG_HS_DIEPCTL_EPENA_Msk);
            errcode = MBED_ERROR_NONE;
        }
    }

    if(ep < USBOTGHS_MAX_OUT_EP) {
        if (ctx->out_eps[ep].configured == true) {
            /* FIX: flushing fifo for each EP */
            usbotghs_rxfifo_flush(ep);

            clear_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep),
                    USBOTG_HS_DOEPCTL_EPENA_Msk);

            errcode = MBED_ERROR_NONE;
        }
    }

    set_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK, USBOTG_HS_GINTMSK_NPTXFEM_Msk | USBOTG_HS_GINTMSK_RXFLVLM_Msk);

    /*@ assert (errcode == MBED_ERROR_NONE || errcode == MBED_ERROR_INVPARAM); */
    return errcode;
}


/*
 * Configure given EP with given params
 * This function should be called on Set_Configuration & Set_Interface requests,
 * in compliance with the currently enabled configuration and interface(s)
 * hold by the libUSBCtrl
 */
/*@
  @  requires \separated(&GHOST_nopublicvar,r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id),r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id));
  @  assigns *(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id)) ;
  @  assigns *(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id)) ;
 */
mbed_error_t usbotghs_activate_endpoint(uint8_t               ep_id,
        usbotghs_ep_dir_t     dir)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    switch (dir) {
        case USBOTG_HS_EP_DIR_IN:
            if (ep_id >= USBOTGHS_MAX_IN_EP) {
                errcode = MBED_ERROR_INVPARAM;
                goto err;
            }
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id),
                    USBOTG_HS_DIEPCTL_EPENA_Msk);
            break;
        case USBOTG_HS_EP_DIR_OUT:
            if (ep_id >= USBOTGHS_MAX_OUT_EP) {
                errcode = MBED_ERROR_INVPARAM;
                goto err;
            }
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_CNAK_Msk);
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id),
                    USBOTG_HS_DOEPCTL_EPENA_Msk);
            break;
        default:
            errcode = MBED_ERROR_INVPARAM;
            break;
    }
err:
    return errcode;
}

/*@
  @ requires \separated(&GHOST_nopublicvar,&usbotghs_ctx,((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
  */
mbed_error_t usbotghs_deactivate_endpoint(uint8_t ep_id,
                                          usbotghs_ep_dir_t     dir)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    /* sanitize */
    if (dir != USBOTG_HS_EP_DIR_IN && dir != USBOTG_HS_EP_DIR_OUT) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (dir == USBOTG_HS_EP_DIR_IN && ep_id >= USBOTGHS_MAX_IN_EP) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (dir == USBOTG_HS_EP_DIR_OUT && ep_id >= USBOTGHS_MAX_OUT_EP) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    clear_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK, USBOTG_HS_GINTMSK_NPTXFEM_Msk | USBOTG_HS_GINTMSK_RXFLVLM_Msk);

    switch (dir) {
        case USBOTG_HS_EP_DIR_IN:
            clear_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id),
                    USBOTG_HS_DIEPCTL_EPENA_Msk);
            break;
        case USBOTG_HS_EP_DIR_OUT:
            clear_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id),
                    USBOTG_HS_DOEPCTL_EPENA_Msk);
            break;
        default:
            /* unreachable, requested by compiler quality check */
            /*@ assert \false; */
            break;

    }
    set_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK, USBOTG_HS_GINTMSK_NPTXFEM_Msk | USBOTG_HS_GINTMSK_RXFLVLM_Msk);

    /*@ assert errcode == MBED_ERROR_NONE; */
err:
    return errcode;
}

/*
 * Force EP to stop transmit (IN EP) or receive (OUT EP)
 */
/* disable (temporary) a given Endpoint (no more data is received or sent) */

/*@
  @ requires \separated(&GHOST_nopublicvar,&usbotghs_ctx,((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
 */
mbed_error_t usbotghs_endpoint_disable(uint8_t ep_id,
                                       usbotghs_ep_dir_t     dir)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_ep_t *ep = NULL;

    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;


    log_printf("[USBOTGHS] disable EP %d: dir %d\n", ep_id, dir);
    usbotghs_context_t *ctx = usbotghs_get_context();
    /*@ assert \valid(ctx); */
    switch (dir) {
        case USBOTG_HS_EP_DIR_IN:
            if (ep_id >= USBOTGHS_MAX_IN_EP) {
                errcode = MBED_ERROR_INVPARAM;
                goto err;
            }
            /*@ assert (ep_id < USBOTGHS_MAX_IN_EP && dir == USBOTG_HS_EP_DIR_IN); */
            ep = &(ctx->in_eps[ep_id]);
            break;
        case USBOTG_HS_EP_DIR_OUT:
            if (ep_id >= USBOTGHS_MAX_OUT_EP) {
                errcode = MBED_ERROR_INVPARAM;
                goto err;
            }
            /*@ assert (ep_id < USBOTGHS_MAX_OUT_EP && dir == USBOTG_HS_EP_DIR_OUT); */
            ep = &(ctx->in_eps[ep_id]);
            break;
        default:
            errcode = MBED_ERROR_INVPARAM;
            goto err;
            break;
    }
    set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id), 0x1,
            USBOTG_HS_DIEPCTL_EPDIS_Msk,
            USBOTG_HS_DIEPCTL_EPDIS_Pos);

    /*@ assert errcode == MBED_ERROR_NONE; */
err:
    return errcode;
}

/* enable a previously disabled Endpoint */
/*@
  @ requires \separated(&GHOST_nopublicvar,&usbotghs_ctx,((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
 */
mbed_error_t usbotghs_endpoint_enable(uint8_t ep_id,
        usbotghs_ep_dir_t     dir)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_ep_t *ep = NULL;

    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;


    log_printf("[USBOTGHS] enable EP %d: dir %d\n", ep_id, dir);
    usbotghs_context_t *ctx = usbotghs_get_context();
    /* sanitize */
    switch (dir) {
        case USBOTG_HS_EP_DIR_IN:
            if (ep_id >= USBOTGHS_MAX_IN_EP) {
                errcode = MBED_ERROR_INVPARAM;
                goto err;
            }
            /*@ assert (ep_id < USBOTGHS_MAX_IN_EP && dir == USBOTG_HS_EP_DIR_IN); */
            ep = &(ctx->in_eps[ep_id]);
            break;
        case USBOTG_HS_EP_DIR_OUT:
            if (ep_id >= USBOTGHS_MAX_OUT_EP) {
                errcode = MBED_ERROR_INVPARAM;
                goto err;
            }
            /*@ assert (ep_id < USBOTGHS_MAX_OUT_EP && dir == USBOTG_HS_EP_DIR_OUT); */
            ep = &(ctx->in_eps[ep_id]);
            break;
        default:
            errcode = MBED_ERROR_INVPARAM;
            goto err;
            break;
    }
    set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id), 0x0,
            USBOTG_HS_DIEPCTL_EPDIS_Msk,
            USBOTG_HS_DIEPCTL_EPDIS_Pos);
    /*@ assert errcode == MBED_ERROR_NONE; */
err:
    return errcode;


}

/*@
  @ requires \separated(&GHOST_nopublicvar, ((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
  */
void usbotghs_set_address(uint16_t addr)
{
    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    set_reg(r_CORTEX_M_USBOTG_HS_DCFG, addr, USBOTG_HS_DCFG_DAD);
}

/*@

  // private function contract
  @ ensures ( dir == USBOTG_HS_EP_DIR_IN && epnum < USBOTGHS_MAX_IN_EP) ==> \result == usbotghs_ctx.in_eps[epnum].state ;
  @ ensures ( dir == USBOTG_HS_EP_DIR_IN && epnum < USBOTGHS_MAX_IN_EP) ==> \result == GHOST_in_eps[epnum].state ;

  @ ensures ( dir == USBOTG_HS_EP_DIR_OUT && epnum < USBOTGHS_MAX_OUT_EP) ==> \result == usbotghs_ctx.out_eps[epnum].state ;
  @ ensures ( dir == USBOTG_HS_EP_DIR_OUT && epnum < USBOTGHS_MAX_OUT_EP) ==> \result == GHOST_out_eps[epnum].state ;

 */
usbotghs_ep_state_t usbotghs_get_ep_state(uint8_t epnum, usbotghs_ep_dir_t dir)
{
    if (dir == USBOTG_HS_EP_DIR_IN && epnum >= USBOTGHS_MAX_IN_EP) {
        return USBOTG_HS_EP_STATE_INVALID;
    }
    if (dir == USBOTG_HS_EP_DIR_OUT && epnum >= USBOTGHS_MAX_OUT_EP) {
        return USBOTG_HS_EP_STATE_INVALID;
    }
    switch (dir) {
        case USBOTG_HS_EP_DIR_IN:
            return usbotghs_ctx.in_eps[epnum].state;
            break;
        case USBOTG_HS_EP_DIR_OUT:
            return usbotghs_ctx.out_eps[epnum].state;
            break;
        default:
            /* even for full-duplex endpoint, select one of the active direction */
            return USBOTG_HS_EP_STATE_INVALID;
            break;
    }
    return USBOTG_HS_EP_STATE_INVALID;
}

usbotghs_port_speed_t usbotghs_get_speed(void)
{
    return USBOTG_HS_PORT_HIGHSPEED;
}
/*
 * About generic part:
 * This part translate libusbctrl forward-declaration symbols to local symbols.
 * This permits to resolve all symbols of the libctrl abstraction layer into this
 * very driver one.
 * WARNING: this method has one single restriction: only one driver can be used
 * at a time by a given ELF binary (i.e. an application), as symbols are resolved
 * at link time.
 */

/* aliasing no working well with framac, driver functions defined in lib USBctrl */
#ifndef __FRAMAC__

mbed_error_t usb_backend_drv_configure(usb_backend_drv_mode_t mode,
        usb_backend_drv_ioep_handler_t ieph,
        usb_backend_drv_ioep_handler_t oeph)
    __attribute__ ((alias("usbotghs_configure")));

mbed_error_t usb_backend_drv_declare(void)
    __attribute__ ((alias("usbotghs_declare")));
mbed_error_t usb_backend_drv_activate_endpoint(uint8_t               id,
        usb_backend_drv_ep_dir_t     dir)
    __attribute__ ((alias("usbotghs_activate_endpoint")));
mbed_error_t usb_backend_drv_configure_endpoint(uint8_t               ep,
        usb_backend_drv_ep_type_t    type,
        usb_backend_drv_ep_dir_t     dir,
        usb_backend_drv_epx_mpsize_t mpsize,
        usb_backend_drv_ep_toggle_t  dtoggle,
        usb_backend_drv_ioep_handler_t handler)
    __attribute__ ((alias("usbotghs_configure_endpoint")));

mbed_error_t usb_backend_drv_deconfigure_endpoint(uint8_t ep)
    __attribute__ ((alias("usbotghs_deconfigure_endpoint")));

usb_backend_drv_ep_state_t  usb_backend_drv_get_ep_state(uint8_t epnum, usb_backend_drv_ep_dir_t dir)
    __attribute__ ((alias("usbotghs_get_ep_state")));
mbed_error_t usb_backend_drv_send_data(uint8_t *src, uint32_t size, uint8_t ep)
    __attribute__ ((alias("usbotghs_send_data")));
mbed_error_t usb_backend_drv_send_zlp(uint8_t ep)
    __attribute__ ((alias("usbotghs_send_zlp")));
void         usb_backend_drv_set_address(uint16_t addr)
    __attribute__ ((alias("usbotghs_set_address")));
    /* USB protocol standard handshaking */
mbed_error_t usb_backend_drv_ack(uint8_t ep_id, usb_backend_drv_ep_dir_t dir)
    __attribute__ ((alias("usbotghs_endpoint_clear_nak")));
mbed_error_t usb_backend_drv_nak(uint8_t ep_id, usb_backend_drv_ep_dir_t dir)
    __attribute__ ((alias("usbotghs_endpoint_set_nak")));
mbed_error_t usb_backend_drv_stall(uint8_t ep_id, usb_backend_drv_ep_dir_t dir)
    __attribute__ ((alias("usbotghs_endpoint_stall")));
mbed_error_t usb_backend_drv_endpoint_disable(uint8_t ep_id, usb_backend_drv_ep_dir_t dir)
    __attribute__ ((alias("usbotghs_endpoint_disable")));
mbed_error_t usb_backend_drv_endpoint_enable(uint8_t ep_id, usb_backend_drv_ep_dir_t dir)
    __attribute__ ((alias("usbotghs_endpoint_enable")));

uint16_t usb_backend_get_ep_mpsize(void) __attribute__ ((alias("usbotghs_get_ep_mpsize")));
usb_backend_drv_port_speed_t usb_backend_drv_get_speed(void) __attribute__ ((alias("usbotghs_get_speed")));


#endif/*!__FRAMAC__*/
