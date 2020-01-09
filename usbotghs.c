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
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#include "autoconf.h"

#include "libc/syscall.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/string.h"
#include "generated/usb_otg_hs.h"

#include "api/libusbotghs.h"
#include "usbotghs.h"
#include "usbotghs_init.h"
#include "usbotghs_fifos.h"
#include "usbotghs_handler.h"
#include "usbotghs_regs.h"
#include "ulpi.h"


#define ZERO_LENGTH_PACKET 0
#define OUT_NAK		0x01
#define DataOUT		0x02
#define Data_Done	0x03
#define SETUP_Done	0x04
#define SETUP		0x06

#define USB_REG_CHECK_TIMEOUT 50

#define USBOTG_HS_RX_FIFO_SZ 	512
#define USBOTG_HS_TX_FIFO_SZ	512

#define USBOTG_HS_DEBUG 0

/******************************************************************
 * Utilities
 */
/* wait while the iepint (or oepint in host mode) clear the DATA_OUT state */
static void usbotghs_wait_for_xmit_complete(usbotghs_ep_t *ep)
{
    do {
        ;
    } while (ep->state != USBOTG_HS_EP_STATE_IDLE);
    return;
}

/******************************************************************
 * Defining functional API
 */

static const char *devname = "usb-otg-hs";
/* buffer for setup packets */
// TODO to use static uint8_t 	setup_packet[8];

/* local context. Only one as there is one USB OTG device per SoC */
static volatile usbotghs_context_t usbotghs_ctx = { 0 };

usbotghs_context_t *usbotghs_get_context(void)
{
    return (usbotghs_context_t *)&usbotghs_ctx;
}

mbed_error_t usbotghs_declare(void)
{
    e_syscall_ret ret = 0;

    log_printf("[USBOTG][HS] Declaring device\n");
    memset((void*)&(usbotghs_ctx.dev), 0, sizeof(device_t));

    memcpy((void*)usbotghs_ctx.dev.name, devname, strlen(devname));

    usbotghs_ctx.dev.address = USB_OTG_HS_BASE;
    usbotghs_ctx.dev.size = 0x4000;
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
    usbotghs_ctx.dev.irqs[0].posthook.action[2].mask.offset_mask = 0x18; /* MASK register offset */
    usbotghs_ctx.dev.irqs[0].posthook.action[2].mask.mode = 0; /* no binary inversion */


    usbotghs_ctx.dev.irqs[0].posthook.action[3].instr = IRQ_PH_AND;
    usbotghs_ctx.dev.irqs[0].posthook.action[3].and.offset_dest = 0x18; /* MASK register offset */
    usbotghs_ctx.dev.irqs[0].posthook.action[3].and.offset_src = 0x14; /* MASK register offset */
    usbotghs_ctx.dev.irqs[0].posthook.action[3].and.mask =
                 USBOTG_HS_GINTMSK_USBRST_Msk   |
                 USBOTG_HS_GINTMSK_ENUMDNEM_Msk |
                 USBOTG_HS_GINTMSK_ESUSPM_Msk   |
                 USBOTG_HS_GINTMSK_USBSUSPM_Msk |
                 USBOTG_HS_GINTMSK_SOFM_Msk     |
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
//static mbed_error_t usbotghs_core_init;

mbed_error_t usbotghs_configure(usbotghs_dev_mode_t mode)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* First, reset the PHY device connected to the core through ULPI interface */
    log_printf("[USB HS] Mapping device\n");
    if (sys_cfg(CFG_DEV_MAP, usbotghs_ctx.dev_desc)) {
        log_printf("[USB HS] Unable to map USB device !!!\n");
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }
    if ((errcode = usbotghs_ulpi_reset()) != MBED_ERROR_NONE) {
        goto err;
    }
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
    usbotghs_ctx.mode = mode;

    /* initialize EP0, which is both IN & OUT EP */
    usbotghs_ctx.in_eps[0].id = 0;
    usbotghs_ctx.in_eps[0].configured = false; /* wait for reset */
    usbotghs_ctx.in_eps[0].mpsize = USBOTG_HS_EP0_MPSIZE_64BYTES;
    usbotghs_ctx.in_eps[0].type = USBOTG_HS_EP_TYPE_CONTROL;
    usbotghs_ctx.in_eps[0].state = USBOTG_HS_EP_STATE_IDLE;
    usbotghs_ctx.in_eps[0].fifo = NULL; /* not yet configured */
    usbotghs_ctx.in_eps[0].fifo_idx = 0; /* not yet configured */
    usbotghs_ctx.in_eps[0].fifo_size = 0; /* not yet configured */
    usbotghs_ctx.in_eps[0].fifo_lck = false;

    usbotghs_ctx.out_eps[0].id = 0;
    usbotghs_ctx.out_eps[0].configured = false; /* wait for reset */
    usbotghs_ctx.out_eps[0].mpsize = USBOTG_HS_EP0_MPSIZE_64BYTES;
    usbotghs_ctx.out_eps[0].type = USBOTG_HS_EP_TYPE_CONTROL;
    usbotghs_ctx.out_eps[0].state = USBOTG_HS_EP_STATE_IDLE;
    usbotghs_ctx.out_eps[0].fifo = 0; /* not yet configured */
    usbotghs_ctx.out_eps[0].fifo_idx = 0; /* not yet configured */
    usbotghs_ctx.out_eps[0].fifo_size = 0; /* not yet configured */
    usbotghs_ctx.in_eps[0].fifo_lck = false;

err:
    return errcode;
}

/*
 * Sending data put content in the USB OTG FIFO and ask the EP to read from it to
 * send the data on the line (by activating the EP (field USBAEP of out EPs))
 * We must wait data sent IT to be sure that content is effectively transmitted
 */
mbed_error_t usbotghs_send_data(uint8_t *src, uint32_t size, uint8_t ep_id)
{
    uint32_t packet_count = 0;
    mbed_error_t errcode = MBED_ERROR_NONE;

    usbotghs_context_t *ctx = usbotghs_get_context();
    usbotghs_ep_t *ep = NULL;

    if (ctx->mode == USBOTGHS_MODE_HOST) {
      ep = &ctx->out_eps[ep_id];
    } else {
      ep = &ctx->in_eps[ep_id];
    }
    if (!ep->configured) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /*
     * Here, we have to split the src content, taking into account the
     * current EP mpsize, and schedule transmission into the Core TxFIFO.
     */
    /* first set xmit fifo with given argument */
    usbotghs_set_xmit_fifo(src, size, ep_id);

    /* we loop while size is bigger than EPx Core TxFIFO size. Core TxFIFO size
     * is bigger (or equal) to mpsize (ideally bigger), which means that we can
     * transfer to the core TxFIFO size of the EP multiple mpsize packets
     * and a potential residual short packet while the FIFO is not full.
     * Yet, if we needs to consume more than the FIFO size, we need to
     * repeat this operation multiple time by:
     * 1. Set the transfert size (depending on the current FIFO free space) and the packet
     *    count (equal to the number of mpsize packets + short packet that need to be
     *    transfered
     * 2. Fullfill the FIFO
     * 3. Request a transmission of these packets
     * 4. check the Status flag to be sure that data has been sent (or wait for
     *    Endpoint diabled IT)
     * 4. Loop again with the next offset of the input src buffer, while there is still
     *    some data to send.
     *
     *    FIXME: BELOW TO REPLACE
     */
    for (; size >= ep->mpsize; size -= ep->mpsize) {
        /* Program the transfer size and packet count as follows:
         *      xfersize = N * maxpacket + short_packet pktcnt = N + (short_packet exist ? 1 : 0)
         */
        packet_count = 0; //(size / ep->mpsize) + (size & ep->mpsize-1) ? 1 : 0);

        if (ctx->mode == USBOTGHS_MODE_DEVICE) {
            /* 1. Program the OTG_HS_DIEPTSIZx register for the transfer size
             * and the corresponding packet count. */
            set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),
                      packet_count,
                      USBOTG_HS_DIEPTSIZ_PKTCNT_Msk(ep_id),
                      USBOTG_HS_DIEPTSIZ_PKTCNT_Pos(ep_id));

            set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),
                    size,
                    USBOTG_HS_DIEPTSIZ_XFRSIZ_Msk(ep_id),
                    USBOTG_HS_DIEPTSIZ_XFRSIZ_Pos(ep_id));
            /* 2. Enable endpoint for transmission. */
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id),
                    USBOTG_HS_DIEPCTL_CNAK_Msk | USBOTG_HS_DIEPCTL_EPENA_Msk);
        } else {
            /* 1. Program the OTG_HS_DOEPTSIZx register for the transfer size
             * and the corresponding packet count. */
            set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(ep_id),
                      packet_count,
                      USBOTG_HS_DOEPTSIZ_PKTCNT_Msk(ep_id),
                      USBOTG_HS_DOEPTSIZ_PKTCNT_Pos(ep_id));

            set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(ep_id),
                    size,
                    USBOTG_HS_DOEPTSIZ_XFRSIZ_Msk(ep_id),
                    USBOTG_HS_DOEPTSIZ_XFRSIZ_Pos(ep_id));
            /* 2. Enable endpoint for transmission. */

            set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id),
                    USBOTG_HS_DOEPCTL_CNAK_Msk | USBOTG_HS_DOEPCTL_EPENA_Msk);
        }
        ep->state = USBOTG_HS_EP_STATE_DATA_OUT;
        usbotghs_write_epx_fifo(ep->mpsize, ep);
        /* wait for XMIT data to be transfered (wait for iepint (or oepint in
         * host mode) to set the EP in correct state */
        usbotghs_wait_for_xmit_complete(ep);

    }
    /* residual */
    if (size) {
        packet_count = (size / ep->mpsize) + (size & (MAX_DATA_PACKET_SIZE(ep)-1) ? 1 : 0);


        if (ctx->mode == USBOTGHS_MODE_DEVICE) {
            /* 1. Program the OTG_HS_DIEPTSIZx register for the transfer size
             * and the corresponding packet count. */
            set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),
                      packet_count,
                      USBOTG_HS_DIEPTSIZ_PKTCNT_Msk(ep_id),
                      USBOTG_HS_DIEPTSIZ_PKTCNT_Pos(ep));

            set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),
                    size,
                    USBOTG_HS_DIEPTSIZ_XFRSIZ_Msk(ep_id),
                    USBOTG_HS_DIEPTSIZ_XFRSIZ_Pos(ep_id));
            /* 2. Enable endpoint for transmission. */
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id),
                    USBOTG_HS_DIEPCTL_CNAK_Msk | USBOTG_HS_DIEPCTL_EPENA_Msk);
        } else {
            /* 1. Program the OTG_HS_DOEPTSIZx register for the transfer size
             * and the corresponding packet count. */
            set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(ep_id),
                      packet_count,
                      USBOTG_HS_DOEPTSIZ_PKTCNT_Msk(ep_id),
                      USBOTG_HS_DOEPTSIZ_PKTCNT_Pos(ep_id));

            set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(ep_id),
                    size,
                    USBOTG_HS_DOEPTSIZ_XFRSIZ_Msk(ep_id),
                    USBOTG_HS_DOEPTSIZ_XFRSIZ_Pos(ep_id));
            /* 2. Enable endpoint for transmission. */

            set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id),
                    USBOTG_HS_DOEPCTL_CNAK_Msk | USBOTG_HS_DOEPCTL_EPENA_Msk);
        }
        ep->state = USBOTG_HS_EP_STATE_DATA_OUT;
        usbotghs_write_epx_fifo(size, ep);
        usbotghs_wait_for_xmit_complete(ep);
    }
err:
    return errcode;
}

/*
 * Send a Zero-length packet into EP 'ep'
 */
mbed_error_t usbotghs_send_zlp(uint8_t ep_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    usbotghs_ep_t *ep = NULL;

    if (ctx->mode == USBOTGHS_MODE_HOST) {
      ep = &ctx->out_eps[ep_id];
    } else {
      ep = &ctx->in_eps[ep_id];
    }
    if (!ep->configured) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* EP is now in DATA_OUT state */
    ep->state = USBOTG_HS_EP_STATE_DATA_OUT;
    if (ctx->mode == USBOTGHS_MODE_DEVICE) {
        /* 1. Program the OTG_HS_DIEPTSIZx register for the transfer size
         * and the corresponding packet count. */
        set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),
                1,
                USBOTG_HS_DIEPTSIZ_PKTCNT_Msk(ep_id),
                USBOTG_HS_DIEPTSIZ_PKTCNT_Pos(ep_id));

        set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),
                0,
                USBOTG_HS_DIEPTSIZ_XFRSIZ_Msk(ep_id),
                USBOTG_HS_DIEPTSIZ_XFRSIZ_Pos(ep_id));
        /* 2. Enable endpoint for transmission. */
        set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id),
                USBOTG_HS_DIEPCTL_CNAK_Msk | USBOTG_HS_DIEPCTL_EPENA_Msk);
    } else {
        /* 1. Program the OTG_HS_DOEPTSIZx register for the transfer size
         * and the corresponding packet count. */
        set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(ep_id),
                1,
                USBOTG_HS_DOEPTSIZ_PKTCNT_Msk(ep_id),
                USBOTG_HS_DOEPTSIZ_PKTCNT_Pos(ep_id));

        set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(ep_id),
                0,
                USBOTG_HS_DOEPTSIZ_XFRSIZ_Msk(ep_id),
                USBOTG_HS_DOEPTSIZ_XFRSIZ_Pos(ep_id));
        /* 2. Enable endpoint for transmission. */
        set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id),
                USBOTG_HS_DOEPCTL_CNAK_Msk | USBOTG_HS_DOEPCTL_EPENA_Msk);
    }
    /* wait for XMIT data to be transfered (wait for iepint (or oepint in
     * host mode) to set the EP in correct state */
    usbotghs_wait_for_xmit_complete(ep);
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
mbed_error_t usbotghs_endpoint_stall(uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    ep = ep;
    return errcode;
}

/*
 * Clear the STALL mode for the given EP
 */
mbed_error_t usbotghs_endpoint_stall_clear(uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    ep = ep;
    return errcode;
}

/*
 * Activate EP (for e.g. before sending data). It can also be used in order to
 * configure a new endpoint with the given configuration (type, mode, data toggle,
 * FIFO informations)
 */
mbed_error_t usbotghs_activate_endpoint(uint8_t               ep,
                                        usbotghs_ep_type_t    type,
                                        usbotghs_epx_mpsize_t mpsize,
                                        usbotghs_ep_toggle_t  dtoggle)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    ep = ep;
    type = type;
    mpsize = mpsize;
    dtoggle = dtoggle;
    return errcode;
}

/*
 * Dectivate EP.
 * This can be requested on SetConfiguration or SetInterface, when
 * a configuration change is required, which implies that some old EPs need to be
 * removed before creating new ones.
 */
mbed_error_t usbotghs_deactivate_endpoint(uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    ep = ep;
    return errcode;
}


/*
 * Configure given EP with given params
 * This function should be called on Set_Configuration & Set_Interface requests,
 * in compliance with the currently enabled configuration and interface(s)
 * hold by the libUSBCtrl
 */
mbed_error_t usbotghs_configure_endpoint(uint8_t                id,
                                         usbotghs_ep_type_t     type,
                                         usbotghs_epx_mpsize_t  mpsize)
{

    mbed_error_t errcode = MBED_ERROR_NONE;
    id = id;
    type = type;
    mpsize = mpsize;
    return errcode;
}

mbed_error_t usbotghs_deconfigure_endpoint(uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    ep = ep;
    return errcode;
}

/*
 * Force EP to stop transmit (IN EP) or receive (OUT EP)
 */
mbed_error_t usbotghs_enpoint_nak(uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    ep = ep;
    return errcode;
}

/*
 * Leave the NAK (freezed) mode for given EP
 */
mbed_error_t usbotghs_enpoint_nak_clear(uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    ep = ep;
    return errcode;
}

void usbotghs_set_address(uint16_t addr)
{
    set_reg(r_CORTEX_M_USBOTG_HS_DCFG, addr, USBOTG_HS_DCFG_DAD);
}

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
            return USBOTG_HS_EP_STATE_INVALID;
            break;
    }
    return USBOTG_HS_EP_STATE_INVALID;
}
