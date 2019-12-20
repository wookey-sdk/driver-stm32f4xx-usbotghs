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
 * Defining functional API
 */

static const char *devname = "usb-otg-hs";
/* buffer for setup packets */
// TODO to use static uint8_t 	setup_packet[8];

/* local context. Only one as there is one USB OTG device per SoC */
static volatile usbotghs_context_t ctx = { 0 };

usbotghs_context_t *usbotghs_get_context(void)
{
    return (usbotghs_context_t *)&ctx;
}

mbed_error_t usbotghs_declare(void)
{
    e_syscall_ret ret = 0;
    memset((void*)&(ctx.dev), 0, sizeof(device_t));

    memcpy((void*)ctx.dev.name, devname, strlen(devname));

    ctx.dev.address = USB_OTG_HS_BASE;
    ctx.dev.size = 0x4000;
    ctx.dev.irq_num = 1;
    /* device is mapped voluntary and will be activated after the full
     * authentication sequence
     */
    ctx.dev.map_mode = DEV_MAP_VOLUNTARY;

    /* IRQ configuration */
    ctx.dev.irqs[0].handler = USBOTGHS_IRQHandler;
    ctx.dev.irqs[0].irq = OTG_HS_IRQ; /* starting with STACK */
    ctx.dev.irqs[0].mode = IRQ_ISR_FORCE_MAINTHREAD; /* if ISR force MT immediat execution, use FORCE_MAINTHREAD instead of STANDARD, and activate FISR permission */

    /*
     * IRQ posthook configuration
     * The posthook is executed at the end of the IRQ handler mode, *before* the ISR.
     * It permit to clean potential status registers (or others) that may generate IRQ loops
     * while the ISR has not been executed.
     * register read can be saved into 'status' and 'data' and given to the ISR in 'sr' and 'dr' argument
     */
    ctx.dev.irqs[0].posthook.status = 0x0014; /* SR is first read */
    ctx.dev.irqs[0].posthook.data = 0x0018; /* Data reg  is 2nd read */


    ctx.dev.irqs[0].posthook.action[0].instr = IRQ_PH_READ;
    ctx.dev.irqs[0].posthook.action[0].read.offset = 0x0014;


    ctx.dev.irqs[0].posthook.action[1].instr = IRQ_PH_READ;
    ctx.dev.irqs[0].posthook.action[1].read.offset = 0x0018;


    ctx.dev.irqs[0].posthook.action[2].instr = IRQ_PH_MASK;
    ctx.dev.irqs[0].posthook.action[2].mask.offset_dest = 0x14; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[2].mask.offset_src = 0x14; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[2].mask.offset_mask = 0x18; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[2].mask.mode = 0; /* no binary inversion */


    ctx.dev.irqs[0].posthook.action[3].instr = IRQ_PH_AND;
    ctx.dev.irqs[0].posthook.action[3].and.offset_dest = 0x18; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[3].and.offset_src = 0x14; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[3].and.mask = USBOTG_HS_GINTMSK_RXFLVLM_Msk; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[3].and.mode = 1; /* binary inversion */


    ctx.dev.irqs[0].posthook.action[4].instr = IRQ_PH_AND;
    ctx.dev.irqs[0].posthook.action[4].and.offset_dest = 0x18; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[4].and.offset_src = 0x14; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[4].and.mask = USBOTG_HS_GINTMSK_IEPINT_Msk; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[4].and.mode = 1; /* binary inversion */


    ctx.dev.irqs[0].posthook.action[5].instr = IRQ_PH_AND;
    ctx.dev.irqs[0].posthook.action[5].and.offset_dest = 0x18; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[5].and.offset_src = 0x14; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[5].and.mask = USBOTG_HS_GINTMSK_OEPINT_Msk; /* MASK register offset */
    ctx.dev.irqs[0].posthook.action[5].and.mode = 1; /* binary inversion */



    /* Now let's configure the GPIOs */
    ctx.dev.gpio_num = 13;

	/* ULPI_D0 */
    ctx.dev.gpios[0].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;
    ctx.dev.gpios[0].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_D0].port;
    ctx.dev.gpios[0].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_D0].pin; /* 3 */
    ctx.dev.gpios[0].mode         = GPIO_PIN_ALTERNATE_MODE;
    ctx.dev.gpios[0].pupd         = GPIO_NOPULL;
    ctx.dev.gpios[0].type         = GPIO_PIN_OTYPER_PP;
    ctx.dev.gpios[0].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    ctx.dev.gpios[0].afr          = GPIO_AF_OTG_HS;

	/* ULPI_CLK */
    ctx.dev.gpios[1].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;
    ctx.dev.gpios[1].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_CLK].port;
    ctx.dev.gpios[1].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_CLK].pin; /* 3 */
    ctx.dev.gpios[1].mode         = GPIO_PIN_ALTERNATE_MODE;
    ctx.dev.gpios[1].pupd         = GPIO_NOPULL;
    ctx.dev.gpios[1].type         = GPIO_PIN_OTYPER_PP;
    ctx.dev.gpios[1].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    ctx.dev.gpios[1].afr          = GPIO_AF_OTG_HS;

    for (uint8_t i = USB_HS_ULPI_D1; i <= USB_HS_ULPI_D7; ++i) {
        /* INFO: for this loop to work, USBOTG_HS_ULPI_D1 must start at index 2
         * in the JSON file */
        /* ULPI_Di */
        ctx.dev.gpios[i].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;
        ctx.dev.gpios[i].kref.port    = usb_otg_hs_dev_infos.gpios[i].port;
        ctx.dev.gpios[i].kref.pin     = usb_otg_hs_dev_infos.gpios[i].pin;
        ctx.dev.gpios[i].mode         = GPIO_PIN_ALTERNATE_MODE;
        ctx.dev.gpios[i].pupd         = GPIO_NOPULL;
        ctx.dev.gpios[i].type         = GPIO_PIN_OTYPER_PP;
        ctx.dev.gpios[i].speed        = GPIO_PIN_VERY_HIGH_SPEED;
        ctx.dev.gpios[i].afr          = GPIO_AF_OTG_HS;
    }

    /* ULPI_STP */
    ctx.dev.gpios[9].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;
    ctx.dev.gpios[9].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_STP].port;
    ctx.dev.gpios[9].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_STP].pin; /* 3 */
    ctx.dev.gpios[9].mode         = GPIO_PIN_ALTERNATE_MODE;
    ctx.dev.gpios[9].pupd         = GPIO_NOPULL;
    ctx.dev.gpios[9].type         = GPIO_PIN_OTYPER_PP;
    ctx.dev.gpios[9].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    ctx.dev.gpios[9].afr          = GPIO_AF_OTG_HS;

    /* ULPI_DIR */
    ctx.dev.gpios[10].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;
    ctx.dev.gpios[10].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_DIR].port;
    ctx.dev.gpios[10].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_DIR].pin; /* 3 */
    ctx.dev.gpios[10].mode         = GPIO_PIN_ALTERNATE_MODE;
    ctx.dev.gpios[10].pupd         = GPIO_NOPULL;
    ctx.dev.gpios[10].type         = GPIO_PIN_OTYPER_PP;
    ctx.dev.gpios[10].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    ctx.dev.gpios[10].afr          = GPIO_AF_OTG_HS;

    /* ULPI_NXT */
    ctx.dev.gpios[11].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;

    ctx.dev.gpios[11].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_NXT].port;
    ctx.dev.gpios[11].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_ULPI_NXT].pin; /* 3 */
    ctx.dev.gpios[11].mode         = GPIO_PIN_ALTERNATE_MODE;
    ctx.dev.gpios[11].pupd         = GPIO_NOPULL;
    ctx.dev.gpios[11].type         = GPIO_PIN_OTYPER_PP;
    ctx.dev.gpios[11].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    ctx.dev.gpios[11].afr          = GPIO_AF_OTG_HS;

    /* Reset */
    ctx.dev.gpios[12].mask         = GPIO_MASK_SET_MODE | GPIO_MASK_SET_PUPD | GPIO_MASK_SET_TYPE | GPIO_MASK_SET_SPEED | GPIO_MASK_SET_AFR;

    ctx.dev.gpios[12].kref.port    = usb_otg_hs_dev_infos.gpios[USB_HS_RESET].port;
    ctx.dev.gpios[12].kref.pin     = usb_otg_hs_dev_infos.gpios[USB_HS_RESET].pin; /* 3 */
    ctx.dev.gpios[12].mode         = GPIO_PIN_OUTPUT_MODE;
    ctx.dev.gpios[12].pupd         = GPIO_PULLUP;//GPIO_PULLDOWN;
    ctx.dev.gpios[12].type         = GPIO_PIN_OTYPER_PP;
    ctx.dev.gpios[12].speed        = GPIO_PIN_VERY_HIGH_SPEED;
    ctx.dev.gpios[12].afr          = GPIO_AF_OTG_HS;

    if ((ret == sys_init(INIT_DEVACCESS, (device_t*)&(ctx.dev), (int*)&(ctx.dev_desc))) != SYS_E_DONE) {
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
            log_printf("[USB HS][DEVICE] initialize in Host mode\n");
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
    ctx.mode = mode;

    /* initialize EP0, which is both IN & OUT EP */
    ctx.in_eps[0].id = 0;
    ctx.in_eps[0].configured = false; /* wait for reset */
    ctx.in_eps[0].mpsize = USBOTG_HS_EP0_MPSIZE_64BYTES;
    ctx.in_eps[0].type = USBOTG_HS_EP_TYPE_CONTROL;
    ctx.in_eps[0].state = USBOTG_HS_EP_STATE_IDLE;
    ctx.in_eps[0].fifo = 0; /* not yet configured */
    ctx.in_eps[0].fifo_idx = 0; /* not yet configured */
    ctx.in_eps[0].fifo_size = 0; /* not yet configured */

    ctx.out_eps[0].id = 0;
    ctx.out_eps[0].configured = false; /* wait for reset */
    ctx.out_eps[0].mpsize = USBOTG_HS_EP0_MPSIZE_64BYTES;
    ctx.out_eps[0].type = USBOTG_HS_EP_TYPE_CONTROL;
    ctx.out_eps[0].state = USBOTG_HS_EP_STATE_IDLE;
    ctx.out_eps[0].fifo = 0; /* not yet configured */
    ctx.out_eps[0].fifo_idx = 0; /* not yet configured */
    ctx.out_eps[0].fifo_size = 0; /* not yet configured */

err:
    return errcode;
}

/*
 * Sending data put content in the USB OTG FIFO and ask the EP to read from it to
 * send the data on the line (by activating the EP (field USBAEP of out EPs))
 * We must wait data sent IT to be sure that content is effectively transmitted
 */
mbed_error_t usbotghs_send_data(const uint8_t *src, uint32_t size, uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    src = src;
    size = size;
    ep = ep;
    return errcode;
}

/*
 * Read from a given input EP.
 */
mbed_error_t usbotghs_recv_data(uint8_t *dst, uint32_t size, uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    dst = dst;
    size = size;
    ep = ep;
    return errcode;
}

/*
 * Send a Zero-length packet into EP 'ep'
 */
mbed_error_t usbotghs_send_zlp(uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    ep = ep;
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
