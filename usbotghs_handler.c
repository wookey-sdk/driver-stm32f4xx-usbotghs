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

#include "libc/regutils.h"
#include "libc/types.h"
#include "libc/stdio.h"

#include "api/libusbotghs.h"
#include "usbotghs_regs.h"
#include "usbotghs.h"

#include "usbotghs_handler.h"

/************************************************
 * About ISR handlers
 */
/*
 * interrupt flag bit identifier, as set in the INTSTS global interrupt status register
 * Some of these interrupts required an execution of a stack level handler, other not.
 *
 * When an interrupt is handled, all the bits must be checked against the following
 * bitfield definition, as multiple event may occur in the same time, and as a consequence be
 * handled in the same ISR.
 */
typedef enum {
    USBOTGHS_IT_CMOD       = 0,    /*< Current Mode of Operation  */
    USBOTGHS_IT_MMIS       = 1,    /*< Mode mismatch */
    USBOTGHS_IT_OTGINT     = 2,    /*< OTG interrupt */
    USBOTGHS_IT_SOF        = 3,    /*< Start of Frame */
    USBOTGHS_IT_XFLVL      = 4,    /*< RxFifo non-empty */
    USBOTGHS_IT_NPTXE      = 5,    /*< Non-periodic TxFIFO empty (Host mode) */
    USBOTGHS_IT_GINAKEFF   = 6,    /*< Global IN NAK effective */
    USBOTGHS_IT_GONAKEFF   = 7,    /*< Global OUT NAK effective*/
    USBOTGHS_IT_RESERVED8  = 8,    /*< Reserved */
    USBOTGHS_IT_RESERVED9  = 9,    /*< Reserved */
    USBOTGHS_IT_ESUSP      = 10,   /*< Early suspend */
    USBOTGHS_IT_USBSUSB    = 11,   /*< USB Suspend */
    USBOTGHS_IT_USBRST     = 12,   /*< Reset */
    USBOTGHS_IT_ENUMDNE    = 13,   /*< Speed enumeration done */
    USBOTGHS_IT_ISOODRP    = 14,   /*< Isochronous OUT pkt dropped */
    USBOTGHS_IT_EOPF       = 15,   /*< End of periodic frame */
    USBOTGHS_IT_RESERVED16 = 16,   /*< Reserved */
    USBOTGHS_IT_EPMISM     = 17,   /*< Endpoint mismatch */
    USBOTGHS_IT_IEPINT     = 18,   /*< IN Endpoint event */
    USBOTGHS_IT_OEPINT     = 19,   /*< OUT Endpoint event */
    USBOTGHS_IT_IISOIXFR   = 20,   /*< Incomplete Isochronous IN transfer */
    USBOTGHS_IT_IPXFR      = 21,   /*< Incomplete periodic transfer */
    USBOTGHS_IT_RESERVED22 = 22,   /*< Reserved */
    USBOTGHS_IT_RESERVED23 = 23,   /*< Reserved */
    USBOTGHS_IT_HPRTINT    = 24,   /*< Host port event (Host mode) */
    USBOTGHS_IT_HCINTT     = 25,   /*< Host channels event (Host mode) */
    USBOTGHS_IT_PTXFE      = 26,   /*< Periodic TxFIFO empty (Host mode) */
    USBOTGHS_IT_RESERVED27 = 27,   /*< Reserved */
    USBOTGHS_IT_CIDSCHG    = 28,   /*< Connector ID status change */
    USBOTGHS_IT_DISCINT    = 29,   /*< Disconnect event (Host mode) */
    USBOTGHS_IT_SRQINT     = 30,   /*< Session request/new session event*/
    USBOTGHS_IT_WKUPINT    = 31,   /*< Resume/Wakeup event */
} usbotghs_int_id_t;

/*
 * Generic handler, used by default.
 */
static mbed_error_t default_handler(void)
{
    return MBED_ERROR_NONE;
}

/*
 * Reserved handler, should never be executed, as interrupt flag corresponds to
 * 'Reserved' field.
 */
static mbed_error_t reserved_handler(void)
{
    return MBED_ERROR_UNSUPORTED_CMD;
}

/*
 * USB Reset handler. Handling USB reset requests. These requests can be received in various
 * state and handle a core soft reset and configuration.
 */
static mbed_error_t reset_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    /*
     * activate OEPInt, IEPInt & RxFIFO non-empty.
     * Ready to receive requests on EP0.
     */
	set_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK,
                 USBOTG_HS_GINTMSK_OEPINT_Msk   |
                 USBOTG_HS_GINTMSK_IEPINT_Msk   |
				 USBOTG_HS_GINTMSK_RXFLVLM_Msk);


    return errcode;
}

/*
 * OUT endpoint event (reception in device mode, transmission in Host mode)
 */
static mbed_error_t oepint_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

/*
 * IN endpoint event (transmission in device mode, reception in Host mode)
 */
static mbed_error_t iepint_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

static mbed_error_t rxflvl_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}


/*
 * Start-offrame event (new USB frame)
 */
static mbed_error_t sof_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

static mbed_error_t otg_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

static mbed_error_t mmism_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

static mbed_error_t enumdone_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}


static mbed_error_t esuspend_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

static mbed_error_t ususpend_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}




/************************************************
 * About ISR handlers global table
 */
typedef mbed_error_t (*usb_otg_hs_isr_handler_t)(void);

/*
 * This table handle the overall possible ISR handlers, ordered by their bit identifier in the
 * INTSTS and GINTMSK registers
 */
static const usb_otg_hs_isr_handler_t usb_otg_hs_isr_handlers[32] = {
    default_handler,    /*< Current Mode of Operation  */
    mmism_handler,      /*< Mode mismatch */
    otg_handler,        /*< OTG interrupt */
    sof_handler,        /*< Start of Frame */
    rxflvl_handler,     /*< RxFifo non-empty */
    default_handler,    /*< Non-periodic TxFIFO empty (Host mode) */
    default_handler,    /*< Global IN NAK effective */
    default_handler,    /*< Global OUT NAK effective*/
    reserved_handler,   /*< Reserved */
    reserved_handler,   /*< Reserved */
    esuspend_handler,   /*< Early suspend */
    ususpend_handler,   /*< USB Suspend */
    reset_handler,      /*< Reset */
    enumdone_handler,   /*< Speed enumeration done */
    default_handler,    /*< Isochronous OUT pkt dropped */
    default_handler,    /*< End of periodic frame */
    default_handler,    /*< Reserved */
    default_handler,    /*< Endpoint mismatch */
    iepint_handler,     /*< IN Endpoint event */
    oepint_handler,     /*< OUT Endpoint event */
    default_handler,    /*< Incomplete Isochronous IN transfer */
    default_handler,    /*< Incomplete periodic transfer */
    reserved_handler,   /*< Reserved */
    reserved_handler,   /*< Reserved */
    default_handler,    /*< Host port event (Host mode) */
    default_handler,    /*< Host channels event (Host mode) */
    default_handler,    /*< Periodic TxFIFO empty (Host mode) */
    reserved_handler,   /*< Reserved */
    default_handler,    /*< Connector ID status change */
    default_handler,    /*< Disconnect event (Host mode) */
    default_handler,    /*< Session request/new session event*/
    default_handler,    /*< Resume/Wakeup event */
};

/************************************************
 * About ISR dispatchers
 */
void USBOTGHS_IRQHandler(uint8_t interrupt __attribute__((unused)),
                         uint32_t sr,
                         uint32_t dr)
{
	uint8_t i;
	uint32_t intsts = sr;
	uint32_t intmsk = dr;

	if (intsts & USBOTG_HS_GINTSTS_CMOD_Msk){
		log_printf("[USB HS] Int in Host mode !\n");
	}
    uint32_t val = intsts;
    val &= intmsk;

    /*
     * Here, for each status flag active, execute the corresponding handler if
     * the global interrupt mask is also enabled
     */
	for (i = 0; val; i++,val>>=1) {
		/* Below code is equivalent to
         * calculating (!(intsts & ((uint32_t)1 << i)) || !(intmsk & ((uint32_t)1 << i)))
         */
        if (val & 1)
        {
            usb_otg_hs_isr_handlers[i]();
        }
    }
}

