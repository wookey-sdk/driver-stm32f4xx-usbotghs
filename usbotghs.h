/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
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

#ifndef USBOTGHS_H_
# define USBOTGHS_H_

#include "autoconf.h"

#include "libc/regutils.h"
#include "libc/types.h"

#include "api/libusbotghs.h"
#include "usbotghs_regs.h"

#define USBOTGHS_REG_CHECK_TIMEOUT 50

#define MAX_TIME_DETACH     4000

#define USB_GLOBAL_OUT_NAK        0b0001 /* Global OUT NAK (triggers an interrupt) */
#define USB_OUT_PACKET_RECEIVED   0b0010 /* OUT data packet received */
#define USB_OUT_TRANSFERT_COMPLETED   0b0011 /* OUT transfer completed (triggers an interrupt) */
#define USB_SETUP_TRANS_COMPLETED 0b0100 /* SETUP transaction completed (triggers an interrupt) */
#define USB_SETUP_PACKET_RECEIVED 0b0110 /* SETUP data packet received */


/*********************************************************
 * General tooling
 */

#if CONFIG_USR_DRV_USBOTGHS_DEBUG
# define log_printf(...) printf(__VA_ARGS__)
#else
# define log_printf(...)
#endif

/********************************************************
 * Driver private structures and types
 */

/* setup packet, to be passed to upper libctrl */

typedef enum {
    USB_EP_STATE_IDLE  = 0,
    USB_EP_STATE_SETUP = 1,
    USB_EP_STATE_STATUS = 2,
    USB_EP_STATE_STALL = 3,
    USB_EP_STATE_DATA_IN = 4,
    USB_EP_STATE_DATA_OUT = 5,
} usbotghs_ep_state_t;

/*
 * local context hold by the driver
 */
typedef struct {
    uint8_t             id;            /* EP id (libusbctrl view) */
    bool                configured;    /* is EP configured in current configuration ? */
    uint16_t            mpsize;        /* max packet size (bitfield, 11 bits, in bytes) */
    usbotghs_ep_type_t  type;          /* EP type */
    usbotghs_ep_state_t state;         /* EP current state */

    physaddr_t          *fifo;         /* associated RAM FIFO */
    uint32_t             fifo_idx;     /* current FIFO index */
    uint32_t             fifo_size;    /* associated RAM FIFO */
} usbotghs_ep_t;


/* current context of the USB OTG HS Core */
typedef struct {
    uint8_t             id;              /* device unique identifier, from generated header */
    device_t            dev;             /* associated device_t structure */
    int                 dev_desc;        /* device descriptor */
    usbotghs_dev_mode_t mode;            /* current OTG mode (host or device) */
    usbotghs_ep_t       in_eps[8];       /* list of HW supported IN EPs */
    usbotghs_ep_t       out_eps[3];      /* list of HW supported OUT EPs */
    setup_pkt_handler_t setup_handler;   /* setup and events handler */
    data_pkt_handler_t  data_handler;    /* data (non-control) handler */
} usbotghs_context_t;


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

#endif /*!USBOTGHS_H_ */
