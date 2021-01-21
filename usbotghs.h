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

#ifndef USBOTGHS_H_
# define USBOTGHS_H_

#include "autoconf.h"

#include "libc/regutils.h"
#include "libc/types.h"
#include "libc/stdio.h"

#include "api/libusbotghs.h"
#include "usbotghs_regs.h"

#define USBOTGHS_REG_CHECK_TIMEOUT 50

#define MAX_TIME_DETACH     4000

#define USB_GLOBAL_OUT_NAK        0b0001 /* Global OUT NAK (triggers an interrupt) */
#define USB_OUT_PACKET_RECEIVED   0b0010 /* OUT data packet received */
#define USB_OUT_TRANSFERT_COMPLETED   0b0011 /* OUT transfer completed (triggers an interrupt) */
#define USB_SETUP_TRANS_COMPLETED 0b0100 /* SETUP transaction completed (triggers an interrupt) */
#define USB_SETUP_PACKET_RECEIVED 0b0110 /* SETUP data packet received */

#ifndef __FRAMAC__

#define USBOTGHS_MAX_IN_EP   6 /* EP0 + 5 IN EPs */
#define USBOTGHS_MAX_OUT_EP  6 /* EP0 + 5 OUT EPs */

#define MAX_EP_HW 4

#else
/***************************************************************
 * FramaC: private: about registers
 */

# define r_CORTEX_M_USBOTG_HS_DIEPCTL(EP)    REG_ADDR(USB_OTG_HS_BASE + 0x900 + ((EP) * 0x20))
# define r_CORTEX_M_USBOTG_HS_DOEPCTL(EP)    REG_ADDR(USB_OTG_HS_BASE + 0xb00 + ((EP) * 0x20))

/* private predicates */

#endif

#define CPT_HARD 100

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

typedef enum {
    USBOTG_HS_SPEED_LS = 0, /* aka Low speed (USB 1.0) */
    USBOTG_HS_SPEED_FS = 1, /* aka Full Speed (USB 1.1) */
    USBOTG_HS_SPEED_HS = 2, /* aka High speed (USB 2.0) */
} usbotghs_speed_t;

/*
 * local context hold by the driver
 */
typedef struct {
    uint8_t                      id;           /* EP id (libusbctrl view) */
    bool                         configured;   /* is EP configured in current configuration ? */
    uint16_t                     mpsize;       /* max packet size (bitfield, 11 bits, in bytes) */
    uint8_t                      type;         /* EP type */
    uint8_t             state;        /* EP current state */
    usbotghs_ep_dir_t   dir;
    usbotghs_ioep_handler_t      handler;      /* EP Handler for (I|O)EPEVENT */

    uint8_t            *fifo;         /* associated RAM FIFO (recv) */
    uint32_t            fifo_idx;     /* current FIFO index  (recv) */
    uint32_t            fifo_size;    /* associated RAM FIFO max size (recv) */
    bool                fifo_lck;     /* DMA, locking mechanism (recv) */
    bool                core_txfifo_empty; /* core TxFIFO (Half) empty */
} usbotghs_ep_t;

typedef struct {
    device_t            dev;             /* associated device_t structure */
    int                 dev_desc;        /* device descriptor */
    usbotghs_dev_mode_t mode;            /* current OTG mode (host or device) */
    bool                gonak_req;       /* global OUT NAK requested */
    bool                gonak_active;    /* global OUT NAK effective */
    uint16_t            fifo_idx;        /* consumed Core FIFO */
    usbotghs_ep_t       in_eps[USBOTGHS_MAX_IN_EP];       /* list of HW supported IN EPs */
    usbotghs_ep_t       out_eps[USBOTGHS_MAX_OUT_EP];      /* list of HW supported OUT EPs */
    uint8_t             speed;        /* device enumerated speed, default HS */
} usbotghs_context_t;

#ifdef __FRAMAC__
/* export to framaC entrypoint */
usbotghs_context_t usbotghs_ctx = { 0 };
#endif/*!__FRAMAC__*/


usbotghs_context_t *usbotghs_get_context(void);


#endif /*!USBOTGHS_H_ */
