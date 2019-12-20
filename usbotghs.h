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
    USBOTG_HS_EP_STATE_IDLE  = 0,
    USBOTG_HS_EP_STATE_SETUP = 1,
    USBOTG_HS_EP_STATE_STATUS = 2,
    USBOTG_HS_EP_STATE_STALL = 3,
    USBOTG_HS_EP_STATE_DATA_IN = 4,
    USBOTG_HS_EP_STATE_DATA_OUT = 5,
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

#define USBOTGHS_MAX_IN_EP   8
#define USBOTGHS_MAX_OUT_EP  3

/* current context of the USB OTG HS Core */
typedef struct {
    device_t            dev;             /* associated device_t structure */
    int                 dev_desc;        /* device descriptor */
    usbotghs_dev_mode_t mode;            /* current OTG mode (host or device) */
    bool                gonak_req;       /* global OUT NAK requested */
    bool                gonak_active;    /* global OUT NAK effective */
    usbotghs_ep_t       in_eps[USBOTGHS_MAX_IN_EP];       /* list of HW supported IN EPs */
    usbotghs_ep_t       out_eps[USBOTGHS_MAX_OUT_EP];      /* list of HW supported OUT EPs */
} usbotghs_context_t;

usbotghs_context_t *usbotghs_get_context(void);

#endif /*!USBOTGHS_H_ */
