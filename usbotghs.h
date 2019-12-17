#ifndef USBOTGHS_H_
# define USBOTGHS_H_

#include "autoconf.h"

#include "libc/regutils.h"
#include "libc/types.h"

#include "api/libusbotghs.h"
#include "usbotghs_regs.h"

#define MAX_TIME_DETACH     4000

#define USB_GLOBAL_OUT_NAK        0b0001 /* Global OUT NAK (triggers an interrupt) */
#define USB_OUT_PACKET_RECEIVED   0b0010 /* OUT data packet received */
#define USB_OUT_TRANSFERT_COMPLETED   0b0011 /* OUT transfer completed (triggers an interrupt) */
#define USB_SETUP_TRANS_COMPLETED 0b0100 /* SETUP transaction completed (triggers an interrupt) */
#define USB_SETUP_PACKET_RECEIVED 0b0110 /* SETUP data packet received */


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
    uint32_t             fifo_size;    /* associated RAM FIFO */
} usbotghs_ep_t;


/* current context of the USB OTG HS Core */
typedef struct {
    uint8_t       id;              /* device unique identifier, from generated header */
    device_t      dev;             /* associated device_t structure */
    int           dev_desc;        /* device descriptor */
    usbotghs_ep_t in_eps[8];       /* list of HW supported IN EPs */
    usbotghs_ep_t out_eps[3];      /* list of HW supported OUT EPs */
} usbotghs_context_t;


#endif /*!USBOTGHS_H_ */
