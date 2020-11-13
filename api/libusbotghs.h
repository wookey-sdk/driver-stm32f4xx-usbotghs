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
#ifndef LIBUSBOTGHS_H_
#define LIBUSBOTGHS_H_

#include "libc/types.h"
#include "autoconf.h"


#define MAX_DATA_PACKET_SIZE(ep) (((ep) == 0) ? 64 : 512)


typedef mbed_error_t (*usbotghs_ioep_handler_t)(uint32_t dev_id, uint32_t size, uint8_t ep);

typedef enum {
    USBOTG_HS_PORT_LOWSPEED = 0,
    USBOTG_HS_PORT_FULLSPEED = 1,
    USBOTG_HS_PORT_HIGHSPEED = 2
} usbotghs_port_speed_t;

/*
 * The USB OTG support On-The-Go configuration (i.e. Host or Device mode, configurable
 * by software stack. This enumerate define which mode to use
 */
typedef enum {
    USBOTGHS_MODE_HOST = 0,
    USBOTGHS_MODE_DEVICE = 1
} usbotghs_dev_mode_t;

/*
 * Device Endpoint identifiers
 */
typedef enum {
    USBOTG_HS_EP0 = 0,
    USBOTG_HS_EP1 = 1,
    USBOTG_HS_EP2 = 2,
    USBOTG_HS_EP3 = 3,
    USBOTG_HS_EP4 = 4,
    USBOTG_HS_EP5 = 5,
    USBOTG_HS_EP6 = 6,
    USBOTG_HS_EP7 = 7,
} usbotghs_ep_nb_t;

/*
 * Max packet size in EP0 is a specific field.
 * Here are the supported size
 */
typedef enum {
    USBOTG_HS_EP0_MPSIZE_64BYTES = 0,
    USBOTG_HS_EP0_MPSIZE_32BYTES = 1,
    USBOTG_HS_EP0_MPSIZE_16BYTES = 2,
    USBOTG_HS_EP0_MPSIZE_8BYTES  = 3,
} usbotghs_ep0_mpsize_t;


/*
 * Other EPs support various sizes for their
 * max packet size. Although, we limit these size to
 * various standard sizes.
 */
typedef enum {
    USBOTG_HS_EPx_MPSIZE_64BYTES = 64,
    USBOTG_HS_EPx_MPSIZE_128BYTES = 128,
    USBOTG_HS_EPx_MPSIZE_512BYTES = 512,
    USBOTG_HS_EPx_MPSIZE_1024BYTES  = 1024,
} usbotghs_epx_mpsize_t;

typedef enum {
    USB_HS_DXEPCTL_SD0PID_SEVNFRM  = 0,
    USB_HS_DXEPCTL_SD1PID_SODDFRM
} usbotghs_ep_toggle_t;

/*
 * USB standard EP type
 */
typedef enum {
    USBOTG_HS_EP_TYPE_CONTROL     = 0,
    USBOTG_HS_EP_TYPE_ISOCHRONOUS = 1,
    USBOTG_HS_EP_TYPE_BULK        = 2,
    USBOTG_HS_EP_TYPE_INT         = 3,
} usbotghs_ep_type_t;

/*
 * Global device state, depending on currently send/received data.
 * This flags are (mostly) set by rxflvl handler and can be read back
 * at oepint/iepint time to be informed of which data type is currently
 * waiting for treatment (reception case) or has been sent (transmission
 * case). The driver reset the current flag to IDLE automatically when the
 * data has be treated in iepint/oepint end of function.
 */
typedef enum {
    USBOTG_HS_EP_STATE_IDLE  = 0,
    USBOTG_HS_EP_STATE_SETUP_WIP = 1,
    USBOTG_HS_EP_STATE_SETUP = 2,
    USBOTG_HS_EP_STATE_STATUS = 3,
    USBOTG_HS_EP_STATE_STALL = 4,
    USBOTG_HS_EP_STATE_DATA_IN_WIP = 5,
    USBOTG_HS_EP_STATE_DATA_IN = 6,
    USBOTG_HS_EP_STATE_DATA_OUT_WIP = 7,
    USBOTG_HS_EP_STATE_DATA_OUT = 8,
    USBOTG_HS_EP_STATE_INVALID = 9,
} usbotghs_ep_state_t;

typedef enum {
    USBOTG_HS_EP_DIR_IN,
    USBOTG_HS_EP_DIR_OUT,
    USBOTG_HS_EP_DIR_BOTH,
} usbotghs_ep_dir_t;


/*********************************************************************************
 * About handlers
 *
 * The Control plane must declare some handlers for various events (see usbotghs_handlers.c
 * for more informations). These handlers are called on these events in order to execute
 * control level (or potentially upper level(s)) programs. They can use the USB OTG HS
 * driver API during their execution.
 *
 * Control level handlers are linked directly through their prototype definition here.
 *
 * We prefer to use prototype and link time symbol resolution instead of callbacks as:
 *   1. The USB control plane is not an hotpluggable element
 *   2. callbacks have security impacts, as they can be corrupted, generating arbitrary
 *      code execution
 *
 *  WARNING: as we use prototypes (and not callbacks), these functions *must* exists at
 *  link time, for symbol resolution.
 *  It has been decided that the driver doesn't hold weak symbols for these functions,
 *  as their absence would make the USB stack unfonctional.
 *  If one of these function is not set in the control plane (or in any element of the
 *  application to be linked) it would generate a link time error, corresponding to a
 *  missing symbol.
 *
 */

mbed_error_t usbctrl_handle_earlysuspend(uint32_t dev_id);
mbed_error_t usbctrl_handle_reset(uint32_t dev_id);
mbed_error_t usbctrl_handle_usbsuspend(uint32_t dev_id);
mbed_error_t usbctrl_handle_inepevent(uint32_t dev_id, uint32_t size, uint8_t ep);
mbed_error_t usbctrl_handle_outepevent(uint32_t dev_id, uint32_t size, uint8_t ep);
mbed_error_t usbctrl_handle_wakeup(uint32_t dev_id);

#ifdef __FRAMAC__
/********************************************************************************
 * About FramaC exported content
 * This header contains private structures and globals that are only exported here
 * for FramaC use case, in order to allow the usage of ACSL annotations below.
 * In nomincal (non-FramaC) case, this header is empty, private content is pushed
 * back into private files.
 */
#include "libusbotghs_framac.h"

#endif


/********************************************************************************
 * About functional API
 *
 * This is the USB OTG HS functional API. The goal is to abstract as much as
 * possible all device-specific content and to declare a protocol orented API.
 *
 * Nevertheless, all control plane (requests, events) must be handled by the USB
 * control stack, not the driver itself.
 * As a consequence, the following API is made in order to be controlled by an
 * external USB 2.0 control stack.
 */

/*
 * Declaring the device against EwoK
 */
/*@
  @ requires \separated(&usbotghs_ctx);
  @ assigns usbotghs_ctx.dev ;
  @ ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_UNKNOWN ;
  */
mbed_error_t usbotghs_declare(void);

/*
 * Core initial setup and config. At the end of the initialization, the Core should
 * have its USB control pipe ready to receive the first requests from the host.
 */
/*@
  @ requires is_valid_dev_mode(mode) ;
  @ assigns usbotghs_ctx \from indirect:ieph, indirect:oeph;
  @ assigns usbotghs_ctx ;
  @ ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVPARAM || \result == MBED_ERROR_INITFAIL
  || \result == MBED_ERROR_BUSY || \result == MBED_ERROR_UNSUPORTED_CMD || \result == MBED_ERROR_NOMEM ;
  */
/*
FIXME : @ requires \separated(&usbotghs_ctx,\union(ieph+(..),oeph+(..)));
to add for framac messages, but :
expecting a pointer to an object, found set<mbed_error_t (*)(uint32_t dev_id, uint32_t size, uint8_t ep)
*/
mbed_error_t usbotghs_configure(usbotghs_dev_mode_t mode,
                                usbotghs_ioep_handler_t ieph,
                                usbotghs_ioep_handler_t oeph);

/*
 * Sending data (whatever data type is (i.e. status on control pipe or data on
 * data (Bulk, IT or isochronous) pipe)
 * This is not a syncrhonous request, i.e. data are stored into the USB OTG HS
 * interanal FIFO, waiting for bus transmission. When data are fully transmitted,
 * a iepint (device mode) or oepint (host mode) is triggered to inform the upper
 * layer that the content has been sent. Although, it is possible to push some
 * other data in the internal FIFO if needed, while this FIFO is not full
 * (check for this function return value)
 *
 * @src the RAM FIFO from which the data are read
 * @size the amount of data bytes to send
 * @ep the endpoint on which the data are to be sent
 *
 * @return MBED_ERROR_NONE if data has been correctly transmitted into the internal
 * core FIFO, or MBED_ERROR_BUSY if the interal core FIFO for the given EP is full
 */
/*@
    @ requires \valid(src);
    @ requires \separated(src,&usbotghs_ctx, (uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END));
    @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.in_eps[ep_id];
    @ assigns \result \from ep_id, src, size;

    @ behavior bad_ctx:
    @   assumes &usbotghs_ctx == \null ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior bad_ep:
    @   assumes &usbotghs_ctx != \null ;
    @   assumes (ep_id >= USBOTGHS_MAX_IN_EP || ep_id >= MAX_EP_HW) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior not_configured:
    @   assumes &usbotghs_ctx != \null ;
    @   assumes !(ep_id >= USBOTGHS_MAX_IN_EP || ep_id >= MAX_EP_HW) ;
    @   assumes ((usbotghs_ctx.in_eps[ep_id].configured == \false) || (usbotghs_ctx.in_eps[ep_id].mpsize == 0));
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior configured:
    @   assumes &usbotghs_ctx != \null ;
    @   assumes !(ep_id >= USBOTGHS_MAX_IN_EP || ep_id >= MAX_EP_HW) ;
    @   assumes !((usbotghs_ctx.in_eps[ep_id].configured == \false) || (usbotghs_ctx.in_eps[ep_id].mpsize == 0));
    @   ensures \result == MBED_ERROR_INVPARAM || \result == MBED_ERROR_BUSY || \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

mbed_error_t usbotghs_send_data(uint8_t *src, uint32_t size, uint8_t ep_id);

/*
 * Configure for receiving data. Receiving data is a triggering event, not a direct call.
 * As a consequence, the upper layers have to specify the amount of data requested for
 * the next USB transaction on the given OUT (device mode) or IN (host mode) enpoint.
 *
 * @dst is the destination buffer that will be used to hold  @size amount of data bytes
 * @size is the amount of data bytes to load before await the upper stack
 * @ep is the active endpoint on which this action is done
 *
 * On data reception:
 * - if there is enough data loaded in the output buffer, the upper stack is awoken
 * - If not, data is silently stored in FIFO RAM (targetted by dst), and the driver waits
 *   for the next content while 'size' amount of data is not reached
 *
 * @return MBED_ERROR_NONE if setup is ok, or various possible other errors (INVSTATE
 * for invalid enpoint type, INVPARAM if dst is NULL or size invalid)
 */
/*
    //@ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.out_eps[epid];

    //@   ensures \result == MBED_ERROR_INVPARAM
    <==> ((usbotghs_ctx.out_eps[epid].configured == \false) || (usbotghs_ctx.out_eps[epid].mpsize == 0))
     || (!((usbotghs_ctx.out_eps[epid].configured == \false) || (usbotghs_ctx.out_eps[epid].mpsize == 0)) && size == 0) ;

    //@   ensures \result == MBED_ERROR_NONE
    ==> (usbotghs_ctx.out_eps[epid].configured == \true && usbotghs_ctx.out_eps[epid].mpsize != 0 && size != 0) ;

*/

/*@
  @ requires \separated(&usbotghs_ctx, ((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), dst + (0..size-1));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.out_eps[epid];

  @ behavior invdst:
  @    assumes dst == NULL;
  @    ensures usbotghs_ctx.out_eps[epid] == \old(usbotghs_ctx.out_eps[epid]);
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior badepid:
  @    assumes \valid(dst);
  @    assumes epid >= USBOTGHS_MAX_OUT_EP;
  @    ensures \result == MBED_ERROR_INVPARAM;
  @    ensures usbotghs_ctx.out_eps[epid] == \old(usbotghs_ctx.out_eps[epid]);

  @ behavior epnotconfigured:
  @    assumes \valid(dst);
  @    assumes epid < USBOTGHS_MAX_OUT_EP;
  @    assumes (usbotghs_ctx.out_eps[epid].configured == \false || usbotghs_ctx.out_eps[epid].mpsize == 0);
  @    ensures usbotghs_ctx.out_eps[epid] == \old(usbotghs_ctx.out_eps[epid]);
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior badsize:
  @    assumes \valid(dst);
  @    assumes epid < USBOTGHS_MAX_OUT_EP;
  @    assumes (usbotghs_ctx.out_eps[epid].configured == \true && usbotghs_ctx.out_eps[epid].mpsize > 0);
  @    assumes size == 0;
  @    ensures usbotghs_ctx.out_eps[epid] == \old(usbotghs_ctx.out_eps[epid]);
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior epfifolocked:
  @    assumes \valid(dst);
  @    assumes epid < USBOTGHS_MAX_OUT_EP;
  @    assumes (usbotghs_ctx.out_eps[epid].configured == \true && usbotghs_ctx.out_eps[epid].mpsize > 0);
  @    assumes size > 0;
  @    assumes usbotghs_ctx.out_eps[epid].fifo_lck == \true;
  @    ensures usbotghs_ctx.out_eps[epid] == \old(usbotghs_ctx.out_eps[epid]);
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes \valid(dst);
  @    assumes epid < USBOTGHS_MAX_OUT_EP;
  @    assumes (usbotghs_ctx.out_eps[epid].configured == \true && usbotghs_ctx.out_eps[epid].mpsize > 0);
  @    assumes size > 0;
  @    assumes usbotghs_ctx.out_eps[epid].fifo_lck == \false;
  @    ensures \result == MBED_ERROR_NONE;

  @ complete behaviors;
  @ disjoint behaviors;

  */
mbed_error_t usbotghs_set_recv_fifo(uint8_t *dst, uint32_t size, uint8_t epid);

/*
 * Send a special zero-length packet on EP ep
 */
 /*@
   @ requires \separated(((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), &usbotghs_ctx);
   @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
   @ assigns \result \from ep_id;
   @ ensures (CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE && ep_id >= USBOTGHS_MAX_IN_EP) ==> \result == MBED_ERROR_INVPARAM ;
   @ ensures (!CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE && ep_id >= USBOTGHS_MAX_OUT_EP) ==> \result == MBED_ERROR_INVPARAM ;
   @ ensures (CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE && ep_id < USBOTGHS_MAX_IN_EP && usbotghs_ctx.in_eps[ep_id].configured == \false)
   <==> \result == MBED_ERROR_INVSTATE ;
   @ ensures (!CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE && ep_id < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep_id].configured == \false)
   ==> \result == MBED_ERROR_INVSTATE ;
   @ ensures (CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE && ep_id < USBOTGHS_MAX_IN_EP && usbotghs_ctx.in_eps[ep_id].configured == \true)
   <==> \result == MBED_ERROR_BUSY || \result == MBED_ERROR_NONE ;
   @ ensures (!CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE && ep_id < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep_id].configured == \true)
   ==> \result == MBED_ERROR_BUSY || \result == MBED_ERROR_NONE ;
   */
/*
  spec ok with CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE == 1
  TODO : <==> to be prooved with CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE == 0
*/
mbed_error_t usbotghs_send_zlp(uint8_t ep_id);

/*
 * Activate the configuration global stall mode. If any EP has its stall mode configured,
 * it can override the global stall mode
 * INFO: stall mode for Control and data EP don't have the same meaning. See datasheet,
 * chap 35.13.7
 */
mbed_error_t usbotghs_global_stall(void);

/*
 * Clear the global stall mode.
 */
mbed_error_t usbotghs_global_stall_clear(void);

/*
 * Set the STALL mode for the given EP
 */
/*@
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
  @ ensures (&usbotghs_ctx == \null) ==> (\result == MBED_ERROR_INVSTATE) ;
  @ ensures ((&usbotghs_ctx == \null) && (dir == USBOTG_HS_EP_DIR_IN )) ==>
  (\result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_INVPARAM || \result == MBED_ERROR_NONE ||  \result == MBED_ERROR_BUSY ) ;
  @ ensures ((&usbotghs_ctx == \null) && (dir == USBOTG_HS_EP_DIR_OUT )) ==>
  (\result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_INVPARAM || \result == MBED_ERROR_NONE ||  \result == MBED_ERROR_BUSY ) ;
  @ ensures ((&usbotghs_ctx == \null) && (dir != USBOTG_HS_EP_DIR_OUT ) && (dir != USBOTG_HS_EP_DIR_IN ) ) ==> (\result == MBED_ERROR_INVPARAM) ;
  */
mbed_error_t usbotghs_endpoint_stall(uint8_t ep_id, usbotghs_ep_dir_t dir);

/*
 * Clear the STALL mode for the given EP
 */
/*@
  @ ensures \result == MBED_ERROR_NONE ;
  @ assigns \nothing ;
  */
mbed_error_t usbotghs_endpoint_stall_clear(uint8_t ep, usbotghs_ep_dir_t dir);

/*@
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
  @ ensures (&usbotghs_ctx == \null) ==> \result == MBED_ERROR_INVSTATE ;
  @ ensures (&usbotghs_ctx != \null) ==> ( \result == MBED_ERROR_INVPARAM ||
  \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_BUSY || \result ==MBED_ERROR_NONE  ) ;
  */
/*
TODO : behavior spec (including __explicit_fallthrough)
*/
mbed_error_t usbotghs_endpoint_set_nak(uint8_t ep_id, usbotghs_ep_dir_t dir);

/*@
  @   requires \separated(&usbotghs_ctx,((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ) ;
  @   assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;

  @ behavior bad_ctx:
  @   assumes &usbotghs_ctx == \null ;
  @   ensures \result == MBED_ERROR_INVSTATE ;

  @ behavior dir_in_bad_epid:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir == USBOTG_HS_EP_DIR_IN ;
  @   assumes ep_id >= USBOTGHS_MAX_IN_EP ;
  @   ensures \result == MBED_ERROR_INVPARAM ;

  @ behavior dir_in_not_configured:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir == USBOTG_HS_EP_DIR_IN ;
  @   assumes ep_id < USBOTGHS_MAX_IN_EP ;
  @   assumes usbotghs_ctx.in_eps[ep_id].configured == \false ;
  @   ensures \result == MBED_ERROR_INVSTATE ;

  @ behavior dir_in_configured_epid_0:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir == USBOTG_HS_EP_DIR_IN ;
  @   assumes ep_id < USBOTGHS_MAX_IN_EP ;
  @   assumes usbotghs_ctx.in_eps[ep_id].configured == \true ;
  @   assumes ep_id == 0 ;
  @   ensures \result == MBED_ERROR_NONE ;

  @ behavior dir_in_out_MBED_ERROR_INVPARAM:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes ((dir == USBOTG_HS_EP_DIR_IN && ep_id < USBOTGHS_MAX_IN_EP && usbotghs_ctx.in_eps[ep_id].configured == \true &&
  ep_id != 0 && ep_id >= USBOTGHS_MAX_OUT_EP) || (dir == USBOTG_HS_EP_DIR_OUT && ep_id >= USBOTGHS_MAX_OUT_EP )) ;
  @   ensures \result == MBED_ERROR_INVPARAM ;

  @ behavior dir_in_out_MBED_ERROR_INVSTATE:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes (dir == USBOTG_HS_EP_DIR_IN && ep_id < USBOTGHS_MAX_IN_EP && usbotghs_ctx.in_eps[ep_id].configured == \true &&
  ep_id != 0 && ep_id < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep_id].configured == \false) ||
  ( dir == USBOTG_HS_EP_DIR_OUT && ep_id < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep_id].configured == \false ) ;
  @   ensures \result == MBED_ERROR_INVSTATE ;

  @ behavior dir_in_out_configured_MBED_ERROR_NONE:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes (dir == USBOTG_HS_EP_DIR_IN && ep_id < USBOTGHS_MAX_IN_EP && usbotghs_ctx.in_eps[ep_id].configured == \true &&
  ep_id != 0 && ep_id < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep_id].configured == \true) ||
  ( dir == USBOTG_HS_EP_DIR_OUT && ep_id < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep_id].configured == \true ) ;
  @   ensures \result == MBED_ERROR_NONE ;

  @ behavior other_dir:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir != USBOTG_HS_EP_DIR_OUT && dir != USBOTG_HS_EP_DIR_IN ;
  @   ensures \result == MBED_ERROR_INVPARAM ;

  @ complete behaviors;
  @ disjoint behaviors;
  */
mbed_error_t usbotghs_endpoint_clear_nak(uint8_t ep_id, usbotghs_ep_dir_t dir);

/*
 * Activate the given EP (for e.g. to transmit data)
 */
/*@
  @ requires \separated(&usbotghs_ctx.out_eps[0..(USBOTGHS_MAX_OUT_EP-1)], &usbotghs_ctx.in_eps[0..(USBOTGHS_MAX_IN_EP-1)],((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.in_eps[0..(USBOTGHS_MAX_IN_EP-1)], usbotghs_ctx, usbotghs_ctx.out_eps[0..(USBOTGHS_MAX_OUT_EP-1)] ;

  @ behavior bad_ctx:
  @   assumes &usbotghs_ctx == \null ;
  @   ensures \result == MBED_ERROR_INVSTATE ;

  @ behavior USBOTG_HS_EP_DIR_IN:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir == USBOTG_HS_EP_DIR_IN ;
  @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_NOSTORAGE ;

  @ behavior USBOTG_HS_EP_DIR_OUT:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir == USBOTG_HS_EP_DIR_OUT ;
  @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_NOSTORAGE ;

  @ behavior default:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir != USBOTG_HS_EP_DIR_OUT && dir != USBOTG_HS_EP_DIR_IN  ;
  @   ensures \result == MBED_ERROR_NONE ;

  @ complete behaviors ;
  @ disjoint behaviors ;
  */
/*
TODO : be more precise with behavior based on ep number
*/
mbed_error_t usbotghs_configure_endpoint(uint8_t               ep,
                                         usbotghs_ep_type_t    type,
                                         usbotghs_ep_dir_t     dir,
                                         usbotghs_epx_mpsize_t mpsize,
                                         usbotghs_ep_toggle_t  dtoggle,
                                         usbotghs_ioep_handler_t handler);

/*
 * Deactivate the given EP (Its configuration is keeped, the EP is *not* deconfigured)
 */
/*@
  @ requires \separated(&usbotghs_ctx.out_eps[0..(USBOTGHS_MAX_OUT_EP-1)], &usbotghs_ctx.in_eps[0..(USBOTGHS_MAX_IN_EP-1)],((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.in_eps[0..(USBOTGHS_MAX_IN_EP-1)], usbotghs_ctx, usbotghs_ctx.out_eps[0..(USBOTGHS_MAX_OUT_EP-1)] ;
  */
mbed_error_t usbotghs_deconfigure_endpoint(uint8_t ep);

/*
 * Configure the given EP in order to be ready to work
 */
/*@
  @  assigns *(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id)) ;
  @  assigns *(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id)) ;

  @ behavior badctx:
  @    assumes &usbotghs_ctx == \null ;
  @    ensures r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id) == \old(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id)) ;
  @    ensures r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id) == \old(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id)) ;
  @    ensures \result == MBED_ERROR_INVSTATE ;


  @ behavior dir_in_bad_ep_id:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir == USBOTG_HS_EP_DIR_IN ;
  @   assumes ep_id >= USBOTGHS_MAX_IN_EP ;
  @   ensures \result == MBED_ERROR_INVPARAM ;

  @ behavior dir_out_bad_ep_id:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir == USBOTG_HS_EP_DIR_OUT ;
  @   assumes ep_id >= USBOTGHS_MAX_OUT_EP ;
  @   ensures \result == MBED_ERROR_INVPARAM ;

  @ behavior other_dir:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir != USBOTG_HS_EP_DIR_OUT && dir != USBOTG_HS_EP_DIR_IN ;
  @   ensures \result == MBED_ERROR_INVPARAM ;

  @ behavior dir_in_ok:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir == USBOTG_HS_EP_DIR_IN ;
  @   assumes ep_id < USBOTGHS_MAX_IN_EP ;
  @   ensures \result == MBED_ERROR_NONE ;

  @ behavior dir_out_ok:
  @   assumes &usbotghs_ctx != \null ;
  @   assumes dir == USBOTG_HS_EP_DIR_OUT ;
  @   assumes ep_id < USBOTGHS_MAX_OUT_EP ;
  @   ensures \result == MBED_ERROR_NONE ;


  @ complete behaviors;
  @ disjoint behaviors;
  @*/
mbed_error_t usbotghs_activate_endpoint(uint8_t               ep_id,
                                        usbotghs_ep_dir_t     dir);

/*
 * Deconfigure the given EP. The EP is no more usable after this call. A new configuration
 * of the EP must be done before reuse it.
 * This function is typically used on SetConfiguration Requests schedule, or on
 * Reset frame reception to reconfigure the Core in a known clear state.
 */
mbed_error_t usbotghs_deactivate_endpoint(uint8_t ep,
                                          usbotghs_ep_dir_t     dir);

/*
 * Temporarily disable Endpoint (Endpoint is not deconfigured but neither emit
 * nor receive data (including IN Token or OUT handshakes)
 */
mbed_error_t usbotghs_endpoint_disable(uint8_t ep,
                                       usbotghs_ep_dir_t     dir);



/*
 * Reenable Endpoint previously disabled
 */
mbed_error_t usbotghs_endpoint_enable(uint8_t ep,
                                      usbotghs_ep_dir_t     dir);

/**
 * usb_driver_set_address - Set the address of the device
 * @addr: Device's address
 */
/*@
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
  */
void usbotghs_set_address(uint16_t addr);

/* Map USB device. TODO */
void usbotghs_bind(void);

void usbotghs_unbind(void);

/*@

  @  assigns \nothing ;

  @ behavior DIR_IN_EPNUM_BIG:
  @   assumes (dir == USBOTG_HS_EP_DIR_IN && epnum >= USBOTGHS_MAX_IN_EP);
  @   ensures \result == USBOTG_HS_EP_STATE_INVALID ;

  @ behavior DIR_OUT_EPNUM_BIG:
  @   assumes (dir == USBOTG_HS_EP_DIR_OUT && epnum >= USBOTGHS_MAX_OUT_EP);
  @   ensures \result == USBOTG_HS_EP_STATE_INVALID ;

  @ behavior DIR_IN:
  @   assumes dir == USBOTG_HS_EP_DIR_IN ;
  @   assumes epnum < USBOTGHS_MAX_IN_EP ;
  @   ensures \result == usbotghs_ctx.in_eps[epnum].state ;

  @ behavior DIR_OUT:
  @   assumes dir == USBOTG_HS_EP_DIR_OUT ;
  @   assumes epnum < USBOTGHS_MAX_OUT_EP ;
  @   ensures \result == usbotghs_ctx.out_eps[epnum].state ;

  @ behavior other_dir:
  @   assumes (dir != USBOTG_HS_EP_DIR_OUT && dir != USBOTG_HS_EP_DIR_IN) ;
  @   ensures \result == USBOTG_HS_EP_STATE_INVALID ;

  @ complete behaviors ;
  @ disjoint behaviors ;

*/
usbotghs_ep_state_t usbotghs_get_ep_state(uint8_t epnum, usbotghs_ep_dir_t dir);

uint16_t usbotghs_get_ep_mpsize(void);

/*@
  @ assigns \nothing ;
  @ ensures \result == USBOTG_HS_PORT_HIGHSPEED ;
  */
usbotghs_port_speed_t usbotghs_get_speed(void);

#if defined(__FRAMAC__)
/*Cyril : these 2 functions are called by test_fcn_driver_eva, so i need to declare their proto somewhere */
mbed_error_t usbotghs_enpoint_nak(uint8_t ep) ;
mbed_error_t usbotghs_enpoint_nak_clear(uint8_t ep) ;
#endif/*__FRAMAC__*/


#endif /*!LIBUSBOTGHS_H_ */
