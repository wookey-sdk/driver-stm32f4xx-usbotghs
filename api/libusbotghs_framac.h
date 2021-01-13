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
#ifndef LIBUSBOTGHS_FRAMAC_H_
#define LIBUSBOTGHS_FRAMAC_H_

#ifdef __FRAMAC__

#include "generated/usb_otg_hs.h"
#include "libc/regutils.h"

/******************************************************************
 * About FramaC dedicated predicates
 */

/*@
    predicate is_valid_dev_mode(usbotghs_dev_mode_t i) =
        i == USBOTGHS_MODE_HOST || i == USBOTGHS_MODE_DEVICE ;
*/

/*@ predicate is_valid_ep_dir(usbotghs_ep_dir_t i) =
    i == USBOTG_HS_EP_DIR_IN || i == USBOTG_HS_EP_DIR_OUT;
*/


#define USBOTGHS_MAX_IN_EP   6 /* EP0 + 5 IN EPs */
#define USBOTGHS_MAX_OUT_EP  6 /* EP0 + 5 OUT EPs */

/* is the following useless ?*/
#define MAX_EP_HW 6


/*
 * Size of the USB OTG HS core internal FIFO (global config, not per EP)
 */
#define USBOTG_HS_RX_CORE_FIFO_SZ 512 /* 128 bytes, unit is 32bits DWORD here */
#define USBOTG_HS_TX_CORE_FIFO_SZ 512 /* 128 bytes, unit is 32bits DWORD here */


//@ ghost uint32_t GHOST_nopublicvar = 0;


/*@ predicate is_valid_ep_state(usbotghs_ep_state_t s) =
  s == USBOTG_HS_EP_STATE_IDLE ||
  s == USBOTG_HS_EP_STATE_SETUP_WIP ||
  s == USBOTG_HS_EP_STATE_SETUP ||
  s == USBOTG_HS_EP_STATE_STATUS ||
  s == USBOTG_HS_EP_STATE_STALL ||
  s == USBOTG_HS_EP_STATE_DATA_IN_WIP ||
  s == USBOTG_HS_EP_STATE_DATA_IN ||
  s == USBOTG_HS_EP_STATE_DATA_OUT_WIP ||
  s == USBOTG_HS_EP_STATE_DATA_OUT ||
  s == USBOTG_HS_EP_STATE_INVALID;
*/

struct ep_public_info_t {
    usbotghs_ep_state_t state;
};

/* Logic states of all IN and OUT endpoints. Kept synchronous with driver internal state handling */
/*@
  @ ghost
     struct ep_public_info_t GHOST_in_eps[USBOTGHS_MAX_IN_EP] = { 0 };
     struct ep_public_info_t GHOST_out_eps[USBOTGHS_MAX_OUT_EP] = { 0 };
 */


#include "libusbctrl.h"

#endif/*__FRAMAC__*/

#endif/*LIBUSBOTGHS_FRAMAC_H_*/
