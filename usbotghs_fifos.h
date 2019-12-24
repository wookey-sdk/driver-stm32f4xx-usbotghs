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

#ifndef USBOTGHS_FIFOS_H_
#define USBOTGHS_FIFOS_H_

#include "libc/types.h"

#include "api/libusbotghs.h"
#include "usbotghs.h"

mbed_error_t usbotghs_init_global_fifo(void);

mbed_error_t usbotghs_reset_epx_fifo(usbotghs_ep_t *ep);

/* FIFO RAM buffers are EP contexts informations, and don't need to be passed as
 * parameters */
mbed_error_t usbotghs_read_epx_fifo(uint32_t size, usbotghs_ep_t *ep);

/* FIFO RAM buffers are EP contexts informations, and don't need to be passed as
 * parameters */
mbed_error_t usbotghs_write_epx_fifo(uint32_t size, usbotghs_ep_t *ep);

mbed_error_t usbotghs_set_recv_fifo(uint8_t *dst, uint32_t size, uint8_t epid);

mbed_error_t usbotghs_set_xmit_fifo(uint8_t *src, uint32_t size, uint8_t epid);

#endif/*!USBOTGHS_FIFOS_H_*/
