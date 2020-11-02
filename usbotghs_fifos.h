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

#ifndef USBOTGHS_FIFOS_H_
#define USBOTGHS_FIFOS_H_

#include "libc/types.h"

#include "api/libusbotghs.h"
#include "usbotghs.h"

/*
 * Size of the USB OTG HS core internal FIFO (global config, not per EP)
 */
#define USBOTG_HS_RX_CORE_FIFO_SZ 512 /* 128 bytes, unit is 32bits DWORD here */
#define USBOTG_HS_TX_CORE_FIFO_SZ 512 /* 128 bytes, unit is 32bits DWORD here */



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

void usbotghs_read_core_fifo(uint8_t *dest, uint32_t size, uint8_t ep);

/* flush the Core TxFIFO of the given EP. This functions does *not* upate the
 * associated EP ctx (fifo_idx, fifo_size) */
mbed_error_t usbotghs_txfifo_flush(uint8_t ep_id);

/* flush the Core TxFIFO of all the IN (Tx in device mode) EP.
 * This functions does *not* upate the associated EP ctx (fifo_idx, fifo_size) */
mbed_error_t usbotghs_txfifo_flush_all(void);

mbed_error_t usbotghs_rxfifo_flush(uint8_t ep_id);

#endif/*!USBOTGHS_FIFOS_H_*/
