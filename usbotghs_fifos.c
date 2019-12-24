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

#include "generated/usb_otg_hs.h"
#include "usbotghs_handler.h"

/*
 * Size of the USB OTG HS core internal FIFO
 */
#define USBOTG_HS_RX_CORE_FIFO_SZ 0x80 /* 512 bytes, unit is 32bits DWORD here */
#define USBOTG_HS_TX_CORE_FIFO_SZ 0x80 /* 512 bytes, unit is 32bits DWORD here */

#if CONFIG_USR_DEV_USBOTGHS_DMA
/*
 * In DMA mode, the copy is done using DMA
 */
static inline void usbotghs_read_core_fifo(volatile uint8_t *dest, volatile uint32_t size, uint8_t ep)
{
}


static inline void usbotghs_write_core_fifo(volatile uint8_t *src, volatile uint32_t size, uint8_t ep)
{
#if CONFIG_USR_DEV_USBOTGHS_DMA
    /* configuring DMA for this FIFO */
    /* set EP0 FIFO using local buffer */
    /* 3. lock FIFO (while DMA is running) */
    /* 4. set Endpoint enabled (start the DMA transfer) */
    /* 5. unlock FIFO now that DMA transfer is finished */
#endif

}
#else
/*
 * With DMA mode deactivated, the copy is done manually
 */
static inline void usbotghs_read_core_fifo(volatile uint8_t *dest, volatile uint32_t size, uint8_t ep)
{
	uint32_t size_4bytes = size / 4;
    uint32_t tmp;

    /* 4 bytes aligned copy from EP FIFO */
	for (uint32_t i = 0; i < size_4bytes; i++, dest += 4){
		*(volatile uint32_t *)dest = *(USBOTG_HS_DEVICE_FIFO(ep));
	}
    /* read the residue */
	switch (size % 4) {
	case 1:
		*dest = (*(USBOTG_HS_DEVICE_FIFO(ep))) & 0xff;
		break;
	case 2:
		*(volatile uint16_t *)dest = (*(USBOTG_HS_DEVICE_FIFO(ep))) & 0xffff;
		break;
	case 3:
		tmp = *(USBOTG_HS_DEVICE_FIFO(ep));
		dest[0] = tmp & 0xff;
		dest[1] = (tmp >> 8) & 0xff;
		dest[2] = (tmp >> 16) & 0xff;
		break;
	default:
		break;
	}
}


static inline void usbotghs_write_core_fifo(volatile uint8_t *src, volatile uint32_t size, uint8_t ep)
{
	uint32_t size_4bytes = size / 4;
    uint32_t tmp = 0;
    // IP should has its own interrupts disable during ISR execution
    uint32_t oldmask = read_reg_value(r_CORTEX_M_USBOTG_HS_GINTMSK);
    /* mask interrupts while writting Core FIFO */
    set_reg_value(r_CORTEX_M_USBOTG_HS_GINTMSK, 0, 0xffffffff, 0);

    for (uint32_t i = 0; i < size_4bytes; i++, src += 4){
        write_reg_value(USBOTG_HS_DEVICE_FIFO(ep), *(const uint32_t *)src);
    }
    switch (size & 3) {
        case 1:
            write_reg_value(USBOTG_HS_DEVICE_FIFO(ep), *(const uint8_t *)src);
            break;
        case 2:
            write_reg_value(USBOTG_HS_DEVICE_FIFO(ep), *(const uint16_t *)src);
            break;
        case 3:
            tmp  = ((const uint8_t*) src)[0];
            tmp |= ((const uint8_t*) src)[1] << 8;
            tmp |= ((const uint8_t*) src)[2] << 16;
            write_reg_value(USBOTG_HS_DEVICE_FIFO(ep), tmp);
            break;
        default:
            break;
    }

    // IP should has its own interrupts disable during ISR execution
    set_reg_value(r_CORTEX_M_USBOTG_HS_GINTMSK, oldmask, 0xffffffff, 0);
}

#endif


mbed_error_t usbotghs_init_global_fifo(void)
{
    /*
     * 	  Set up the Data FIFO RAM for each of the FIFOs
	 *      – Program the OTG_HS_GRXFSIZ register, to be able to receive control OUT data
	 *        and setup data. If thresholding is not enabled, at a minimum, this must be equal to
	 *        1 max packet size of control endpoint 0 + 2 Words (for the status of the control
	 *        OUT data packet) + 10 Words (for setup packets).
	 *
	 * See reference manual section 34.11 for peripheral FIFO architecture.
	 * XXX: The sizes of TX FIFOs seems to be the size of TX FIFO #0 for
	 * all FIFOs. We don't know if it is really the case or if the DTXFSTS
	 * register does not give the free space for the right FIFO.
	 *
	 * 0                512                1024             1536
	 * +-----------------+------------------+-----------------+-----------
	 * |     RX FIFO     |     TX0 FIFO     | TXi FIFO (EP i) |
	 * |    128 Words    |    128 Words     |    128 Words    |...
	 * +-----------------+------------------+-----------------+------------
     * Settings FIFOs for Endpoint 0
     * RXFD (RxFIFO depth, in 32bits DWORD)
     */
	set_reg(r_CORTEX_M_USBOTG_HS_GRXFSIZ, USBOTG_HS_RX_CORE_FIFO_SZ, USBOTG_HS_GRXFSIZ_RXFD);

    return MBED_ERROR_NONE;
}

mbed_error_t usbotghs_reset_epx_fifo(usbotghs_ep_t *ep)
{
    if (ep->id == 0) {
        /*
         * EndPoint 0 TX FIFO configuration (should store a least 4 64byte paquets)
         */
        set_reg(r_CORTEX_M_USBOTG_HS_DIEPTXF0, USBOTG_HS_TX_CORE_FIFO_SZ, USBOTG_HS_DIEPTXF_INEPTXSA);
        set_reg(r_CORTEX_M_USBOTG_HS_DIEPTXF0, USBOTG_HS_TX_CORE_FIFO_SZ, USBOTG_HS_DIEPTXF_INEPTXFD);
        /*
         * 4. Program STUPCNT in the endpoint-specific registers for control OUT endpoint 0 to receive a SETUP packet
         *      – STUPCNT = 3 in OTG_HS_DOEPTSIZ0 (to receive up to 3 back-to-back SETUP packets)
         */
        set_reg(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(0),
                3, USBOTG_HS_DOEPTSIZ_STUPCNT);
        set_reg(r_CORTEX_M_USBOTG_HS_DOEPCTL(0),
                1, USBOTG_HS_DOEPCTL_CNAK);
    } else {
        /* all other EPs have their DIEPTXF registers accesible through a single macro */
        set_reg(r_CORTEX_M_USBOTG_HS_DIEPTXF(ep->id), ep->mpsize, USBOTG_HS_DIEPTXF_INEPTXSA);
        set_reg(r_CORTEX_M_USBOTG_HS_DIEPTXF(ep->id), ep->mpsize, USBOTG_HS_DIEPTXF_INEPTXFD);
    }
    ep->fifo_idx = 0;
    ep->fifo = NULL;
    ep->fifo_lck = false;
    ep->fifo_size = 0;
    return MBED_ERROR_NONE;
}

/*
 * read from Core EPx FIFO to associated RAM FIFO for given EP.
 * The EP must be a receiver EP (IN in host mode, OUT in device mode)
 *
 * There is two ways to copy from Core FIFO to RAM FIFO:
 * 1. Manual recopy
 * 2. DMA recopy
 */
mbed_error_t usbotghs_read_epx_fifo(uint32_t size, usbotghs_ep_t *ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* sanitation */
    if (ep->configured == false) {
        log_printf("[USBOTG][HS] EPx %d not configured\n", ep->id);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* TODO: checking that EP is in correct direction before continuing */
    if (size == 0 || size > (ep->fifo_size - ep->fifo_idx)) {
        log_printf("[USBOTG][HS] invalid or too big size: %d\n", size);
        /* Why reading 0 bytes from Core FIFO ? */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* Let's now do the read transaction itself... */
    if (ep->fifo_lck != false) {
        log_printf("[USBOTG][HS] invalid state! fifo already locked\n");
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    ep->fifo_lck = true;
    usbotghs_read_core_fifo(ep->fifo, size, ep->id);
    ep->fifo_idx += size;
    ep->fifo_lck = false;
err:
    return errcode;
}

/*
 * read from the EPx RAM FIFO to the Core EPx FIFO.
 * The EP must be a sender EP (OUT in host mode, IN in device mode).
 *
 * There is two ways to copy from RAM FIFO to Core FIFO:
 * 1. Manual recopy
 * 2. DMA recopy
 *
 * Here, size is already splitted to be smaller than current EP mpsize
 * Moreover, the TX FIFO ZS is (must) be bigger than EP MPSize in order to
 * permit packet transmission. As a consequence, comparison to FIFO MAX SZ is not
 * needed.
 */
mbed_error_t usbotghs_write_epx_fifo(uint32_t size, usbotghs_ep_t *ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitation */
    /* we consider that packet splitting is made by the caller (i.e. usbotghs_send()) */
    if (size > ep->mpsize) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* Let's now do the read transaction itself... */
    if (ep->fifo_lck != false) {
        log_printf("[USBOTG][HS] invalid state! fifo already locked\n");
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    ep->fifo_lck = true;
    usbotghs_write_core_fifo(ep->fifo, size, ep->id);
    ep->fifo_idx += size;
    ep->fifo_lck = false;
err:
    return errcode;
}

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
mbed_error_t usbotghs_set_recv_fifo(uint8_t *dst, uint32_t size, uint8_t epid)
{
    usbotghs_context_t *ctx = usbotghs_get_context();
    usbotghs_ep_t*      ep;
    mbed_error_t        errcode = MBED_ERROR_NONE;

    if (ctx->mode == USBOTGHS_MODE_DEVICE) {
        /* reception is done ON out_eps in device mode */
        ep = &(ctx->out_eps[epid]);
    } else {
        /* reception is done IN out_eps in device mode */
        ep = &(ctx->in_eps[epid]);
    }
    if (!ep->configured) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
#if CONFIG_USR_DEV_USBOTGHS_DMA
    if (ep->recv_fifo_dma_lck) {
        /* a DMA transaction is currently being executed toward the recv FIFO.
         * Wait for it to finish before resetting it */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
#endif
    /* set RAM FIFO for current EP. */
    ep->fifo = dst;
    ep->fifo_idx = 0;
    ep->fifo_size = size;

#if CONFIG_USR_DEV_USBOTGHS_DMA
    /* configuring DMA for this FIFO */
    /* set EP0 FIFO using local buffer */
	write_reg_value(r_CORTEX_M_USBOTG_HS_DOEPDMA(epid),
                    dst);
#endif

    /* FIFO is now configured */
err:
    return errcode;
}

mbed_error_t usbotghs_set_xmit_fifo(uint8_t *src, uint32_t size, uint8_t epid)
{
    usbotghs_context_t *ctx = usbotghs_get_context();
    usbotghs_ep_t*      ep;
    mbed_error_t        errcode = MBED_ERROR_NONE;

    if (ctx->mode == USBOTGHS_MODE_DEVICE) {
        /* reception is done ON out_eps in device mode */
        ep = &(ctx->out_eps[epid]);
    } else {
        /* reception is done IN out_eps in device mode */
        ep = &(ctx->in_eps[epid]);
    }
    if (!ep->configured) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (ep->fifo_lck) {
        /* a DMA transaction is currently being executed toward the recv FIFO.
         * Wait for it to finish before resetting it */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* set RAM FIFO for current EP. */
    ep->fifo = src;
    ep->fifo_idx = 0;
    ep->fifo_size = size;

#if CONFIG_USR_DEV_USBOTGHS_DMA
    /* 1. set DMA src address*/
	write_reg_value(r_CORTEX_M_USBOTG_HS_DOEPDMA(epid), src);
#endif

    /* FIFO is now configured */
err:
    return errcode;
}
