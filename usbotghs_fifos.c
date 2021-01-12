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

#include "libc/regutils.h"
#include "libc/types.h"
#include "libc/sync.h"
#include "libc/stdio.h"
#include "api/libusbotghs.h"
#include "usbotghs_regs.h"
#include "usbotghs_fifos.h"
#include "usbotghs.h"
#include "usbotghs_handler.h"
#include "generated/usb_otg_hs.h"

#if defined(__FRAMAC__)
#include "socs/stm32f439/usbctrl_backend.h"
#else
#include "libs/usbctrl/api/libusbctrl.h"
#endif/*!__FRAMAC__*/


/* Hardware IP FIFO size */
#define CORE_FIFO_LENGTH 4096

/*@
  @ requires ep < USBOTGHS_MAX_OUT_EP;
  @ requires size > 0;
  @ requires \valid(dest + (0 .. size-1));
  @ requires (uint32_t *)USB_BACKEND_MEMORY_BASE <= USBOTG_HS_DEVICE_FIFO(ep) <= (uint32_t *)USB_BACKEND_MEMORY_END ;

  @ requires \separated(&usbotghs_ctx,&num_ctx,&SIZE_DESC_FIXED,&FLAG,
                         ctx_list+(..),dest+(..));
  @ assigns *(dest + (0 .. size-1));

  @ behavior badep:
  @    assumes ep >= USBOTGHS_MAX_OUT_EP;
  @    ensures *(dest + (0 .. size-1)) == \old(*(dest + (0 .. size-1)));
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior ok:
  @    assumes ep < USBOTGHS_MAX_OUT_EP;
  @    ensures \result == MBED_ERROR_NONE;

  @ disjoint behaviors;
  @ complete behaviors;

  */

mbed_error_t usbotghs_read_core_fifo(uint8_t * const dest, const uint32_t size, uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
#if CONFIG_USR_DEV_USBOTGHS_DMA
    /*
     * In DMA mode, the copy is done using DMA
     */

#else
    /*
     * With DMA mode deactivated, the copy is done manually
     */
    const uint32_t size_4bytes = size / 4;
    uint32_t tmp;

    /* 4 bytes aligned copy from EP FIFO */
    uint32_t offset = 0;

    /*@
      @ loop invariant 0 <= i <= size_4bytes;
      @ loop invariant size >=0;
      @ loop invariant \valid(dest + (0 ..size -1));
      @ loop invariant 0<=offset <= size ;
      @ loop invariant 0 <= size_4bytes <= size;
      @ loop assigns offset, i, tmp;
      @ loop assigns *(dest+(0..4*size_4bytes -1));
      @ loop variant (size_4bytes - i);
      */
    for (uint32_t i = 0; i < size_4bytes; i++) {
        tmp = *(USBOTG_HS_DEVICE_FIFO(ep));
        /*@ assert size_4bytes >=1 ==> size >=4*size_4bytes; */
        dest[offset + 0] = tmp & 0xff;
        dest[offset + 1] = (tmp >> 8) & 0xff;
        dest[offset + 2] = (tmp >> 16) & 0xff;
        dest[offset + 3] = (tmp >> 24) & 0xff;
        //old, FRAMAC incompatible cast *(uint32_t *)dest = *(USBOTG_HS_DEVICE_FIFO(ep));
        /* this assert must be set **before** the offset increment, as, when size is a 4 bytes
           multiple, the last increment of offset generate an overflow. Though, this
           overflow **is not impacting** as in this last case, offset is no more used. */
        offset += 4;
        /*@ assert offset<= 4*size_4bytes; */
    }
    /*@ assert offset <= size;*/
    /*@ assert offset == 4*size_4bytes; */
    /*@ assert size == (size_4bytes * 4) + (size%4); */
    /*@ assert offset == size - (size%4); */
        request_data_membarrier();
        /* read the residue */
    switch (size % 4) {
    case 0:
      /*@ assert offset == size ; */
      break;
    case 1:
      /*@ assert offset == size-1; */
      dest[offset] = (*(USBOTG_HS_DEVICE_FIFO(ep))) & 0xff;
      break;
    case 2:
      /*@ assert offset +1  == size-1; */
      /* assigned to u32, LSB only set (little endian case !!!) */
      tmp = *(USBOTG_HS_DEVICE_FIFO(ep)) & 0xffff;
      dest[offset] = tmp & 0xff;
      dest[offset + 1] = (tmp >> 8) & 0xff;
      break;
    case 3:
      /*@ assert offset +2 == size-1; */
      tmp = *(USBOTG_HS_DEVICE_FIFO(ep));
      dest[offset] = tmp & 0xff;
      dest[offset + 1] = (tmp >> 8) & 0xff;
      dest[offset + 2] = (tmp >> 16) & 0xff;
      break;
    default:
      /* should be dead code */
      break;
    }
    request_data_membarrier();
#endif
    return errcode;
}


/*  requires ep < USBOTGHS_MAX_IN_EP needed for memory space :
    if ep >= USBOTGHS_MAX_IN_EP, USBOTG_HS_DEVICE_FIFO(ep) target reserved memory
        this limit is hardware dependant (even if USBOTGHS_MAX_IN_EP > USBOTGHS_MAX_OUT_EP, it is not possible
        to handle more than USBOTGHS_MAX_IN_EP (+ EP0))
*/
/*@
    @ requires ep < USBOTGHS_MAX_IN_EP ;
    @ requires size > 0;
    @ requires \valid_read(src + (0 .. size-1));
    @ requires (uint32_t *)USB_BACKEND_MEMORY_BASE <= USBOTG_HS_DEVICE_FIFO(ep) <= (uint32_t *)USB_BACKEND_MEMORY_END ;
    @ requires \separated(((uint32_t *)((int)(0x40040000 + (int)(0x1000 * (int)((int)ep + 1))))), ((uint32_t *) r_CORTEX_M_USBOTG_HS_GINTMSK),src) ;
    @ assigns *((uint32_t *)((int)(0x40040000 + (int)(0x1000 * (int)((int)ep + 1))))), *((uint32_t *) r_CORTEX_M_USBOTG_HS_GINTMSK),*src;
*/
static inline void usbotghs_write_core_fifo(uint8_t *src, const uint32_t size, uint8_t ep)
{
#if CONFIG_USR_DEV_USBOTGHS_DMA
    /* configuring DMA for this FIFO */
    /* set EP0 FIFO using local buffer */
    /* 3. lock FIFO (while DMA is running) */
    /* 4. set Endpoint enabled (start the DMA transfer) */
    /* 5. unlock FIFO now that DMA transfer is finished */
#else
	uint32_t size_4bytes = size / 4;
    uint32_t tmp = 0;
    log_printf("[USBOTG][HS] writing %d bytes to EP %d core TxFIFO\n", size, ep);
    // IP should has its own interrupts disable during ISR execution
    uint32_t oldmask = read_reg_value(r_CORTEX_M_USBOTG_HS_GINTMSK);
    /* mask interrupts while writting Core FIFO */
    set_reg_value(r_CORTEX_M_USBOTG_HS_GINTMSK, 0, 0xffffffff, 0);

    /* manual copy to Core FIFO */
    /* there is no overflow on src here, as the C divisor is natural integer
     * divisor, truncating the divised size value to the first integer below
     */

    /*@
        @ loop invariant 0 <= i <= size_4bytes;
        @ loop invariant ep < USBOTGHS_MAX_IN_EP ;
        @ loop invariant (uint32_t *)USB_BACKEND_MEMORY_BASE <= USBOTG_HS_DEVICE_FIFO(ep) <= (uint32_t *)USB_BACKEND_MEMORY_END ;
        @ loop invariant \separated(src,((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ) ;
	@ loop assigns i, tmp, src, *((uint32_t *)((int)(0x40040000 + (int)(0x1000 * (int)((int)ep + 1)))));
        @ loop variant (size_4bytes - i) ;
    */

    for (uint32_t i = 0; i < size_4bytes; i++, src += 4){
        tmp = src[0];
        tmp |= (uint32_t)(src[1] & 0xff) << 8;
        tmp |= (uint32_t)(src[2] & 0xff) << 16;
        tmp |= (uint32_t)(src[3] & 0xff) << 24;
        write_reg_value(USBOTG_HS_DEVICE_FIFO(ep), tmp);

    }
    tmp = 0;
    switch (size & 3) {
        /* sequencialy write up to 3 bytes into tmp (depending on the carry)
         * and write tmp to Core FIFO
         * INFO: the sequencial bytes inclusion (up to 3) is managed by *removing*
         * the switch/case breaks. Do not re-add it ! */
        case 3:
            tmp = ((const uint8_t*) src)[2] << 16;
            __explicit_fallthrough
        case 2:
            tmp |= ((const uint8_t*) src)[1] << 8;
            __explicit_fallthrough
        case 1:
            tmp  |= ((const uint8_t*) src)[0];
            write_reg_value(USBOTG_HS_DEVICE_FIFO(ep), tmp);
            break;
        default:
            /* should never happend, complete switch */
            break;
    }

    /* IP should has its own interrupts disable during ISR execution */
    set_reg_value(r_CORTEX_M_USBOTG_HS_GINTMSK, oldmask, 0xffffffff, 0);
#endif
}

/*@
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.fifo_idx;
  @ ensures \result == MBED_ERROR_NONE;
  */
mbed_error_t usbotghs_init_global_fifo(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    /*
     * 	  Set up the Data FIFO RAM for each of the FIFOs
	 *      – Program the OTG_HS_GRXFSIZ register, to be able to receive control OUT data
	 *        and setup data. If thresholding is not enabled, at a minimum, this must be equal to
	 *        1 max packet size of control endpoint 0 + 2 Words (for the status of the control
	 *        OUT data packet) + 10 Words (for setup packets).
     *        for  e.g. giving 64 bytes for max EP0 Pkt size, this means 64 + 2*wz + 10*wz
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
    /* PTH: to check: executed at reset handling time: here we set back fifo_idx from
     * 0 as the device is reset. previously configured FIFO slots are purged and
     * must be reconfigured using usbotghs_reset_epx_fifo() */
    set_u16_with_membarrier(&ctx->fifo_idx, USBOTG_HS_RX_CORE_FIFO_SZ);
    /* setting TX0FSIZ to */

    return errcode;
}

/*@
    @ requires \valid(ep);
    @ requires \separated(((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), &usbotghs_ctx) ;
    @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)),usbotghs_ctx.fifo_idx, *ep , usbotghs_ctx.in_eps[0 .. USBOTGHS_MAX_IN_EP-1], usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_OUT_EP-1];
    @ behavior epid_null_NOSTORAGE:
    @   assumes &usbotghs_ctx != \null;
    @   assumes (ep->id == 0) ;
    @   assumes usbotghs_ctx.fifo_idx + (uint16_t)USBOTG_HS_TX_CORE_FIFO_SZ >= (uint16_t)CORE_FIFO_LENGTH ;
    @   ensures \result == MBED_ERROR_NOSTORAGE ;
    @   ensures ep->mpsize == \old(ep->mpsize) ;

    @ behavior epid_null_STORAGE_OK:
    @   assumes &usbotghs_ctx != \null;
    @   assumes (ep->id == 0) ;
    @   assumes !(usbotghs_ctx.fifo_idx + (uint16_t)USBOTG_HS_TX_CORE_FIFO_SZ >= (uint16_t)CORE_FIFO_LENGTH) ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior epid_not_null :
    @   assumes &usbotghs_ctx != \null;
    @   assumes !(ep->id == 0) ;
    @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_NOSTORAGE ;

    @ complete behaviors;
    @ disjoint behaviors ;
*/

/*
    TODO : be more precise for behavior epid_not_null : problem proving \result == MBED_ERROR_NOSTORAGE, problably
            du to some assume about ep->mpsize
*/

mbed_error_t usbotghs_reset_epx_fifo(usbotghs_ep_t *ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    /*@ assert ctx != NULL; */
    if (ep->id == 0) {
        /*
         * EndPoint 0 TX FIFO configuration (should store a least 4 64byte paquets)
         */
        /*  – Program the OTG_HS_TX0FSIZ register (depending on the FIFO number
         *  chosen) to be able to transmit control IN data. At a minimum, this must be equal to
         *  1 max packet size of control endpoint 0.
         *
         *  FIXME: this work is not made in the previous driver... Maybe we should correct this here.
         */

        if (ctx->fifo_idx + USBOTG_HS_TX_CORE_FIFO_SZ >= CORE_FIFO_LENGTH) {
            errcode = MBED_ERROR_NOSTORAGE;
            goto err;
        }

        /*
         */
        /* FIXME: DIEPTXF fifo size is in word unit, shouldn't it be fifo_idx/4 ? see USBOTGFS driver */
        set_reg(r_CORTEX_M_USBOTG_HS_DIEPTXF0, USBOTG_HS_RX_CORE_FIFO_SZ, USBOTG_HS_DIEPTXF_INEPTXSA);
        set_reg(r_CORTEX_M_USBOTG_HS_DIEPTXF0, USBOTG_HS_TX_CORE_FIFO_SZ, USBOTG_HS_DIEPTXF_INEPTXFD);
        /*
         * 4. Program STUPCNT in the endpoint-specific registers for control OUT endpoint 0 to receive a SETUP packet
         *      – STUPCNT = 3 in OTG_HS_DOEPTSIZ0 (to receive up to 3 back-to-back SETUP packets)
         */
        set_reg(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(0),
                3, USBOTG_HS_DOEPTSIZ_STUPCNT);
        set_reg(r_CORTEX_M_USBOTG_HS_DOEPCTL(0),
                1, USBOTG_HS_DOEPCTL_CNAK);
        usbotghs_txfifo_flush(0);
        set_u16_with_membarrier(&ctx->fifo_idx, ctx->fifo_idx + USBOTG_HS_TX_CORE_FIFO_SZ);
    } else {
        /* all other EPs have their DIEPTXF registers accesible through a single macro */
        if (ep->dir == USBOTG_HS_EP_DIR_OUT) {
            /* using global RX fifo... GRXFIFOSZ set as global RX FIFO */
        } else {
            set_reg(r_CORTEX_M_USBOTG_HS_DIEPTXF(ep->id), ctx->fifo_idx, USBOTG_HS_DIEPTXF_INEPTXSA);
            /* this field is in 32bits words unit */
            /* for very small mpsize EP (e.g. keyboards, we must support at list
             * URB size + mpsize */

            uint32_t fifosize;
            if (ep->mpsize <= 64) {
                fifosize = 128;
            } else {
                fifosize = ep->mpsize;
            }


            if (ctx->fifo_idx + fifosize >= CORE_FIFO_LENGTH) {
                errcode = MBED_ERROR_NOSTORAGE;
                goto err;
            }

            /* FIXME: DIEPTXF fifo size is in word unit, shouldn't it be fifosize/4 ? */
            set_reg(r_CORTEX_M_USBOTG_HS_DIEPTXF(ep->id), fifosize, USBOTG_HS_DIEPTXF_INEPTXFD);
            set_u16_with_membarrier(&ctx->fifo_idx, ctx->fifo_idx + fifosize);
        }
    }

    set_bool_with_membarrier(&(ep->fifo_lck), true);
    ep->fifo_idx = 0;
    ep->fifo = NULL;
    ep->fifo_size = 0;
    ep->core_txfifo_empty = true;
    set_bool_with_membarrier(&(ep->fifo_lck), false);
err:
    return errcode;
}


/*
 * read from Core EPx FIFO to associated RAM FIFO for given EP.
 * The EP must be a receiver EP (IN in host mode, OUT in device mode)
 *
 * There is two ways to copy from Core FIFO to RAM FIFO:
 * 1. Manual recopy
 * 2. DMA recopy
 */
/*@
  @ requires 0 <= ep_id < USBOTGHS_MAX_OUT_EP;
  @ requires size > 0;
  @ requires \separated(&usbotghs_ctx, ((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)),&num_ctx,ctx_list+(..));
  @ assigns usbotghs_ctx.out_eps[ep_id],  *(usbotghs_ctx.out_eps[ep_id].fifo+(usbotghs_ctx.out_eps[ep_id].fifo_idx..(usbotghs_ctx.out_eps[ep_id].fifo_idx + (size-1))));

  @ behavior notconfigured:
  @    assumes usbotghs_ctx.out_eps[ep_id].configured == \false;
  @    ensures \result == MBED_ERROR_INVPARAM;


  @ behavior nofifo:
  @    assumes usbotghs_ctx.out_eps[ep_id].configured != \false;
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo == NULL;
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior invalididx:
  @    assumes usbotghs_ctx.out_eps[ep_id].configured == \true;
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo != NULL;
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo_idx > usbotghs_ctx.out_eps[ep_id].fifo_size;
  @    ensures \result == MBED_ERROR_UNKNOWN;

  @ behavior sizetoobig:
  @    assumes usbotghs_ctx.out_eps[ep_id].configured == \true;
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo != NULL;
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo_idx <= usbotghs_ctx.out_eps[ep_id].fifo_size;
  @    assumes size > (usbotghs_ctx.out_eps[ep_id].fifo_size - usbotghs_ctx.out_eps[ep_id].fifo_idx);
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior fifolocked:
  @    assumes usbotghs_ctx.out_eps[ep_id].configured == \true;
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo != NULL;
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo_idx <= usbotghs_ctx.out_eps[ep_id].fifo_size;
  @    assumes 0 < size <= (usbotghs_ctx.out_eps[ep_id].fifo_size - usbotghs_ctx.out_eps[ep_id].fifo_idx);
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo_lck == \true;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes usbotghs_ctx.out_eps[ep_id].configured == \true;
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo != NULL;
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo_idx <= usbotghs_ctx.out_eps[ep_id].fifo_size;
  @    assumes 0 < size <= (usbotghs_ctx.out_eps[ep_id].fifo_size - usbotghs_ctx.out_eps[ep_id].fifo_idx);
  @    assumes usbotghs_ctx.out_eps[ep_id].fifo_lck != \true;
  @    ensures \result == MBED_ERROR_NONE;


  @ complete behaviors;
  @ disjoint behaviors;

  */
mbed_error_t usbotghs_read_epx_fifo(uint32_t size, uint8_t ep_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    usbotghs_ep_t*      ep = NULL;

    ep = &(ctx->out_eps[ep_id]);

    /* sanitation */
    if (ep->configured == false) {
        log_printf("[USBOTG][HS] EPx %d not configured\n", ep->id);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (ep->fifo == NULL) {
        log_printf("[USBOTG][HS] EPx %d FIFO not set\n", ep->id);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    /*@ assert \valid(ep); */
    /* @assert \valid(ep->fifo); */
    /* @assert \separated(((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)),
           &num_ctx,ctx_list+(..),&usbotghs_ctx,
           usbotghs_ctx.out_eps[ep_id].fifo+(0..usbotghs_ctx.out_eps[ep_id].fifo_size)); */

    /* TODO: checking that EP is in correct direction before continuing */
    if (ep->fifo_idx > ep->fifo_size) {
        log_printf("[USBOTG][HS] FIFO idx to big! This should not happen on EPx %d\n", ep->id);
        /*@ assert \at(usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_IN_EP-1],Here) == \at(usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_IN_EP-1],Pre);*/
        errcode = MBED_ERROR_UNKNOWN;
        goto err;
    }
    if (size > (ep->fifo_size - ep->fifo_idx)) {
        log_printf("[USBOTG][HS] invalid or too big size in ep %d: %d (fifo: 0x%x, fifo size: %d, idx: %d)\n", ep->id, size, ep->fifo, ep->fifo_size, ep->fifo_idx);
        /* Why reading 0 bytes from Core FIFO ? */
        errcode = MBED_ERROR_INVPARAM;
        /*@ assert \at(usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_IN_EP-1],Here) == \at(usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_IN_EP-1],Pre);*/
        goto err;
    }
    /* Let's now do the read transaction itself... */
    if (ep->fifo_lck != false) {
        log_printf("[USBOTG][HS] invalid state! fifo already locked\n");
        errcode = MBED_ERROR_INVSTATE;
        /*@ assert \at(usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_IN_EP-1],Here) == \at(usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_IN_EP-1],Pre);*/
        goto err;
    }
    set_bool_with_membarrier(&(ep->fifo_lck), true);
    /* @ assert \valid(ep->fifo + (0 .. (ep->fifo_idx+size-1))); */
    usbotghs_read_core_fifo(&(ep->fifo[ep->fifo_idx]), size, ep->id);
    ep->fifo_idx += size;
    request_data_membarrier();
    set_bool_with_membarrier(&(ep->fifo_lck), false);
    /*@ assert errcode == MBED_ERROR_NONE; */
err:
    /* INVSTATE patch */
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

/*@
    @ requires ep_id < USBOTGHS_MAX_IN_EP;
    @ requires 0 < size <= USBOTG_HS_TX_CORE_FIFO_SZ;
    @ requires \valid(&usbotghs_ctx.in_eps[ep_id].fifo_lck);
    @ requires \valid(&usbotghs_ctx.in_eps[ep_id].fifo_idx);
    @ requires \valid(&usbotghs_ctx.in_eps[ep_id].fifo_size);
    @ requires \valid(usbotghs_ctx.in_eps[ep_id].fifo+(0..usbotghs_ctx.in_eps[ep_id].fifo_size-1));
    @ requires \separated( ((uint32_t *)((int)(0x40040000 + (int)(0x1000 * (int)((int)usbotghs_ctx.in_eps[ep_id].id + 1))))),(uint32_t *) r_CORTEX_M_USBOTG_HS_GINTMSK ,&num_ctx,ctx_list+(..),&usbotghs_ctx.in_eps[ep_id].fifo[\at(usbotghs_ctx.in_eps[ep_id].fifo_idx,Pre)],&usbotghs_ctx.in_eps[ep_id]+(0..sizeof(usbotghs_context_t)));


    @ behavior fifolocked:
    @    assumes usbotghs_ctx.in_eps[ep_id].fifo_lck == \true;
    @    ensures \result == MBED_ERROR_INVSTATE && usbotghs_ctx.in_eps[ep_id].fifo_lck == \false;
    @   assigns usbotghs_ctx.in_eps[ep_id].fifo_lck;

    @ behavior fifotoosmall:
    @    assumes usbotghs_ctx.in_eps[ep_id].fifo_lck == \false;
    @    assumes (size > usbotghs_ctx.in_eps[ep_id].fifo_size || usbotghs_ctx.in_eps[ep_id].fifo_idx  > (usbotghs_ctx.in_eps[ep_id].fifo_size - size));
    @    ensures \result == MBED_ERROR_NOMEM;
    @    assigns  usbotghs_ctx.in_eps[ep_id].fifo_lck;

    @ behavior ok:
    @    assumes usbotghs_ctx.in_eps[ep_id].fifo_lck == \false;
    @    assumes (size <= usbotghs_ctx.in_eps[ep_id].fifo_size && usbotghs_ctx.in_eps[ep_id].fifo_idx  <= (usbotghs_ctx.in_eps[ep_id].fifo_size - size));
    @    ensures \result == MBED_ERROR_NONE;
    @   assigns *((uint32_t *)((int)(0x40040000 + (int)(0x1000 * (int)((int)usbotghs_ctx.in_eps[ep_id].id + 1))))), *((uint32_t *) r_CORTEX_M_USBOTG_HS_GINTMSK), usbotghs_ctx.in_eps[ep_id].fifo_idx, usbotghs_ctx.in_eps[ep_id].fifo_lck, usbotghs_ctx.in_eps[ep_id].fifo[\at(usbotghs_ctx.in_eps[ep_id].fifo_idx,Pre)];

    @ complete behaviors;
    @ disjoint behaviors;
*/

mbed_error_t usbotghs_write_epx_fifo(const uint32_t size, uint8_t ep_id)
{
    usbotghs_context_t *ctx = usbotghs_get_context();
    usbotghs_ep_t*      ep = NULL;
    mbed_error_t errcode = MBED_ERROR_NONE;
/* sanitation */
    /* we consider that packet splitting is made by the caller (i.e. usbotghs_send()) */
    /* fixme: size > (USBOTG_HS_TX_CORE_FIFO_SZ - ep->fifo_idx) */
    ep = &(ctx->in_eps[ep_id]);
    /* Let's now do the read transaction itself... */
    if (ep->fifo_lck == true) {
        /* Tgus is not exactly dead code, but this check is a protection against reentrancy between the end of the
         * set_xmit_fifo() done by the caller (send_data()) and the current statement.
         * Here, we do not emulate this reentrancy behavior as framaC is not well-made for this */
        /*@ assert \false; */
        log_printf("[USBOTG][HS] invalid state! fifo already locked\n");
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /*@ assert \at(usbotghs_ctx.in_eps[ep_id].fifo_lck,Pre)!=\true; */
    if (size > ep->fifo_size) {
        /* this should be unreachable code, as fifo_size, fifo_idx and size are correlated and controled by the caller */
        /* Again, we may imagine a concurrent thread upgrading the FIFO somewhere during the caller's execution. Thus
         * this is an abnormal usage of the various stacks */
        /*@ assert \false; */
        log_printf("USBOTG][HS] buf overflow detected!\n");
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }
    if (ep->fifo_idx > (ep->fifo_size - size)) {
        log_printf("USBOTG][HS] buf overflow detected!\n");
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }
    set_bool_with_membarrier(&(ep->fifo_lck), true);
    /* FIFO should have been set with set_xmit_fifo, accordingly with its size */
    usbotghs_write_core_fifo(&(ep->fifo[ep->fifo_idx]), size, ep->id);
    /* buffer overflow check */
    ep->fifo_idx += size;
    request_data_membarrier();
err:
    set_bool_with_membarrier(&(ep->fifo_lck), false);
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

/* ep check is done by calling functions */
/*@

  @ requires \separated(&GHOST_nopublicvar, &usbotghs_ctx, ((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), dst + (0..size-1));
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.out_eps[epid].fifo, usbotghs_ctx.out_eps[epid].fifo_size, usbotghs_ctx.out_eps[epid].fifo_idx, usbotghs_ctx.out_eps[epid].fifo_lck;

  // private function contract, depend on private globals state
  @ ensures (\valid(dst) && epid < USBOTGHS_MAX_OUT_EP && (usbotghs_ctx.out_eps[epid].configured == \false || usbotghs_ctx.out_eps[epid].mpsize == 0)) ==> \result == MBED_ERROR_INVPARAM;

  @ ensures (\valid(dst) && epid < USBOTGHS_MAX_OUT_EP && (usbotghs_ctx.out_eps[epid].configured == \true && usbotghs_ctx.out_eps[epid].mpsize > 0) && size == 0) ==> \result == MBED_ERROR_INVPARAM;

  @ ensures(\valid(dst) && epid < USBOTGHS_MAX_OUT_EP && (usbotghs_ctx.out_eps[epid].configured == \true && usbotghs_ctx.out_eps[epid].mpsize > 0) && size > 0 && usbotghs_ctx.out_eps[epid].fifo_lck == \true) ==> \result == MBED_ERROR_INVSTATE;

  @ ensures (\valid(dst) && epid < USBOTGHS_MAX_OUT_EP && (usbotghs_ctx.out_eps[epid].configured == \true && usbotghs_ctx.out_eps[epid].mpsize > 0) && size > 0 && usbotghs_ctx.out_eps[epid].fifo_lck == \false) ==> \result == MBED_ERROR_NONE;

  */
mbed_error_t usbotghs_set_recv_fifo(uint8_t *dst, uint32_t size, uint8_t epid)
{
    usbotghs_context_t *ctx = usbotghs_get_context();
    usbotghs_ep_t*      ep;
    mbed_error_t        errcode = MBED_ERROR_NONE;

    /* no public (exported) variable is set. This GHOST var is used as countermeasure to public assignment
     * specification for functions that assign private global content */
    //@ ghost GHOST_nopublicvar = 1;

    if (dst == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (epid >= USBOTGHS_MAX_OUT_EP) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
        /* reception is done ON out_eps in device mode */
        ep = &(ctx->out_eps[epid]);
#else
        /* reception is done IN out_eps in device mode */
        ep = &(ctx->in_eps[epid]);
#endif
    if (!ep->configured || !ep->mpsize ) {  // ep->mpsize check to avoid RTE later
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    if (size == 0) {
        printf("[USBOTG] try to set FIFO of size 0\n");
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
    if (ep->fifo_lck == true) {
        /* Recv FIFO is currently being proceeded ! */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }

    /* set RAM FIFO for current EP. */

    /* Lock FIFO handling here */
    set_bool_with_membarrier(&(ep->fifo_lck), true);
    ep->fifo = dst;
    ep->fifo_idx = 0;
    ep->fifo_size = size;
    /* the following membarrier does push the previous fifo_* variables
     * to the memory, even if they were not using memory barrier at each
     * state. The lock being true, this section is concurrency safe  */
    set_bool_with_membarrier(&(ep->fifo_lck), false);

#if CONFIG_USR_DEV_USBOTGHS_DMA
    /* configuring DMA for this FIFO */
    /* set EP0 FIFO using local buffer */
    /*@ assert  r_CORTEX_M_USBOTG_HS_DOEPDMA(epid) \in ((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)); */
	//pmo pour les assigns
	write_reg_value(r_CORTEX_M_USBOTG_HS_DOEPDMA(epid),
                    dst);
#endif

    if (epid > 0) {
        /* configure EP for receiving size amount of data */
        uint32_t pktcount = size / ep->mpsize + (size & (ep->mpsize - 1) ? 1: 0);
	/*@ assert  r_CORTEX_M_USBOTG_HS_DOEPTSIZ(epid) \in ((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)); */
	//pmo pour les assigns
	set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(epid), pktcount, USBOTG_HS_DOEPTSIZ_PKTCNT_Msk(epid), USBOTG_HS_DOEPTSIZ_PKTCNT_Pos(epid));
	/*@ assert  r_CORTEX_M_USBOTG_HS_DOEPTSIZ(epid) \in ((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)); */
	//pmo pour les assigns
        set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(epid), size, USBOTG_HS_DOEPTSIZ_XFRSIZ_Msk(epid), USBOTG_HS_DOEPTSIZ_XFRSIZ_Pos(ep));
    } else {
        /* for EP0, the IP is not able to handle more than 64 bytes per
         * transfer. As a consequence, even for bigger transfers (e.g. 4K)
         * a fragmentation step is needed. This is done by:
         * 1. settting pktcunt and pktsize so that oepint is executed for each
         * 64 bytes packet
         * 2. oepint (in DATA_OUT mode ) check that fifo_idx == fifo_size.
         * If not, oepting does NOT call the upper class handler, silently
         * acknowledge. */
        set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(epid), 1, USBOTG_HS_DOEPTSIZ_PKTCNT_Msk(epid), USBOTG_HS_DOEPTSIZ_PKTCNT_Pos(epid));
        set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(epid), ep->mpsize, USBOTG_HS_DOEPTSIZ_XFRSIZ_Msk(epid), USBOTG_HS_DOEPTSIZ_XFRSIZ_Pos(epid));
    }
    /* FIFO is now configured */
    /* CNAK is done by endpoint activation */
    /*@ assert errcode == MBED_ERROR_NONE; */
err:
    return errcode;
}



/* epid check done by calling function, usbotghs_send_data
    TODO : add !CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE behavior and CONFIG_USR_DEV_USBOTGHS_DMA behavior
*/
/*@
    @ requires \valid_read(&usbotghs_ctx.in_eps[epid]);
    @ requires \valid_read(&usbotghs_ctx.in_eps[epid].fifo_lck);
    @ requires 0 <= epid < USBOTGHS_MAX_IN_EP;
    @ requires size > 0;
    @ requires \valid_read(src+(0..size-1));
    @ requires usbotghs_ctx.in_eps[epid].configured == \true;
    @ requires \separated(src+(0..size-1),&usbotghs_ctx.in_eps[epid].fifo_lck, &usbotghs_ctx.in_eps[epid].fifo_size,&usbotghs_ctx.in_eps[epid].fifo_idx,&usbotghs_ctx.in_eps[epid].fifo);

    @ behavior fifo_lock:
    @   assumes (usbotghs_ctx.in_eps[epid].fifo_lck == \true)  ;
    @   ensures \result == MBED_ERROR_INVSTATE ;
    @   assigns \nothing;

    @ behavior fifo_not_lck:
    @   assumes !(usbotghs_ctx.in_eps[epid].fifo_lck == \true)  ;
    @   assumes \valid(&usbotghs_ctx.in_eps[epid].fifo_lck);
    @   assumes \valid(&usbotghs_ctx.in_eps[epid].fifo);
    @   assumes \valid(&usbotghs_ctx.in_eps[epid].fifo_idx);
    @   assumes \valid(&usbotghs_ctx.in_eps[epid].fifo_size);
    @   ensures \result == MBED_ERROR_NONE && usbotghs_ctx.in_eps[epid].fifo == src && usbotghs_ctx.in_eps[epid].fifo_lck == \false && usbotghs_ctx.in_eps[epid].fifo_idx == 0 && usbotghs_ctx.in_eps[epid].fifo_size == size ;
    @   assigns usbotghs_ctx.in_eps[epid].fifo, usbotghs_ctx.in_eps[epid].fifo_lck, usbotghs_ctx.in_eps[epid].fifo_idx,usbotghs_ctx.in_eps[epid].fifo_size ;

    @ complete behaviors;
    @ disjoint behaviors ;
*/
mbed_error_t usbotghs_set_xmit_fifo(uint8_t *src, uint32_t size, uint8_t epid)
{
    usbotghs_context_t *ctx = usbotghs_get_context();
    usbotghs_ep_t*      ep;
    mbed_error_t        errcode = MBED_ERROR_NONE;

#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
        /* transmition is done using in_eps in device mode */
        ep = &(ctx->in_eps[epid]);
#else
        /* transmition is done using out_eps in device mode */
        ep = &(ctx->out_eps[epid]);
#endif
    if (ep->fifo_lck == true) {
      /* a DMA transaction is currently being executed toward the recv FIFO.
       * Wait for it to finish before resetting it */
      errcode = MBED_ERROR_INVSTATE;
      /*@ assert (\at(usbotghs_ctx.in_eps[epid].fifo_lck, Pre)==\true) ==> errcode==MBED_ERROR_INVSTATE; */
      goto err;
    }
    /*@ assert errcode != MBED_ERROR_INVSTATE && \at(usbotghs_ctx.in_eps[epid].fifo_lck,Pre)!= \true; */
    log_printf("[USBOTG][HS] set ep %d TxFIFO to %p (size %d)\n", ep->id, src, size);

    set_bool_with_membarrier(&(ep->fifo_lck), true);
    /* set RAM FIFO for current EP. */
    ep->fifo = src;
    ep->fifo_idx = 0;
    ep->fifo_size = size;
    set_bool_with_membarrier(&(ep->fifo_lck), false);

#if CONFIG_USR_DEV_USBOTGHS_DMA
    /* 1. set DMA src address*/
	write_reg_value(r_CORTEX_M_USBOTG_HS_DOEPDMA(epid), src);
#endif

    /* FIFO is now configured */
err:
	return errcode;
}

/*@
    @ requires ep_id < USBOTGHS_MAX_IN_EP;
    @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
    @ ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_BUSY ;
*/
mbed_error_t usbotghs_txfifo_flush(uint8_t ep_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
	/* Select which ep to flush and do it
 	 * This is the FIFO number that must be flushed using the TxFIFO Flush bit.
 	 * This field must not be changed until the core clears the TxFIFO Flush bit.
 	 */
    /*
     * Is there a previous flush being executed ? If yes, wait for this flush to
     * end.
     */

    if (get_reg(r_CORTEX_M_USBOTG_HS_GRSTCTL, USBOTG_HS_GRSTCTL_TXFFLSH)){
        errcode = MBED_ERROR_BUSY;
        goto err;
    }
    /*
	 * The application must write this bit only after checking that the core is neither writing to the
	 * TxFIFO nor reading from the TxFIFO. Verify using these registers:
	 */

	/* FIXME Read: the NAK effective interrupt ensures the core is not reading from the FIFO */

	/* Write: the AHBIDL bit in OTG_HS_GRSTCTL ensures that the core is not writing anything to the FIFO */
	set_reg(r_CORTEX_M_USBOTG_HS_GRSTCTL, ep_id, USBOTG_HS_GRSTCTL_TXFNUM);
	set_reg(r_CORTEX_M_USBOTG_HS_GRSTCTL, 1, USBOTG_HS_GRSTCTL_TXFFLSH);
    /* wait for fifo flush to be executed */

    /*@
        @ loop invariant 0 <= cpt <= CPT_HARD;
        @ loop assigns cpt;
        @ loop variant (CPT_HARD - cpt);
    */
    for(uint8_t cpt=0; cpt<CPT_HARD; cpt++){
        if (get_reg(r_CORTEX_M_USBOTG_HS_GRSTCTL, USBOTG_HS_GRSTCTL_TXFFLSH)) {
            if (cpt > USBOTGHS_REG_CHECK_TIMEOUT) {
                log_printf("[USBOTG][HS] HANG! Waiting for the core to clear the TxFIFO Flush bit GRSTCTL:TXFFLSH\n");
                errcode = MBED_ERROR_BUSY;
                goto err;
            }
        }
    }

err:
    return errcode;

}

/*@
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END));
 */
mbed_error_t usbotghs_txfifo_flush_all(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    usbotghs_context_t *ctx = usbotghs_get_context();
    /* Device mode, TxFIFO set in IN EPs */
    /*@
        @ loop invariant 0 <= i <= USBOTGHS_MAX_IN_EP;
        @ loop assigns i, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END));
        @ loop variant (USBOTGHS_MAX_IN_EP - i);
    */
    for (uint8_t i = 0; i < USBOTGHS_MAX_IN_EP; ++i) {
        if (ctx->in_eps[i].configured) {
            usbotghs_txfifo_flush(i);
        }
    }
    return errcode;
}

/*@
    @ requires ep_id < USBOTGHS_MAX_OUT_EP;
    @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
    @ ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_BUSY ;
*/
mbed_error_t usbotghs_rxfifo_flush(uint8_t ep_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    ep_id = ep_id;
	/* Select which ep to flush and do it
 	 * This is the FIFO number that must be flushed using the RxFIFO Flush bit.
 	 * This field must not be changed until the core clears the RxFIFO Flush bit.
 	 */

    /*@
        @ loop invariant 0 <= cpt <= CPT_HARD;
        @ loop assigns cpt;
        @ loop variant (CPT_HARD - cpt);
    */
    for(uint8_t cpt=0; cpt<CPT_HARD; cpt++){
        if (get_reg(r_CORTEX_M_USBOTG_HS_GRSTCTL, USBOTG_HS_GRSTCTL_RXFFLSH)) {
            if (cpt > USBOTGHS_REG_CHECK_TIMEOUT) {
                log_printf("[USBOTG][HS] HANG! Waiting for the core to clear the RxFIFO Flush bit GRSTCTL:RXFFLSH\n");
                errcode = MBED_ERROR_BUSY;
                goto err;
            }
        }
    }
	/*
	 * The application must write this bit only after checking that the core is neither writing to the
	 * TxFIFO nor reading from the TxFIFO. Verify using these registers:
	 */

	/* FIXME Read: the NAK effective interrupt ensures the core is not reading from the FIFO */

	/* Write: the AHBIDL bit in OTG_HS_GRSTCTL ensures that the core is not writing anything to the FIFO */
    /* requesting RX fifo flush (RX FIFO is shared in USB-OTG-HS device) */
	set_reg(r_CORTEX_M_USBOTG_HS_GRSTCTL, 1, USBOTG_HS_GRSTCTL_RXFFLSH);
    /*@
        @ loop invariant 0 <= cpt <= CPT_HARD;
        @ loop assigns cpt;
        @ loop variant (CPT_HARD - cpt);
    */
    for(uint8_t cpt=0; cpt<CPT_HARD; cpt++) {
        if (get_reg(r_CORTEX_M_USBOTG_HS_GRSTCTL, USBOTG_HS_GRSTCTL_RXFFLSH)) {
            if (cpt > USBOTGHS_REG_CHECK_TIMEOUT) {
                log_printf("[USBOTG][HS] HANG! Waiting for the core to clear the RxFIFO Flush bit GRSTCTL:RXFFLSH\n");
                errcode = MBED_ERROR_BUSY;
                goto err;
            }
        }
    }
err:
    return errcode;
}

/*
 * About generic part:
 * This part translate libusbctrl forward-declaration symbols to local symbols.
 * This permits to resolve all symbols of the libctrl abstraction layer into this
 * very driver one.
 * WARNING: this method has one single restriction: only one driver can be used
 * at a time by a given ELF binary (i.e. an application), as symbols are resolved
 * at link time.
 */
#ifndef __FRAMAC__
mbed_error_t usb_backend_drv_set_recv_fifo(uint8_t *dst, uint32_t size, uint8_t ep)
    __attribute__ ((alias("usbotghs_set_recv_fifo")));
#endif/*__FRAMAC__*/
