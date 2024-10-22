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
#include "libc/stdio.h"
#include "libc/sync.h"

#include "libc/sanhandlers.h"


#ifdef __FRAMAC__
# include "framac/entrypoint.h"
#endif

#include "api/libusbotghs.h"
#include "usbotghs_regs.h"
#include "usbotghs.h"

#include "generated/usb_otg_hs.h"
#include "usbotghs_fifos.h"
#include "usbotghs_handler.h"

/************************************************
 * Buffers (FIFO storage in RAM
 */
#if CONFIG_USR_DEV_USBOTGHS_DMA
uint8_t ep0_fifo[512] = {0};
#endif

/************************************************
 * About ISR handlers
 */
/*
 * interrupt flag bit identifier, as set in the INTSTS global interrupt status register
 * Some of these interrupts required an execution of a stack level handler, other not.
 *
 * When an interrupt is handled, all the bits must be checked against the following
 * bitfield definition, as multiple event may occur in the same time, and as a consequence be
 * handled in the same ISR.
 *
 * In all these interrupts, the following must be pushed to the upper layer:
 * - ESUSP (Early suspend, i.e. BUS_INACTIVE transition)
 * - USBRST (USB reset transition)
 * - USBSUSP (USB Suspend, i.e. BUS_INACTIVE transition, starting the USB DEFAULT state)
 * - IEPINT (IN Endpoint event interrupt)
 * - OEPINT (OUT Endpoint event interrupt)
 * - RXFLVL (RxFIFO non-empty interrupt)
 * - WKUPINT (Wakeup event interrupt)
 *
 * The USB OTG HS driver is neither responsible for dispatching received data between
 * interfaces, nor responsible for parsing setup packets or dispatching differencially
 * data or setup packets for various endpoint.
 * O(I)EPINT handlers get back the packet, its size, its EP num and type, and push
 * it back to the control plane for parsing/dispatching.
 */
typedef enum {
    USBOTGHS_IT_CMOD       = 0,    /*< Current Mode of Operation  */
    USBOTGHS_IT_MMIS       = 1,    /*< Mode mismatch */
    USBOTGHS_IT_OTGINT     = 2,    /*< OTG interrupt */
    USBOTGHS_IT_SOF        = 3,    /*< Start of Frame */
    USBOTGHS_IT_RXFLVL     = 4,    /*< RxFifo non-empty */
    USBOTGHS_IT_NPTXE      = 5,    /*< Non-periodic TxFIFO empty (Host mode) */
    USBOTGHS_IT_GINAKEFF   = 6,    /*< Global IN NAK effective */
    USBOTGHS_IT_GONAKEFF   = 7,    /*< Global OUT NAK effective*/
    USBOTGHS_IT_RESERVED8  = 8,    /*< Reserved */
    USBOTGHS_IT_RESERVED9  = 9,    /*< Reserved */
    USBOTGHS_IT_ESUSP      = 10,   /*< Early suspend */
    USBOTGHS_IT_USBSUSP    = 11,   /*< USB Suspend */
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


#if CONFIG_USR_DRV_USBOTGHS_DEBUG

static volatile uint32_t    usbotghs_int_cnt[32] = { 0 };


#endif
/*
 * Generic handler, used by default.
 */
/*@
  @ assigns \nothing;
  */
static mbed_error_t default_handler(void)
{
    return MBED_ERROR_NONE;
}

/*
 * Reserved handler, should never be executed, as interrupt flag corresponds to
 * 'Reserved' field.
 */
/*@
  @ assigns \nothing;
  */
static mbed_error_t reserved_handler(void)
{
    return MBED_ERROR_UNSUPORTED_CMD;
}

/*
 * USB Reset handler. Handling USB reset requests. These requests can be received in
 * various state and handle a core soft reset and configuration.
 *
 * 1. Set the NAK bit for all OUT endpoints:
 *  - DOEPCTLn.SNAK = 1 (for all OUT endpoints)
 * Unmask the following interrupt bits:
 *  - DAINTMSK.INEP0 = 1 (control 0 IN endpoint)
 *  - DAINTMSK.OUTEP0 = 1 (control 0 OUT endpoint)
 *  - DOEPMSK.SETUP = 1
 *  - DOEPMSK.XferCompl = 1
 *  - DIEPMSK.XferCompl = 1
 *  - DIEPMSK.TimeOut = 1
 *
 *  3. To transmit or receive data, the device must initialize more registers as
 *  specified in Device Initialization on page 154.
 *
 *  4. Set up the Data FIFO RAM for each of the FIFOs (only if Dynamic FIFO Sizing is
 *  enabled)
 *  - Program the GRXFSIZ Register, to be able to receive control OUT data and setup
 *    data. If thresholding is not enabled, at a minimum, this must be equal to 1 max
 *    packet size of control endpoint 0 + 2 DWORDs (for the status of the control OUT
 *    data packet) + 10 DWORDs (for setup packets). If thresholding is enabled, at a
 *    minimum, this must be equal to 2 * (DTHRCTL.RxThrLen/4 + 1) + 2 DWORDs (for the
 *    status of the control OUT data packet) + 10 DWORDs (for setup packets)
 *  - Program the GNPTXFSIZ Register in Shared FIFO operation or dedicated FIFO size
 *    register (depending on the FIFO number chosen) in Dedicated FIFO operation, to
 *    be able to transmit control IN data. At a minimum, this must be equal to 1 max
 *    packet size of control endpoint 0.If thresholding is enabled, this can be
 *    programmed to less than one max packet size.
 *
 * 5. Reset the Device Address field in Device Configuration Register (DCFG).
 * 6. (This step is not required if you are using Scatter/Gather DMA mode.) Program
 *    the following fields in the endpoint-specific registers for control OUT endpoint
 *    0 to receive a SETUP packet
 *  - DOEPTSIZ0.SetUP Count = 3 (to receive up to 3 back-to-back SETUP packets)
 *  - In DMA mode, DOEPDMA0 register with a memory address to store any SETUP packets
 *    received
 *
 *    At this point, all initialization required to receive SETUP packets is done,
 *    except for enabling control OUT endpoint 0 in DMA mode.
 */
/*@
  @ requires \separated(((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), &usbotghs_ctx);
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.fifo_idx, usbotghs_ctx.in_eps[0 .. USBOTGHS_MAX_IN_EP-1], usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_OUT_EP-1];
  */
static mbed_error_t reset_handler(void)
{
    log_printf("[USB HS][RESET] received USB Reset\n");
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();

    /*@ assert \valid_read(ctx); */
    /*@
      @ loop invariant 0 <= i <= USBOTGHS_MAX_OUT_EP;
      @ loop assigns i, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END));
      @ loop variant USBOTGHS_MAX_OUT_EP - i;
      */
    for (uint8_t i = 0; i < USBOTGHS_MAX_OUT_EP; ++i) {
        /* if Out EPi is configured, set DOEPCTLi.SNAK to 1 */
        if (ctx->out_eps[i].configured) {
            log_printf("[USB HS][RESET] activate SNAK for out_ep %d\n", i);
            set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(i),
                         USBOTG_HS_DOEPCTL_CNAK_Msk);
        }
    }

    /* unmask control pipe requested interrupt bits:
     * activate OEPInt, IEPInt & RxFIFO non-empty.
     * Ready to receive requests on EP0.
     */
	set_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK,
                 USBOTG_HS_GINTMSK_OEPINT_Msk   |
                 USBOTG_HS_GINTMSK_IEPINT_Msk   |
				 USBOTG_HS_GINTMSK_RXFLVLM_Msk);
    /* unmask control 0 IN & OUT endpoint interrupts */
	set_reg_bits(r_CORTEX_M_USBOTG_HS_DAINTMSK,
                 USBOTG_HS_DAINTMSK_IEPM(0)   |
                 USBOTG_HS_DAINTMSK_OEPM(0));
    /* unmask global setup mask, xfr completion, timeout, for in and out */
	set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPMSK,
                 USBOTG_HS_DOEPMSK_STUPM_Msk   |
                 USBOTG_HS_DOEPMSK_XFRCM_Msk);
	set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPMSK,
                 USBOTG_HS_DIEPMSK_XFRCM_Msk |
                 USBOTG_HS_DIEPMSK_TOM_Msk);

    log_printf("[USB HS][RESET] initialize EP0 fifo\n");
    /* fifo is RESET, in both Core registers and EP context. The FIFO will need
     * to be reconfigured later by the driver API (typically through upper
     * reset handler */
    if (ctx->in_eps[0].configured == true) {
        // reset may happen when multiple EPs are configured, all FIFOs need to be flushed.
        usbotghs_txfifo_flush_all();
    }
# if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
    /* set TxFIFO for EP0 (in_eps[0]) */
    log_printf("[USB HS][RESET] initialize EP0 TxFIFO in device mode\n");
    if ((errcode = usbotghs_reset_epx_fifo(&(ctx->in_eps[0]))) != MBED_ERROR_NONE) {
        goto err;
    }
#else
    /* set TxFIFO for EP0 (out_eps[0]) */
    log_printf("[USB HS][RESET] initialize EP0 TxFIFO in host mode\n");
    if ((errcode = usbotghs_reset_epx_fifo(&(ctx->out_eps[0]))) != MBED_ERROR_NONE) {
        goto err;
    }
#endif
    /* flushing FIFOs */
    /* net yet confiured case, force flush only for EP0 */
    usbotghs_txfifo_flush(0);
    usbotghs_rxfifo_flush(0);

    /* reinit FIFO index and EP0 FIFO. This update ctx->fifo_idx to EP0 FIFO set only */
    log_printf("[USB HS][RESET] initialize global fifo\n");
    if ((errcode = usbotghs_init_global_fifo()) != MBED_ERROR_NONE) {
        goto err;
    }
    /* at this time, ctx->fifo_idx is set to EP0 FIFO size only. EP0 buffer are not yet configued */


    log_printf("[USB HS][RESET] set EP0 as configured\n");
    /* Now EP0 is configured. Set this information in the driver context */
    ctx->in_eps[0].configured = true;
    ctx->out_eps[0].configured = true;

    /* execute upper layer (USB Control plane) reset handler. This
     * function should always reconfigure the FIFO structure */
    log_printf("[USB HS][RESET] call usb ctrl plane reset\n");
    usbctrl_handle_reset(usb_otg_hs_dev_infos.id);
    /* Now, the upper layer should have set the driver FIFO to the correct buffer for EP0 */

    /* now that USB full stack execution is done, Enable Endpoint.
     * From now on, data can be received or sent on Endpoint 0 */
# if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
        log_printf("[USB HS][RESET] enable EP0 out (reception)\n");
        set_reg(r_CORTEX_M_USBOTG_HS_DOEPCTL(0),
                1, USBOTG_HS_DOEPCTL_EPENA);
#else
        log_printf("[USB HS][RESET] host mode TODO\n");
#endif
err:
    return errcode;
}

/*
 * Enumeration done interrupt handler
 */

/*@
  @ requires \separated(((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), &usbotghs_ctx);
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.speed;
  */
static mbed_error_t enumdone_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

	/* 1. read the OTG_HS_DSTS register to determine the enumeration speed. */
	uint8_t speed = get_reg(r_CORTEX_M_USBOTG_HS_DSTS, USBOTG_HS_DSTS_ENUMSPD);
    usbotghs_context_t *ctx = usbotghs_get_context();

	if (speed == USBOTG_HS_DSTS_ENUMSPD_HS) {
		log_printf("[USB HS][ENUMDONE] High speed enumerated !\n");
    } else if (speed == USBOTG_HS_DSTS_ENUMSPD_FS) {
        /* Detect if we are in FS mode (PHY clock at 48Mhz) */
		log_printf("[USB HS][ENUMDONE] Full speed enumerated !\n");
        ctx->speed = USBOTG_HS_SPEED_FS;
	} else {
		log_printf("[USB HS][ENUMDONE] invalid speed 0x%x !\n", speed);
        errcode = MBED_ERROR_INITFAIL;
        goto err;
    }

    /* TODO Program the MPSIZ field in OTG_HS_DIEPCTL0 to set the maximum packet size. This
     * step configures control endpoint 0.
     */
    /*
     * INFO: maximum packet size of control EP in FS and HS is not the same:
     * LS: 8 bytes
     * FS: 8, 16, 32 or 64 bytes
     * HS: 64 bytes only
     * Here we use 64 bytes, compliant with both FS and HS.
     * LS is not supported.
     */
	set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPCTL(0),
		      USBOTG_HS_DIEPCTL0_MPSIZ_64BYTES,
		      USBOTG_HS_DIEPCTL_MPSIZ_Msk(0),
		      USBOTG_HS_DIEPCTL_MPSIZ_Pos(0));

#if CONFIG_USR_DEV_USBOTGHS_DMA
	set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(0), USBOTG_HS_DOEPCTLx_EPENA_Msk);
#endif
#if 0
// XXX: still SOF IT burst to resolve...
	set_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK,
        		 USBOTG_HS_GINTMSK_SOFM_Msk);
#endif

    /* XXX: by now, no upper trigger on 'ENUMERATION DONE' event.
     * This event is received after the USB reset event when full USB
     * enumeration is done and speed selected. It does not change the
     * USB control stack state automaton. Only USB reset do this.
     */
err:
    return errcode;
}


/*
 * OUT endpoint event (reception in device mode, transmission in Host mode)
 *
 * In device mode:
 * OEPINT is executed when the RxFIFO has been fully read by the software (in RXFLVL handler)
 * In Host mode:
 * OEPINNT is executed when the TxFIFO has been flushed by the core and content sent
 */
/*@
    @ requires \separated(GHOST_out_eps+(0 .. USBOTGHS_MAX_OUT_EP-1),((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), &usbotghs_ctx,&num_ctx, ctx_list+(..));
    @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)),GHOST_out_eps[0 .. USBOTGHS_MAX_OUT_EP-1].state, usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_OUT_EP-1];
  */
static mbed_error_t oepint_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    uint16_t daint = 0;
    /* get EPx on which the event came */
    daint = (uint16_t)((read_reg_value(r_CORTEX_M_USBOTG_HS_DAINT) >> 16) & 0xff);
    /* checking current mode */
#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
        /* here, this is a 'data received' interrupt */
        uint16_t val = 0x1;
        uint8_t ep_id = 0;
        log_printf("[USBOTG][HS] handling received data\n");
        /*@
          @ loop invariant 0 <= ep_id <= USBOTGHS_MAX_OUT_EP;
          @ loop assigns errcode, daint, ep_id, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_OUT_EP-1].state,  GHOST_out_eps[0 .. USBOTGHS_MAX_OUT_EP-1].state, usbotghs_ctx.out_eps[0 .. USBOTGHS_MAX_OUT_EP-1].fifo_idx , *(register_t)((0x40040000 + 0xb08) + (int) (0 .. USBOTGHS_MAX_OUT_EP) * 0x20), *(register_t)((0x40040000 + 0xb00)  + (int) (0 .. USBOTGHS_MAX_OUT_EP) * 0x20) ,*r_CORTEX_M_USBOTG_HS_GINTMSK ;
          @ loop variant USBOTGHS_MAX_OUT_EP - ep_id;
          */
        for (ep_id = 0; ep_id < USBOTGHS_MAX_OUT_EP; ++ep_id) {
            if (daint == 0) {
                /* no more EPs to handle */
                break;
            }
            if (daint & val) {
                log_printf("[USBOTG][HS] received data on ep %d\n", ep_id);
                /* calling upper handler */
                uint32_t doepint = read_reg_value(r_CORTEX_M_USBOTG_HS_DOEPINT(ep_id));
                bool callback_to_call = false;
                bool end_of_transfer = false;
                if (doepint & USBOTG_HS_DOEPINT_STUP_Msk) {
                    log_printf("[USBOTG][HS] oepint: entering STUP\n");
		    /* @ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DOEPINT(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
		    /* @ assert r_CORTEX_M_USBOTG_HS_DOEPINT(ep_id) \in ((register_t)(USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ; */
                    set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPINT(ep_id), USBOTG_HS_DOEPINT_STUP_Msk);
                    callback_to_call = true;
                }
                /* Bit 0 XFRC: Data received complete */
                if (doepint & USBOTG_HS_DOEPINT_XFRC_Msk) {
                    log_printf("[USBOTG][HS] oepint: entering XFRC\n");
                    /* @ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DOEPINT(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
                    set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPINT(ep_id), USBOTG_HS_DOEPINT_XFRC_Msk);
                    if (ctx->out_eps[ep_id].fifo_idx == 0) {
                        /* ZLP transfer initialited from the HOST */
                        continue;
                    }
                    end_of_transfer = true;
                    /* Here we set SNAK bit to avoid receiving data before the next read cmd config.
                     * If not, a race condition can happen, if RXFLVL handler is executed *before* the EP
                     * RxFIFO is set by the upper layer */
                    /* @ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
                    set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_SNAK_Msk);
                    /* XXX: defragmentation need to be checked for others (not EP0) EPs */
                    /* always handle defragmentation on EP0 */
                    if (ctx->out_eps[ep_id].fifo_idx < ctx->out_eps[ep_id].fifo_size) {
                        if (ctx->out_eps[ep_id].state == USBOTG_HS_EP_STATE_DATA_OUT) {
                            /* BULK endpoint specific, handle variable length data stage */
                            callback_to_call = true;
                        } else {
                            /* handle defragmentation for DATA OUT packets on EP0 */
                            log_printf("[USBOTG][HS] fragment pkt %d total, %d read\n", ctx->out_eps[ep_id].fifo_size, ctx->out_eps[ep_id].fifo_idx);
                            /* @ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
                            set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_CNAK_Msk);
                        }
                    } else {
                        /* FIFO full */
                        log_printf("[USBOTG][HS] oepint for %d data size read\n", ctx->out_eps[ep_id].fifo_idx);
                        set_u8_with_membarrier(&ctx->out_eps[ep_id].state, USBOTG_HS_EP_STATE_DATA_OUT);
                        callback_to_call = true;
                    }
                }
                if (callback_to_call == true) {
                    log_printf("[USBOTG][HS] oepint: calling callback\n");

                    if (ctx->out_eps[ep_id].handler == NULL) {
                        goto err;
                    }
#ifndef __FRAMAC__
                    if (handler_sanity_check_with_panic((physaddr_t)ctx->out_eps[ep_id].handler)) {
                        goto err;
                    }
#endif
		    /*@ assert ctx->out_eps[ep_id].handler \in {usbctrl_handle_outepevent, &handler_ep} ;*/
		    /*@ calls usbctrl_handle_outepevent, handler_ep; */
                    /* In FramaC context, upper handler is my_handle_outepevent */
		    errcode = ctx->out_eps[ep_id].handler(usb_otg_hs_dev_infos.id, ctx->out_eps[ep_id].fifo_idx, ep_id);
                    ctx->out_eps[ep_id].fifo_idx = 0;
                    if (end_of_transfer == true && ep_id == 0) {
		      /* We synchronously handle CNAK only for EP0 data. others EP are handled by dedicated upper layer
		       * class level handlers */
		      //log_printf("[USBOTG][HS] oepint: set CNAK (end of transfer)\n");
		      //set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_CNAK_Msk);
                    }
                }
                /* XXX: only if SNAK set */
                /* now that data has been handled, consider FIFO as empty */
                set_u8_with_membarrier(&(ctx->out_eps[ep_id].state), (uint8_t)USBOTG_HS_EP_STATE_IDLE);
                //@ ghost GHOST_out_eps[ep_id].state = usbotghs_ctx.out_eps[ep_id].state;
            }
            daint >>= 1;
        }
	/* @ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_GINTMSK  <=  (register_t) USB_BACKEND_MEMORY_END; */
        set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 1, USBOTG_HS_GINTMSK_OEPINT);
#else
# error "not yet supported!"
#endif
err:
    return errcode;
}

/*
 * IN endpoint event (transmission in device mode, reception in Host mode)
 *
 * In device mode:
 * IEPINNT is executed when the TxFIFO has been flushed by the core and content sent
 * In Host mode:
 * IEPINT is executed when the RxFIFO has been fully read by the software (in RXFLVL handler)
 */
/*@
  @ requires \separated(GHOST_in_eps + (0 .. USBOTGHS_MAX_IN_EP - 1),((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)),   (usbctrl_context_t *)ctx_list + (0..1),&num_ctx);
  @ assigns GHOST_in_eps[0 .. USBOTGHS_MAX_IN_EP - 1].state, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.in_eps[0 .. USBOTGHS_MAX_IN_EP-1];
  */
static mbed_error_t iepint_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    uint16_t daint = 0;
    uint32_t diepintx = 0;
    /* get EPx on which the event came */
    daint = (uint16_t)(read_reg_value(r_CORTEX_M_USBOTG_HS_DAINT) & 0xff);
    /* checking current mode */
#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
        /*
         * An event rose for one or more IN EPs.
         * First, for each EP, we handle driver level events (NAK, errors, etc.)
         * if there is upper layer that need to be executed, we handle it.
         */
        uint16_t val = 0x1;
        uint8_t ep_id = 0;
        /*@
          @ loop invariant 0 <= ep_id <= USBOTGHS_MAX_IN_EP;
	  @ loop assigns ep_id, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.in_eps[0 .. USBOTGHS_MAX_IN_EP-1], daint,errcode,diepintx,GHOST_in_eps[0 .. USBOTGHS_MAX_IN_EP - 1].state;
          @ loop variant USBOTGHS_MAX_IN_EP - ep_id;
	*/

	// @ loop assigns ep_id, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx.in_eps[0 .. USBOTGHS_MAX_IN_EP-1].core_txfifo_empty,usbotghs_ctx.in_eps[0 .. USBOTGHS_MAX_IN_EP-1].fifo_idx,usbotghs_ctx.in_eps[0 .. USBOTGHS_MAX_IN_EP-1].fifo_lck,usbotghs_ctx.in_eps[0 .. USBOTGHS_MAX_IN_EP-1].fifo, GHOST_in_eps[0 .. USBOTGHS_MAX_IN_EP-1].state, usbotghs_ctx.in_eps[0 .. USBOTGHS_MAX_IN_EP-1].state, daint,errcode,diepintx;
	for (ep_id = 0; ep_id < USBOTGHS_MAX_IN_EP; ++ep_id) {
            if (daint == 0) {
                /* no more EPs to handle */
                break;
            }
            if (daint & val) {
                /* an iepint for this EP is active */
                log_printf("[USBOTG][HS] iepint: ep %d\n", ep_id);
                /*
                 * Get back DIEPINTx for this EP
                 */
		 /*@ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
		/*@ assert 0<= ep_id < USBOTGHS_MAX_IN_EP ; */
                diepintx = read_reg_value(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id));

                /* Bit 7 TXFE: Transmit FIFO empty */
                if (diepintx & USBOTG_HS_DIEPINT_TOC_Msk) {
		  /*@ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
		    set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_TXFE_Msk);
                    ctx->in_eps[ep_id].core_txfifo_empty = true;
                    log_printf("[USBOTG][HS] iepint: ep %d: TxFifo empty\n", ep_id);
                }

                /* Bit 6 INEPNE: IN endpoint NAK effective */
                if (diepintx & USBOTG_HS_DIEPINT_INEPNE_Msk) {
		   /*@ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
                    set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_INEPNE_Msk);
                    log_printf("[USBOTG][HS] iepint: ep %d: NAK effective\n", ep_id);
                }

                /* Bit 4 ITTXFE: IN token received when TxFIFO is empty */
                if (diepintx & USBOTG_HS_DIEPINT_ITTXFE_Msk) {
		   /*@ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
		  set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_ITTXFE_Msk);
		  log_printf("[USBOTG][HS] iepint: ep %d: token rcv when fifo empty\n", ep_id);
                }

                /* Bit 3 TOC: Timeout condition */
                if (diepintx & USBOTG_HS_DIEPINT_TOC_Msk) {
		   /*@ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
                    set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_TOC_Msk);
                    log_printf("[USBOTG][HS] iepint: ep %d: timeout cond\n", ep_id);
                }

                /* bit 1 EPDISD: Endpoint disabled interrupt */
                if (diepintx & USBOTG_HS_DIEPINT_EPDISD_Msk) {
		   /*@ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
		  set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_EPDISD_Msk);
		  log_printf("[USBOTG][HS] iepint: ep %d: EP disabled\n", ep_id);
		  /* Now the endpiont is really disabled
		   * We should update enpoint status
		   */
                }

                /* Bit 0 XFRC: Transfer completed interrupt */
                if (diepintx & USBOTG_HS_DIEPINT_XFRC_Msk) {
		   /*@ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
		  set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_XFRC_Msk);

		  log_printf("[USBOTG][HS] iepint: ep %d: transfert completed\n", ep_id);

                    /* inform upper layer only on end of effetvive transfer. A transfer may be
                     * the consequence of multiple FIFO flush, depending on the transfer size and
                     * the FIFO size */
                    if (ctx->in_eps[ep_id].state == USBOTG_HS_EP_STATE_DATA_IN) {
                        if (ctx->in_eps[ep_id].fifo_idx < ctx->in_eps[ep_id].fifo_size) {

                            log_printf("[USBOTG][HS] iepint: ep %d: still in fragmented transfer (%d on %d), continue...\n", ep_id, ctx->in_eps[ep_id].fifo_idx, ctx->in_eps[ep_id].fifo_size);
                            /* still in fragmentation transfer. We need to start a new
                             * transmission of the bigger size between mpsize and residual size
                             * in order to finish the current transfer. The EP state is untouched */
                            /* 1. Configure the endpoint to specify the amount of data to send, at
                             * most MPSize */
                            uint32_t datasize = ctx->in_eps[ep_id].fifo_size - ctx->in_eps[ep_id].fifo_idx;
                            if (datasize > ctx->in_eps[ep_id].mpsize) {
                                datasize = ctx->in_eps[ep_id].mpsize;
                            }
                            /*@ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
                            set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),
                                    1,
                                    USBOTG_HS_DIEPTSIZ_PKTCNT_Msk(ep_id),
                                    USBOTG_HS_DIEPTSIZ_PKTCNT_Pos(ep_id));
                            set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id),
                                    datasize,
                                    USBOTG_HS_DIEPTSIZ_XFRSIZ_Msk(ep_id),
                                    USBOTG_HS_DIEPTSIZ_XFRSIZ_Pos(ep_id));
                            /*@ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id)  <=  (register_t) USB_BACKEND_MEMORY_END; */
                            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id),
                                    USBOTG_HS_DIEPCTL_CNAK_Msk | USBOTG_HS_DIEPCTL_EPENA_Msk);
                            /* 2. write data to fifo */
                            usbotghs_write_epx_fifo(datasize, ep_id);
                        } else {
                            /* now EP is idle */
                            set_u8_with_membarrier(&(ctx->in_eps[ep_id].state), (uint8_t)USBOTG_HS_EP_STATE_IDLE);
                            //@ ghost GHOST_in_eps[ep_id].state = usbotghs_ctx.in_eps[ep_id].state;
                            /* inform libctrl of transfert complete */


                            if (ctx->in_eps[ep_id].handler == NULL) {
                                goto err;
                            }
                            /*@ assert ctx->in_eps[ep_id].handler != \null; */
#ifndef __FRAMAC__
                            if (handler_sanity_check((physaddr_t)ctx->in_eps[ep_id].handler)) {
                                goto err;
                            }
#endif
                            /*@ assert ctx->in_eps[ep_id].handler \in { &handler_ep}; */
                            /*@ calls  handler_ep; */
                            /* In FramaC context, upper handler is my_handle_inepevent */
                            errcode = ctx->in_eps[ep_id].handler(usb_otg_hs_dev_infos.id, ctx->in_eps[ep_id].fifo_idx, ep_id);
                            ctx->in_eps[ep_id].fifo = 0;
                            ctx->in_eps[ep_id].fifo_idx = 0;
                            ctx->in_eps[ep_id].fifo_size = 0;
                        }
                    } else {
                        log_printf("[USBOTGHS] EP %d not in DATA_IN state ???\n", ep_id);
                        /* the EP is only set as IDLE to inform the send process
                         * that the FIFO content is effectively sent */
                        /* clear current FIFO, now that content is sent */
                        set_u8_with_membarrier(&(ctx->in_eps[ep_id].state), (uint8_t)USBOTG_HS_EP_STATE_IDLE);
                        //@ ghost GHOST_in_eps[ep_id].state = usbotghs_ctx.in_eps[ep_id].state;
                    }
                }
                /* now that transmit is complete, set ep state as IDLE */
                /* calling upper handler, transmitted size read from DIEPSTS */
            }
            daint >>= 1;
        }
	/*@ assert  (register_t) USB_BACKEND_MEMORY_BASE <=r_CORTEX_M_USBOTG_HS_GINTMSK  <=  (register_t) USB_BACKEND_MEMORY_END; */
        set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 1, USBOTG_HS_GINTMSK_IEPINT);
#else
# error "not yet supported!"
#endif
    /* calling upper handler... needed ? */
err:
    return errcode;
}

/*
 * RXFLV handler, This interrupt is executed when the core as written a complete packet in the RxFIFO.
 *
 * It is hard, here to define complex function contracts, as behaviors depend on volative values (registers value), which,
 * by essence, can't be considered as a precondition check.
 * As a consequence, we only defines the memory separation contsraints and the worst impact (globals updates) of the function.
 */
/*@
  @ requires \separated(GHOST_out_eps+(0 .. USBOTGHS_MAX_OUT_EP - 1),((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), &usbotghs_ctx,&num_ctx, ctx_list+(..));
  @ assigns GHOST_out_eps[0 .. USBOTGHS_MAX_OUT_EP - 1].state, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx;
  */
static mbed_error_t rxflvl_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
	uint32_t grxstsp;
	pkt_status_t pktsts;
	data_pid_t dpid;
	uint16_t bcnt;
#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
	uint8_t epnum = 0; /* device case */
#else
	uint8_t chnum = 0; /* host case */
#endif
	uint32_t size;
    usbotghs_context_t *ctx;


   	/* 1. Mask the RXFLVL interrupt (in OTG_HS_GINTSTS) by writing to RXFLVL = 0
     * (in OTG_HS_GINTMSK),  until it has read the packet from the receive FIFO
     */
	set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 0, USBOTG_HS_GINTMSK_RXFLVLM);

 	/* 2. Read the Receive status pop register */
    grxstsp = read_reg_value(r_CORTEX_M_USBOTG_HS_GRXSTSP);

    ctx = usbotghs_get_context();
    /* @ assert \valid(ctx); */

    log_printf("[USBOTG][HS] Rxflvl handler\n");

    /* what is our mode (Host or Dev) ? Set corresponding variables */
#if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
            pktsts.devsts = USBOTG_HS_GRXSTSP_GET_STATUS(grxstsp);
            epnum = USBOTG_HS_GRXSTSP_GET_EPNUM(grxstsp);
#else
            pktsts.hoststs = USBOTG_HS_GRXSTSP_GET_STATUS(grxstsp);
            chnum = USBOTG_HS_GRXSTSP_GET_CHNUM(grxstsp);
#endif
	dpid = USBOTG_HS_GRXSTSP_GET_DPID(grxstsp);
	bcnt =  USBOTG_HS_GRXSTSP_GET_BCNT(grxstsp);
	size = 0;
    if (epnum >= USBOTGHS_MAX_OUT_EP) {
        log_printf("[USBOTG][HS] invalid register value for epnum ! (fault injection ?)\n");
        errcode = MBED_ERROR_UNKNOWN;
        goto err;
    }
    /*@ assert 0 <= epnum < USBOTGHS_MAX_OUT_EP; */
    if (ctx->out_eps[epnum].configured != true) {
        log_printf("[USBOTG][HS] invalid register value for epnum ! (fault injection ?)\n");
        errcode = MBED_ERROR_UNKNOWN;
        goto err;
    }

#if CONFIG_USR_DRV_USBOTGHS_DEBUG
# if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
        log_printf("EP:%d, PKTSTS:%x, BYTES_COUNT:%x,  DATA_PID:%x\n", epnum, pktsts.devsts, bcnt, dpid);
# else
        log_printf("CH:%d, PKTSTS:%x, BYTES_COUNT:%x,  DATA_PID:%x\n", chnum, pktsts.hoststs, bcnt, dpid);
# endif
#endif
    /* 3. If the received packet’s byte count is not 0, the byte count amount of data
     * is popped from the receive Data FIFO and stored in memory. If the received packet
     * byte count is 0, no data is popped from the receive data FIFO.
     *
     *   /!\ Reading an empty receive FIFO can result in undefined core behavior.
     */
# if CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE
        /* 4. The receive FIFO’s packet status readout indicates one of the following: */
        switch (pktsts.devsts) {
            case PKT_STATUS_GLOBAL_OUT_NAK:
                {
                    if (epnum != USBOTG_HS_EP0) {
                        errcode = MBED_ERROR_UNSUPORTED_CMD;
                        goto err;
                    }
                    log_printf("[USB HS][RXFLVL] EP%d Global OUT NAK effective\n", epnum);
                    ctx->gonak_active = true;
                    set_u8_with_membarrier(&ctx->out_eps[epnum].state, USBOTG_HS_EP_STATE_IDLE);
                    //@ ghost GHOST_out_eps[epnum].state = usbotghs_ctx.out_eps[epnum].state;
                    break;
                }
            case PKT_STATUS_OUT_DATA_PKT_RECV:
                {
                    log_printf("[USB HS][RXFLVL] EP%d OUT Data PKT (size %d) Recv\n", epnum, bcnt);

                    /* error cases first */
                    if (ctx->out_eps[epnum].configured != true)
                    {
                        log_printf("[USB HS][RXFLVL] EP%d OUT Data PKT on invalid EP!\n", epnum);
                        /* to clear RXFLVL IT, we must read from FIFO. read to garbage here */
                        if (bcnt > 0) {
                            usbotghs_rxfifo_flush(epnum);
                        }
                        errcode = MBED_ERROR_INVSTATE;
                        goto err;
                    }
                    if (ctx->out_eps[epnum].state == USBOTG_HS_EP_STATE_SETUP) {
                        /* associated oepint not yet executed, return NYET to host */
                        log_printf("[RXFLVL] recv DATA while in STUP mode!\n");
                        if (bcnt > 0) {
                            usbotghs_rxfifo_flush(epnum);
                        }
                        usbotghs_endpoint_set_nak(epnum, USBOTG_HS_EP_DIR_OUT);
                        errcode = MBED_ERROR_INVSTATE;
                        goto err;
                    }


                    /* if bcnt == 0, nothing to read from the FIFO */
                    if (bcnt == 0) {
                        goto check_variable_length_transfer;
                    }

                    log_printf("[USB HS][RXFLVL] EP%d OUT Data PKT (size %d) Read EPx FIFO\n", epnum, bcnt);

                    /*@ assert usbotghs_ctx.out_eps[epnum].configured == \true; */
                    if (usbotghs_read_epx_fifo(bcnt, epnum) != MBED_ERROR_NONE) {
                        /* empty fifo on error */
                        usbotghs_rxfifo_flush(epnum);
                        usbotghs_endpoint_stall(epnum, USBOTG_HS_EP_DIR_OUT);
                    }
                    set_u8_with_membarrier(&(ctx->out_eps[epnum].state), (uint8_t)USBOTG_HS_EP_STATE_DATA_OUT_WIP);
                    //@ ghost GHOST_out_eps[epnum].state = usbotghs_ctx.out_eps[epnum].state;
                    if (epnum == USBOTG_HS_EP0) {
                        if (ctx->out_eps[epnum].fifo_idx < ctx->out_eps[epnum].fifo_size) {
                            /* rise oepint to permit refragmentation at oepint layer */
                            set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(epnum), 1, USBOTG_HS_DOEPTSIZ_PKTCNT_Msk(epnum), USBOTG_HS_DOEPTSIZ_PKTCNT_Pos(epnum));
                            set_reg_value(r_CORTEX_M_USBOTG_HS_DOEPTSIZ(epnum), ctx->out_eps[epnum].mpsize, USBOTG_HS_DOEPTSIZ_XFRSIZ_Msk(epnum), USBOTG_HS_DOEPTSIZ_XFRSIZ_Pos(epnum));
                        } else {
                            usbotghs_endpoint_set_nak(epnum, USBOTG_HS_EP_DIR_OUT);
                        }
                    }
check_variable_length_transfer:
                    /* handling variable length transfert (for BULK only, see chap. 5.8.3)
                     * When receiving ZLP after mpsize multiple data OR
                     * receiving data smaller than MPSize, this means that this is the last DATA packet (see
                     * Data variable length transaction, USB 2.0 std protocol).
                     * We consider variable length data transfer not supported on EP0 */
                    if ((bcnt < ctx->out_eps[epnum].mpsize) ||
                            (bcnt == 0 && ctx->out_eps[epnum].fifo_idx >= ctx->out_eps[epnum].mpsize))
                    {
                        /* only for BULK endpoints, says the USB standard */
                        if (ctx->out_eps[epnum].type != USBOTG_HS_EP_TYPE_ISOCHRONOUS) {
                            set_u8_with_membarrier(&ctx->out_eps[epnum].state, USBOTG_HS_EP_STATE_DATA_OUT);
                            //@ ghost GHOST_out_eps[epnum].state = usbotghs_ctx.out_eps[epnum].state;
                        }
                    }
                    goto err;
                    break;
                }
            case PKT_STATUS_OUT_TRANSFER_COMPLETE:
                {
                    log_printf("[USB HS][RXFLVL] OUT Transfer complete on EP %d\n", epnum);
                    if (ctx->out_eps[epnum].configured != true) /* which state on OUT TRSFER Complete ? */
                    {
                        log_printf("[USB HS][RXFLVL] OUT Data PKT on invalid EP!\n");
                        errcode = MBED_ERROR_INVSTATE;
                        goto err;
                    }
                    //set_u8_with_membarrier(&(ctx->out_eps[epnum].state), (uint8_t)USBOTG_HS_EP_STATE_DATA_OUT);
                    //@ ghost GHOST_out_eps[epnum].state = usbotghs_ctx.out_eps[epnum].state;
                    break;
                }
            case PKT_STATUS_SETUP_TRANS_COMPLETE:
                {
                    log_printf("[USB HS][RXFLVL] Setup Transfer complete on ep %d (bcnt %d)\n", epnum, bcnt);
                    if (epnum != USBOTG_HS_EP0 || bcnt != 0) {
                        errcode = MBED_ERROR_UNSUPORTED_CMD;
                        goto err;
                    }
                    /* setup transfer complete, no wait oepint to handle this */
                    set_u8_with_membarrier(&(ctx->out_eps[epnum].state), (uint8_t)USBOTG_HS_EP_STATE_SETUP);
                    //@ ghost GHOST_out_eps[epnum].state = usbotghs_ctx.out_eps[epnum].state;
                    break;
                }
            case PKT_STATUS_SETUP_PKT_RECEIVED:
                {
                    log_printf("[USB HS][RXFLVL] Setup pkt (%dB) received on ep %d\n", bcnt, epnum);
                    if (bcnt == 0) {
                        /* ZLP, nothing to do. */
                        goto err;
                    }
                    /*@ assert bcnt > 0; */
                    if (epnum != USBOTG_HS_EP0) {
                        usbotghs_rxfifo_flush(epnum);
                        usbotghs_endpoint_set_nak(epnum, USBOTG_HS_EP_DIR_OUT);
                        errcode = MBED_ERROR_UNSUPORTED_CMD;
                        goto err;
                    } else if (ctx->out_eps[epnum].state == USBOTG_HS_EP_STATE_SETUP) {
                        /* associated oepint not yet executed, return NYET to host */
                        usbotghs_rxfifo_flush(epnum);
                        usbotghs_endpoint_set_nak(epnum, USBOTG_HS_EP_DIR_OUT);
                        errcode = MBED_ERROR_INVSTATE;
                        goto err;
                    }
                    /* INFO: here, We don't check the setup pkt size, this is under the responsability of the
                     * control plane, as the setup pkt size is USB-standard defined, not driver specific */
                    if (usbotghs_read_epx_fifo(bcnt, epnum)) {
                        /* empty fifo on error */
                        usbotghs_rxfifo_flush(epnum);
                        usbotghs_endpoint_stall(epnum, USBOTG_HS_EP_DIR_OUT);
                    }
                    /* After this, the Data stage begins. A Setup stage done should be received, which triggers
                     * a Setup interrupt */
                    set_u8_with_membarrier(&(ctx->out_eps[epnum].state), (uint8_t)USBOTG_HS_EP_STATE_SETUP_WIP);
                    //@ ghost GHOST_out_eps[epnum].state = usbotghs_ctx.out_eps[epnum].state;
                    break;
                }
            default:
                log_printf("[USB HS][RXFLVL] RXFLVL bad status %x!", pktsts.devsts);
                break;
        }

err:
#else
        /* TODO: handle Host mode RXFLVL behavior */
#endif
	set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 1, USBOTG_HS_GINTMSK_RXFLVLM);
    return errcode;
}


/*
 * Start-offrame event (new USB frame)
 */

/*@
  @ assigns \nothing;
  */
static mbed_error_t sof_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

/*@
  @ assigns \nothing;
  */
static mbed_error_t otg_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

/*@
  @ assigns \nothing;
  */
static mbed_error_t mmism_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

/*
 * Early suspend handler. Received when an Idle state has been
 * detected on the USB for 3ms.
 */
/*@
  @ assigns \nothing;
  */
static mbed_error_t esuspend_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    usbctrl_handle_earlysuspend(usb_otg_hs_dev_infos.id);

    return errcode;
}

/*
 * USB suspend handler. Received when there is no activity on the data
 * lines (including EP0) for a period of 3ms after an early suspend event.
 * The device should enter SUSPEND state
 */
/*@
  @ assigns \nothing;
  */
static mbed_error_t ususpend_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* we must inform the control layer that we should enter suspend state as
     * no event has been received on USB. */
    usbctrl_handle_usbsuspend(usb_otg_hs_dev_infos.id);

    return errcode;
}

/*
 * USB resume/wakeup handler. Received when the host restart its activity
 * after a suspension (see ususpend).
 */
/*@
  @ assigns \nothing;
  */
static mbed_error_t resume_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* we must inform the control layer that we should enter suspend state as
     * no event has been received on USB. */
    usbctrl_handle_wakeup(usb_otg_hs_dev_infos.id);

    return errcode;
}


/************************************************
 * About ISR handlers global table
 */
typedef mbed_error_t (*usb_otg_hs_isr_handler_t)(void);

/*
 * This table handle the overall possible ISR handlers, ordered by their bit identifier in the
 * INTSTS and GINTMSK registers
 */
static const usb_otg_hs_isr_handler_t usb_otg_hs_isr_handlers[32] = {
    default_handler,    /*< Current Mode of Operation  */
    mmism_handler,      /*< Mode mismatch */
    otg_handler,        /*< OTG interrupt */
    sof_handler,        /*< Start of Frame */
    rxflvl_handler,     /*< RxFifo non-empty */
    default_handler,    /*< Non-periodic TxFIFO empty */
    default_handler,    /*< Global IN NAK effective */
    default_handler,    /*< Global OUT NAK effective*/
    reserved_handler,   /*< Reserved */
    reserved_handler,   /*< Reserved */
    esuspend_handler,   /*< Early suspend */
    ususpend_handler,   /*< USB Suspend */
    reset_handler,      /*< Reset */
    enumdone_handler,   /*< Speed enumeration done */
    default_handler,    /*< Isochronous OUT pkt dropped */
    default_handler,    /*< End of periodic frame */
    default_handler,    /*< Reserved */
    default_handler,    /*< Endpoint mismatch */
    iepint_handler,     /*< IN Endpoint event */
    oepint_handler,     /*< OUT Endpoint event */
    default_handler,    /*< Incomplete Isochronous IN transfer */
    default_handler,    /*< Incomplete periodic transfer */
    reserved_handler,   /*< Reserved */
    reserved_handler,   /*< Reserved */
    default_handler,    /*< Host port event (Host mode) */
    default_handler,    /*< Host channels event (Host mode) */
    default_handler,    /*< Periodic TxFIFO empty (Host mode) */
    reserved_handler,   /*< Reserved */
    default_handler,    /*< Connector ID status change */
    default_handler,    /*< Disconnect event (Host mode) */
    default_handler,    /*< Session request/new session event*/
    resume_handler,    /*< Resume/Wakeup event */
};

/************************************************
 * About ISR dispatchers
 */

/*@
  @ requires \separated(((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), &usbotghs_ctx);
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx;
  */
void USBOTGHS_IRQHandler(uint8_t interrupt __attribute__((unused)),
                         uint32_t sr,
                         uint32_t dr)
{
	uint8_t i;
	uint32_t intsts = sr;
	uint32_t intmsk = dr;

	if (intsts & USBOTG_HS_GINTSTS_CMOD_Msk){
		log_printf("[USB HS] Int in Host mode !\n");
	}
    uint32_t val = intsts;
    val &= intmsk;

    /*
     * Here, for each status flag active, execute the corresponding handler if
     * the global interrupt mask is also enabled
     */
    /*@
      @ loop invariant 0 <= i <= 32;
      @ loop assigns val, i, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx;
      @ loop variant 32 - i;
      */
	for (i = 0; i < 32; i++) {
		/* Below code is equivalent to
         * calculating (!(intsts & ((uint32_t)1 << i)) || !(intmsk & ((uint32_t)1 << i)))
         */
        if (val == 0) {
            break;
        }
        if (val & 1)
        {
            /*@ assert i < 32; */
#if CONFIG_USR_DRV_USBOTGHS_DEBUG
            /* out of __FRAMAC__ case */
            usbotghs_int_cnt[i]++;
#endif
            /* INFO: as log_printf is a *macro* only resolved by cpp in debug mode,
             * usbotghs_int_name is accedded only in this mode. There is no
             * invalid memory access in the other case. */

            /*@ assert usb_otg_hs_isr_handlers[i] \in
              { &default_handler, &mmism_handler, &otg_handler, &sof_handler, &rxflvl_handler, &reserved_handler, &ususpend_handler, &esuspend_handler, &reset_handler, &enumdone_handler, &iepint_handler, &oepint_handler }; */
            /*@ calls default_handler, mmism_handler, otg_handler, sof_handler, rxflvl_handler, reserved_handler, ususpend_handler, esuspend_handler, reset_handler, enumdone_handler, iepint_handler, oepint_handler; */
            usb_otg_hs_isr_handlers[i]();
        }
        val >>= 1;
    }
}

