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
/* This table is made only as a debug helper, in order to assicate the
 * interrupt identifier with a full-text name for pretty printing.
 * This consume space in the device flash memory and should be used only
 * for debug purpose.
 */
static const char *usbotghs_int_name[] = {
    "CMOD",
    "MMIS",
    "OTGINT",
    "SOF",
    "RXFLVL",
    "NPTXE",
    "GINAKEFF",
    "GONAKEFF",
    "RESERVED8",
    "RESERVED9",
    "ESUSP",
    "USBSUSP",
    "USBRST",
    "ENUMDNE",
    "ISOODRP",
    "EOPF",
    "RESERVED16",
    "EPMISM",
    "IEPINT",
    "OEPINT",
    "IISOIXFR",
    "IPXFR",
    "RESERVED22",
    "RESERVED23",
    "HPRTINT",
    "HCINTT",
    "PTXFE",
    "RESERVED27",
    "CIDSCHG",
    "DISCINT",
    "SRQINT",
    "WKUPINT",
};

static volatile uint32_t    usbotghs_int_cnt[] = { 0 };




#endif
/*
 * Generic handler, used by default.
 */
static mbed_error_t default_handler(void)
{
    return MBED_ERROR_NONE;
}

/*
 * Reserved handler, should never be executed, as interrupt flag corresponds to
 * 'Reserved' field.
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
static mbed_error_t reset_handler(void)
{
    log_printf("[USB HS][RESET] received USB Reset\n");
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
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

    log_printf("[USB HS][RESET] initialize global fifo\n");
    if ((errcode = usbotghs_init_global_fifo()) != MBED_ERROR_NONE) {
        goto err;
    }

    log_printf("[USB HS][RESET] initialize EP0 fifo\n");
    /* fifo is RESET, in both Core registers and EP context. The FIFO will need
     * to be reconfigured later by the driver API (typically through upper
     * reset handler */
    if (ctx->mode == USBOTGHS_MODE_DEVICE) {
        /* set TxFIFO for EP0 (in_eps[0]) */
        log_printf("[USB HS][RESET] initialize EP0 TxFIFO in device mode\n");
        if ((errcode = usbotghs_reset_epx_fifo(&(ctx->in_eps[0]))) != MBED_ERROR_NONE) {
            goto err;
        }
    } else {
        /* set TxFIFO for EP0 (out_eps[0]) */
        log_printf("[USB HS][RESET] initialize EP0 TxFIFO in host mode\n");
        if ((errcode = usbotghs_reset_epx_fifo(&(ctx->out_eps[0]))) != MBED_ERROR_NONE) {
            goto err;
        }
    }

    log_printf("[USB HS][RESET] set EP0 as configured\n");
    /* Now EP0 is configued. Set this information in the driver context */
    ctx->in_eps[0].configured = true;
    ctx->out_eps[0].configured = true;

    /* execute upper layer (USB Control plane) reset handler. This
     * function should always reconfigure the FIFO structure */
    log_printf("[USB HS][RESET] call usb ctrl plane reset\n");
    usbctrl_handle_reset(usb_otg_hs_dev_infos.id);

    /* now that USB full stack execution is done, Enable Endpoint.
     * From now on, data can be received or sent on Endpoint 0 */
    if (ctx->mode == USBOTGHS_MODE_DEVICE) {
        log_printf("[USB HS][RESET] enable EP0 out (reception)\n");
        set_reg(r_CORTEX_M_USBOTG_HS_DOEPCTL(0),
                1, USBOTG_HS_DOEPCTL_EPENA);
    } else {
        log_printf("[USB HS][RESET] host mode TODO\n");
    }
err:
    return errcode;
}

/*
 * Enumeration done interrupt handler
 */
static mbed_error_t enumdone_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

	/* 1. read the OTG_HS_DSTS register to determine the enumeration speed. */
	uint8_t speed = get_reg(r_CORTEX_M_USBOTG_HS_DSTS, USBOTG_HS_DSTS_ENUMSPD);
	if (speed != USBOTG_HS_DSTS_ENUMSPD_HS) {
		log_printf("[USB HS][ENUMDONE]  Wrong enum speed !\n");
        errcode = MBED_ERROR_INITFAIL;
		goto err;
	}

    /* TODO Program the MPSIZ field in OTG_HS_DIEPCTL0 to set the maximum packet size. This
     * step configures control endpoint 0.
     */
	set_reg_value(r_CORTEX_M_USBOTG_HS_DIEPCTL(0),
		      USBOTG_HS_DIEPCTL0_MPSIZ_64BYTES,
		      USBOTG_HS_DIEPCTL_MPSIZ_Msk(0),
		      USBOTG_HS_DIEPCTL_MPSIZ_Pos(0));

#if CONFIG_USR_DEV_USBOTGHS_DMA
	set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(0), USBOTG_HS_DOEPCTLx_EPENA_Msk);
#endif
	set_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK,
        		 USBOTG_HS_GINTMSK_SOFM_Msk);

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
static mbed_error_t oepint_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    uint16_t daint = 0;
    /* get EPx on which the event came */
    daint = (uint16_t)((read_reg_value(r_CORTEX_M_USBOTG_HS_DAINT) >> 16) & 0xff);
    /* checking current mode */
    if (ctx->mode == USBOTGHS_MODE_DEVICE) {
        /* here, this is a 'data received' interrupt */
        uint16_t val = 0x1;
        uint8_t ep_id = 0;
        printf("[USBOTG][HS] handling received data\n");
        for (uint8_t i = 0; i < 16; ++i) {
            if (daint & val) {
                printf("[USBOTG][HS] received data on ep %x\n", ep_id);
                /* calling upper handler */
                uint32_t doepint = read_reg_value(r_CORTEX_M_USBOTG_HS_DOEPINT(ep_id));
                set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPINT(ep_id), USBOTG_HS_DOEPINT_STUP_Msk);

                errcode = usbctrl_handle_outepevent(usb_otg_hs_dev_infos.id, ctx->out_eps[ep_id].fifo_idx, ep_id);
                if (doepint & USBOTG_HS_DOEPINT_XFRC_Msk) {
                    set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPINT(ep_id), USBOTG_HS_DOEPINT_XFRC_Msk);
                    if (ep_id != 0) {
                        /* WHERE in the datasheet ? In disabling an OUT ep (p1360) */
                        set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_SNAK_Msk);
                        set_reg_bits(r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id), USBOTG_HS_DOEPCTL_CNAK_Msk);
                    }
                }
                ctx->out_eps[ep_id].state = USBOTG_HS_EP_STATE_IDLE;
            }
            ep_id++;
            val = val << 1;
        }
        set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 1, USBOTG_HS_GINTMSK_OEPINT);
    } else {
        /* TODO: (FIXME host mode not working yet) here, this is a 'end of transmission' interrupt. Let's handle each
         * endpoint for which the interrupt rised */
        uint16_t val = 0x1;
        uint8_t ep_id = 0;
        for (uint8_t i = 0; i < 16; ++i) {
            if (daint & val) {
                /* an iepint for this EP is active */
                log_printf("[USBOTG][HS] iepint: ep %d\n", ep_id);
                /* now that transmit is complete, set ep state as IDLE */
                /* calling upper handler, transmitted size read from DOEPSTS */
                errcode = usbctrl_handle_outepevent(usb_otg_hs_dev_infos.id, ctx->out_eps[ep_id].fifo_idx, ep_id);
                ctx->out_eps[ep_id].state = USBOTG_HS_EP_STATE_IDLE;
            }
            ep_id++;
            val = val << 1;
        }
    }
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
static mbed_error_t iepint_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbotghs_context_t *ctx = usbotghs_get_context();
    uint16_t daint = 0;
    uint32_t diepintx = 0;
    /* get EPx on which the event came */
    daint = (uint16_t)(read_reg_value(r_CORTEX_M_USBOTG_HS_DAINT) & 0xff);
    /* checking current mode */
    if (ctx->mode == USBOTGHS_MODE_DEVICE) {
        /*
         * An event rose for one or more IN EPs.
         * First, for each EP, we handle driver level events (NAK, errors, etc.)
         * if there is upper layer that need to be executed, we handle it.
         */
        uint16_t val = 0x1;
        uint8_t ep_id = 0;
        for (uint8_t i = 0; i < 16; ++i) {
            if (daint & val) {
                /* an iepint for this EP is active */
                log_printf("[USBOTG][HS] iepint: ep %d\n", ep_id);
                /*
                 * Get back DIEPINTx for this EP
                 */
                diepintx = read_reg_value(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id));

                if (ep_id == 0) {
                    uint32_t diepint0 = read_reg_value(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id));
                    /* Bit 7 TXFE: Transmit FIFO empty */
                    if (diepint0 & USBOTG_HS_DIEPINT_TOC_Msk) {
                        set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_TXFE_Msk);
                        ctx->in_eps[ep_id].core_txfifo_empty = true;
                        ctx->in_eps[ep_id].fifo_idx = 0;
                        ctx->in_eps[ep_id].fifo_lck = false;
                    }

                    /* Bit 6 INEPNE: IN endpoint NAK effective */
                    if (diepint0 & USBOTG_HS_DIEPINT_INEPNE_Msk) {
                        set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_INEPNE_Msk);
                    }

                    /* Bit 4 ITTXFE: IN token received when TxFIFO is empty */
                    if (diepint0 & USBOTG_HS_DIEPINT_ITTXFE_Msk) {
                        set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_ITTXFE_Msk);
                    }

                    /* Bit 3 TOC: Timeout condition */
                    if (diepint0 & USBOTG_HS_DIEPINT_TOC_Msk) {
                        set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_TOC_Msk);
                    }

                    /* bit 1 EPDISD: Endpoint disabled interrupt */
                    if (diepint0 & USBOTG_HS_DIEPINT_EPDISD_Msk) {
                        set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_EPDISD_Msk);
                        /* Now the endpiont is really disabled
                         * We should update enpoint status
                         */
                    }

                    /* Bit 0 XFRC: Transfer completed interrupt */
                    if (diepint0 & USBOTG_HS_DIEPINT_XFRC_Msk) {
                        set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_XFRC_Msk);
                        ctx->in_eps[ep_id].state = USBOTG_HS_EP_STATE_IDLE;
                        /* Our callback */
                    }
                } else {
                    if (daint & ep_id) {
                        uint32_t diepint = read_reg_value(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id));

                        /* Bit 7 TXFE: Transmit FIFO empty */
                        if (diepint & USBOTG_HS_DIEPINT_TOC_Msk) {
                            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_TXFE_Msk);
                            ctx->in_eps[ep_id].core_txfifo_empty = true;
                        }

                        /* Bit 6 INEPNE: IN endpoint NAK effective */
                        if (diepint & USBOTG_HS_DIEPINT_INEPNE_Msk) {
                            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_INEPNE_Msk);
                        }

                        /* Bit 4 ITTXFE: IN token received when TxFIFO is empty */
                        if (diepint & USBOTG_HS_DIEPINT_ITTXFE_Msk) {
                            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_ITTXFE_Msk);
                        }

                        /* Bit 3 TOC: Timeout condition */
                        if (diepint & USBOTG_HS_DIEPINT_TOC_Msk) {
                            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_TOC_Msk);
                        }

                        /* bit 1 EP2DISD: Endpoint disabled interrupt */
                        if (diepint & USBOTG_HS_DIEPINT_EPDISD_Msk) {
                            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_EPDISD_Msk);
                        }

                        /* Bit 2 XFRC: Transfer completed interrupt */
                        if (diepint & USBOTG_HS_DIEPINT_XFRC_Msk) {
                            set_reg_bits(r_CORTEX_M_USBOTG_HS_DIEPINT(ep_id), USBOTG_HS_DIEPINT_XFRC_Msk);
                            ctx->in_eps[ep_id].fifo_idx = 0;
                            ctx->in_eps[ep_id].fifo_lck = false;
                            ctx->in_eps[ep_id].state = USBOTG_HS_EP_STATE_IDLE;
                            /* Our callback */
                        }

                    }
                }

#if 0
                /* handle various events of the current IN EP */
                /* TxFIFO (half) empty ? */
                if (diepintx & USBOTG_HS_DIEPINT_TXFE_Msk) {
                    /* set TxFIFO has (half) empty */
                    ctx->in_eps[ep_id].core_txfifo_empty = true;
#if CONFIG_USR_DEV_USBOTGHS_TRIGER_XMIT_ON_HALF
                    ctx->in_eps[ep_id].state = USBOTG_HS_EP_STATE_DATA_OUT
#endif
                }
                /* transmission terminated ? */
                if (diepintx & USBOTG_HS_DIEPINT_XFRC_Msk) {
                    errcode = usbctrl_handle_inepevent(usb_otg_hs_dev_infos.id, ctx->in_eps[ep_id].fifo_idx, ep_id);
                    ctx->in_eps[ep_id].core_txfifo_empty = true;
                    ctx->in_eps[ep_id].state = USBOTG_HS_EP_STATE_IDLE;
                }
                /* TODO: status & error flags (overrun, NAK... */
#endif

                /* now that transmit is complete, set ep state as IDLE */
                /* calling upper handler, transmitted size read from DIEPSTS */
            }
            ep_id++;
            val = val << 1;
        }
        set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 1, USBOTG_HS_GINTMSK_IEPINT);
    } else {
        /* here, this is a 'data received' interrupt  (Host mode) */
        uint16_t val = 0x1;
        uint8_t ep_id = 0;
        for (uint8_t i = 0; i < 16; ++i) {
            if (daint & val) {
                /* an iepint for this EP is active */
                log_printf("[USBOTG][HS] iepint: ep %d\n", ep_id);
                /* calling upper handler */
                errcode = usbctrl_handle_outepevent(usb_otg_hs_dev_infos.id, ctx->in_eps[ep_id].fifo_idx, ep_id);
                ctx->in_eps[ep_id].state = USBOTG_HS_EP_STATE_IDLE;
            }
            ep_id++;
            val = val << 1;
        }
    }
    /* calling upper handler */
    return errcode;
}

/*
 * RXFLV handler, This interrupt is executed when the core as written a complete packet in the RxFIFO.
 */
static mbed_error_t rxflvl_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
	uint32_t grxstsp;
	pkt_status_t pktsts;
	data_pid_t dpid;
	uint16_t bcnt;
	uint8_t epnum = 0; /* device case */
	uint8_t chnum = 0; /* host case */
	uint32_t size;
    usbotghs_context_t *ctx;

    ctx = usbotghs_get_context();

   	/* 2. Mask the RXFLVL interrupt (in OTG_HS_GINTSTS) by writing to RXFLVL = 0
     * (in OTG_HS_GINTMSK),  until it has read the packet from the receive FIFO
     */
	set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 0, USBOTG_HS_GINTMSK_RXFLVLM);

 	/* 1. Read the Receive status pop register */
    grxstsp = read_reg_value(r_CORTEX_M_USBOTG_HS_GRXSTSP);

    /* what is our mode (Host or Dev) ? Set corresponding variables */
    switch (ctx->mode) {
        case USBOTGHS_MODE_HOST:
            pktsts.hoststs = USBOTG_HS_GRXSTSP_GET_STATUS(grxstsp);
            chnum = USBOTG_HS_GRXSTSP_GET_CHNUM(grxstsp);
            break;
        case USBOTGHS_MODE_DEVICE:
            pktsts.devsts = USBOTG_HS_GRXSTSP_GET_STATUS(grxstsp);
            epnum = USBOTG_HS_GRXSTSP_GET_EPNUM(grxstsp);
            break;
        default:
            errcode = MBED_ERROR_INVSTATE;
            goto err;
    }
	dpid = USBOTG_HS_GRXSTSP_GET_DPID(grxstsp);
	bcnt =  USBOTG_HS_GRXSTSP_GET_BCNT(grxstsp);
	size = 0;
#if CONFIG_USR_DRV_USBOTGHS_DEBUG
    if (ctx->mode == USBOTGHS_MODE_DEVICE) {
        log_printf("EP:%d, PKTSTS:%x, BYTES_COUNT:%x,  DATA_PID:%x\n", epnum, pktsts.devsts, bcnt, dpid);
    } else if (ctx->mode == USBOTGHS_MODE_HOST) {
        log_printf("CH:%d, PKTSTS:%x, BYTES_COUNT:%x,  DATA_PID:%x\n", chnum, pktsts.hoststs, bcnt, dpid);
    }
#endif
    /* 3. If the received packet’s byte count is not 0, the byte count amount of data
     * is popped from the receive Data FIFO and stored in memory. If the received packet
     * byte count is 0, no data is popped from the receive data FIFO.
     *
     *   /!\ Reading an empty receive FIFO can result in undefined core behavior.
     */
    switch (ctx->mode) {
        case USBOTGHS_MODE_DEVICE:
        {
            /* 4. The receive FIFO’s packet status readout indicates one of the following: */
            switch (pktsts.devsts) {
                case PKT_STATUS_GLOBAL_OUT_NAK:
                {
                    if (epnum != EP0) {
                        errcode = MBED_ERROR_UNSUPORTED_CMD;
                        goto err;
                    }
                    log_printf("[USB HS][RXFLVL] EP0 Global OUT NAK effective\n");
                    ctx->gonak_active = true;
                    ctx->out_eps[epnum].state = USBOTG_HS_EP_STATE_IDLE;
                    break;
                }
                case PKT_STATUS_OUT_DATA_PKT_RECV:
                {
                    log_printf("[USB HS][RXFLVL] EP0 OUT Data PKT Recv\n");
                    if (ctx->out_eps[epnum].configured != true ||
                        ctx->out_eps[epnum].state != USBOTG_HS_EP_STATE_DATA_OUT)
                    {
                        log_printf("[USB HS][RXFLVL] EP0 OUT Data PKT on invalid EP %d!\n", epnum);
                        /* to clear RXFLVL IT, we must read from FIFO. read to garbage here */
                        uint8_t buf[16];
                        for (; bcnt > 16; bcnt -= 16) {
                            usbotghs_read_core_fifo(&(buf[0]), 16, epnum);
                        }
                        usbotghs_read_core_fifo(&(buf[0]), bcnt, epnum);

                        errcode = MBED_ERROR_INVSTATE;
                        goto err;
                    }
                    // TODO:
#ifndef CONFIG_USR_DEV_USBOTGHS_DMA
                    usbotghs_read_epx_fifo(bcnt, &(ctx->out_eps[epnum]));
                    ctx->out_eps[epnum].state = USBOTG_HS_EP_STATE_DATA_IN;
#else
                    /* XXX: in case of DMA mode activated, the RAM FIFO recopy should be
                     * handled by the Core itself, and OEPINT executed automatically... */
                    /* Although, we may have to check the RAM buffer address and size
                     * in OEPINT and reset them */
#endif
                    break;
                }
                case PKT_STATUS_OUT_TRANSFER_COMPLETE:
                {
                    log_printf("[USB HS][RXFLVL] EP0 OUT Transfer complete on EP %d\n", epnum);
                    if (ctx->out_eps[epnum].configured != true) /* which state on OUT TRSFER Complete ? */
                    {
                        log_printf("[USB HS][RXFLVL] EP0 OUT Data PKT on invalid EP!\n");
                        errcode = MBED_ERROR_INVSTATE;
                        goto err;
                    }
                    ctx->out_eps[epnum].state = USBOTG_HS_EP_STATE_IDLE;
                    break;
                }
                case PKT_STATUS_SETUP_TRANS_COMPLETE:
                {
                    log_printf("[USB HS][RXFLVL] Setup Transfer complete on ep %d (bcnt %d)\n", epnum, bcnt);
                    if (epnum != EP0 || bcnt != 0) {
                        errcode = MBED_ERROR_UNSUPORTED_CMD;
                        goto err;
                    }
                    /* setup transfer complete, no wait oepint to handle this */
                    ctx->out_eps[epnum].state = USBOTG_HS_EP_STATE_SETUP;
                    break;
                }
                case PKT_STATUS_SETUP_PKT_RECEIVED:
                {
                    log_printf("[USB HS][RXFLVL] EP0 Setup pkt receive\n");
                    if (epnum != EP0 || dpid != DATA_PID_DATA0) {

                        uint8_t buf[16];
                        for (; bcnt > 16; bcnt -= 16) {
                            usbotghs_read_core_fifo(&(buf[0]), 16, epnum);
                        }
                        usbotghs_read_core_fifo(&(buf[0]), bcnt, epnum);

                        errcode = MBED_ERROR_UNSUPORTED_CMD;
                        goto err;
                    }
                    if (bcnt == 0) {
                        /* This is a Zero-length-packet reception, nothing to do */
                        goto err;
                    }
                    /* INFO: here, We don't check the setup pkt size, this is under the responsability of the
                     * control plane, as the setup pkt size is USB-standard defined, not driver specific */
                    usbotghs_read_epx_fifo(bcnt, &(ctx->out_eps[epnum]));
                    // TODO: read_fifo(setup_packet, bcnt, epnum);
                    /* After this, the Data stage begins. A Setup stage done should be received, which triggers
                     * a Setup interrupt */
                    ctx->out_eps[epnum].state = USBOTG_HS_EP_STATE_SETUP_WIP;
                    break;
                }
                default:
                    log_printf("RXFLVL bad status %x!", pktsts.devsts);

            }
        }
        case USBOTGHS_MODE_HOST:
        {
            /* TODO: handle Host mode RXFLVL behavior */
        }
        break;
    }
err:
	set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 1, USBOTG_HS_GINTMSK_RXFLVLM);
    /* XXX; in dev mode only, should not be required */
	//set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 1, USBOTG_HS_GINTMSK_OEPINT);
    return errcode;
}


/*
 * Start-offrame event (new USB frame)
 */
static mbed_error_t sof_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

static mbed_error_t otg_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

static mbed_error_t mmism_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

/*
 * Early suspend handler. Received when an Idle state has been
 * detected on the USB for 3ms.
 */
static mbed_error_t esuspend_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    return errcode;
}

/*
 * USB suspend handler. Received when there is no activity on the data
 * lines (including EP0) for a period of 3ms.
 */
static mbed_error_t ususpend_handler(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

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
    default_handler,    /*< Resume/Wakeup event */
};

/************************************************
 * About ISR dispatchers
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
	for (i = 0; val; i++,val>>=1) {
		/* Below code is equivalent to
         * calculating (!(intsts & ((uint32_t)1 << i)) || !(intmsk & ((uint32_t)1 << i)))
         */
        if (val & 1)
        {
#if CONFIG_USR_DRV_USBOTGHS_DEBUG
            usbotghs_int_cnt[i]++;
#endif
            /* INFO: as log_printf is a *macro* only resolved by cpp in debug mode,
             * usbotghs_int_name is accedded only in this mode. There is no
             * invalid memory access in the other case. */
            if (i != 3) {
                /* 3 is for SOF (Start Of Frame, and is too frequent, generating ISR exhausting */
                log_printf("[USB HS] IRQ Handler for event %d (%s)\n", i, usbotghs_int_name[i]);
            }
            usb_otg_hs_isr_handlers[i]();
        }
    }
}

