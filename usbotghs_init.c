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

#include "api/libusbotghs.h"
#include "usbotghs_regs.h"
#include "usbotghs.h"

#include "usbotghs_init.h"

#define TRIGGER_TXFE_ON_HALF_EMPTY 0
#define TRIGGER_TXFE_ON_FULL_EMPTY 1

/*
 * Core initialization after Power-On. This configuration must
 * be done irrespective to whatever the DWC_Core is going to be
 * configured in Host or Device Mode of Operation.
 * This initialization is common to any use.
 *
 *
 * If the cable is connected during power-up, the Current Mode of
 * Operation bit in the Core Interrupt register  (GINTSTS.CurMod)
 * reflects the mode. The DWC_otg core enters Host mode when an “A” plug is
 * connected, or Device mode when a “B” plug is connected.
 *
 * This section explains the initialization of the DWC_otg core after
 * power-on. The application must follow this initialization sequence
 * irrespective of whether the DWC_otg core is going to be configured
 * in Host or Device mode of operations. All core global registers are
 * initialized according to the core’s configuration. The parameters
 * referred to in this section are the DWC_otg configuration parameters
 * defined in the Databook.
 *
 * 1. Read the User Hardware Configuration registers (GHWCFG1, 2, 3, and
 * 4) to find the configuration parameters selected for DWC_otg core.
 *
 * 2. Program the following fields in the Global AHB Configuration (GAHBCFG)
 * register.
 *
 *  - DMA Mode bit (applicable only when the OTG_ARCHITECTURE parameter is
 *    set to Internal/External DMA)
 *  - AHB Burst Length field (applicable only when the OTG_ARCHITECTURE
 *    parameter is set to Internal/External DMA)
 *  - Global Interrupt Mask bit = 1
 *  - Non-periodic TxFIFO Empty Level (can be enabled only when the core is
 *    operating in Slave mode as a host or as a device in Shared FIFO operation.)
 *  - Periodic TxFIFO Empty Level (can be enabled only when the core is
 *    operating in Slave mode)
 *
 * 3. Program the following field in the Global Interrupt Mask (GINTMSK)
 *    register:
 *
 *  - GINTMSK.RxFLvlMsk = 1’b0
 *
 * 4. Program the following fields in GUSBCFG register.
 *
 * - HNP Capable bit (applicable only when the OTG_MODE parameter is set
 *   to 0)
 * - SRP Capable bit (not applicable when the OTG_MODE parameter is set to
 *   Device Only)
 * - ULPI DDR Selection bit (applicable only when the OTG_HSPHY_INTERFACE
 *   parameter is selected for ULPI)
 * - External HS PHY or Internal FS Serial PHY Selection bit (not applicable
 *   when “None” is selected for the OTG_FSPHY_INTERFACE parameter)
 * - ULPI or UTMI+ Selection bit (not applicable when “None” is selected for
 *   the OTG_HSPHY_INTERFACE parameter)
 * - PHY Interface bit (applicable only when the OTG_HSPHY_INTERFACE parameter
 *   is selected for UTMI+)
 * - HS/FS TimeOUT Time-Out Calibration field
 * - USB Turnaround Time field
 *
 * 5. The software must unmask the following bits in the GINTMSK register.
 *
 * - OTG Interrupt Mask
 * - Mode Mismatch Interrupt Mask
 *
 * 6. If the GUID register is selected for implementation in coreConsultant,
 *    the software has the option of programming this register.
 *
 * 7. The software can read the GINTSTS.CurMod bit to determine whether the
 *    DWC_otg core is operating in Host or Device mode. The software then follows
 *    either the “Programming Flow for Application Selection of PHY Interface” or
 *    "Device Initialization" sequence.
 *
 */
mbed_error_t usbotghs_initialize_core(usbotghs_dev_mode_t mode)
{
    log_printf("[USB HS] initializing the core\n");
    mbed_error_t errcode = MBED_ERROR_NONE;
    int count = 0;
    volatile uint32_t reg_value;

    /* 1. Read the User Hardware Configuration registers
     *
     * INFO: this not needed in the STM32F4 IP instanciation, as GHWCFG registers
     * are not mapped
     */


    /* 2. Program the following fields in the Global AHB Configuration (GAHBCFG)
     * register.
     */
    log_printf("[USB HS] core init: set global AHB config\n");
#if CONFIG_USR_DEV_USBOTGHS_DMA
    /* enable DMA. On STM32F4, this is an external DMA (SoC DMA) */
    set_reg(r_CORTEX_M_USBOTG_HS_GAHBCFG, 1, USBOTG_HS_GAHBCFG_DMAEN);
    /* Set HW burst length/type to INCR4 (32bit increment), in compliance
     * with the DMA configuration */
    set_reg(r_CORTEX_M_USBOTG_HS_GAHBCFG, 0x3, USBOTG_HS_GAHBCFG_HBSTLEN);
#endif
    /* mask the global interrupt mask */
    log_printf("[USB HS] core init: mask the global interrupt msk\n");
    set_reg(r_CORTEX_M_USBOTG_HS_GAHBCFG, 0, USBOTG_HS_GAHBCFG_GINTMSK);
    /* non-periodic TxFIFO empty level (host mode or device with SFO mode) */
    if (mode == USBOTGHS_MODE_HOST) {
        /* periodic TxFIFO empty level rise an interrupt when half empty */
        set_reg(r_CORTEX_M_USBOTG_HS_GAHBCFG, 0, USBOTG_HS_GAHBCFG_PTXFELVL);
    }
    /* both Host & Device mode, TXFE rise on TxFIFO completely empty */
    /* non-periodic TxFIFO empty level rise an interrupt when *full* empty */
#ifdef CONFIG_USR_DEV_USBOTGHS_TRIGER_XMIT_ON_HALF
    set_reg(r_CORTEX_M_USBOTG_HS_GAHBCFG, TRIGGER_TXFE_ON_HALF_EMPTY, USBOTG_HS_GAHBCFG_TXFELVL);
#else
    set_reg(r_CORTEX_M_USBOTG_HS_GAHBCFG, TRIGGER_TXFE_ON_FULL_EMPTY, USBOTG_HS_GAHBCFG_TXFELVL);
#endif

	/* Wait for master AHB automaton to be in IDLE state */
    log_printf("[USB HS] core init: clear PWRDWN\n");

    /*
     * 3. Program the following field in the Global Interrupt Mask (GINTMSK)
     *    register:
     */
    log_printf("[USB HS] core init: clear global interrupt mask\n");
    set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 0, USBOTG_HS_GINTMSK_RXFLVLM);


    /*
     * 4. Program the following fields in GUSBCFG register (configure PHY
     * interactions and HNP/SRP capabilities).
     */

    /* clear the USB transiver powerdwn msk */
	clear_reg_bits(r_CORTEX_M_USBOTG_HS_GCCFG, USBOTG_HS_GCCFG_PWRDWN_Msk);

    /* SRP and HNP capable bits are not described in the USB OTG HS
     * TODO: STM32F4 datasheet. It would be intereseting to check if they can
     * be used in device and host mode in HS case too */
#if 0
    set_reg(r_CORTEX_M_USBOTG_HS_GUSBCFG, 0, USBOTG_HS_GUSBCFG_HNPCAP);
    /* if OTG_mode is set to device only */
    if (mode == USBOTGHS_MODE_DEVICE) {
        set_reg(r_CORTEX_M_USBOTG_HS_GUSBCFG, 1, USBOTG_HS_GUSBCFG_SRPCAP);
    }
#endif
    log_printf("[USB HS] core init: configure ULPI interractions\n");
	reg_value = read_reg_value(r_CORTEX_M_USBOTG_HS_GUSBCFG);
    log_printf("[USB HS] initial GUSBCFG is %x %x %x %x\n", reg_value >> 24, (reg_value >> 16) & 0xff, (reg_value >> 8) & 0xff, reg_value & 0xff);
	/* Use the internal VBUS */
	clear_reg_bits(&reg_value, USBOTG_HS_GUSBCFG_ULPIEVBUSD_Msk);
	/* Data line pulsing using utmi_txvalid */
	clear_reg_bits(&reg_value, USBOTG_HS_GUSBCFG_TSDPS_Msk);
	/* ULPI interface selection */
	set_reg_bits(&reg_value, USBOTG_HS_GUSBCFG_UTMISEL_Msk);
	/* ULPI Physical interface is 8 bits */
	clear_reg_bits(&reg_value, USBOTG_HS_GUSBCFG_PHYIF_Msk);
	/* DDRSEL at single data rate */
	clear_reg_bits(&reg_value, USBOTG_HS_GUSBCFG_DDRSEL_Msk);

	clear_reg_bits(&reg_value, USBOTG_HS_GUSBCFG_ULPIFSLS_Msk);
	clear_reg_bits(&reg_value, USBOTG_HS_GUSBCFG_ULPICSM_Msk);

    /* writing back the global configuration register */
	write_reg_value(r_CORTEX_M_USBOTG_HS_GUSBCFG, reg_value);
    log_printf("[USB HS] core init: GUSBCFG is %x %x %x %x\n", reg_value >> 24, (reg_value >> 16) & 0xff, (reg_value >> 8) & 0xff, reg_value & 0xff);
	reg_value = read_reg_value(r_CORTEX_M_USBOTG_HS_GUSBCFG);
    log_printf("[USB HS] core init: GUSBCFG reg after conf is %x %x %x %x\n", reg_value >> 24, (reg_value >> 16) & 0xff, (reg_value >> 8) & 0xff, reg_value & 0xff);

	/* Core soft reset must be issued after PHY configuration */
	/* Wait for AHB master idle */
    while (!get_reg(r_CORTEX_M_USBOTG_HS_GRSTCTL, USBOTG_HS_GRSTCTL_AHBIDL)) {
        if (++count >  USBOTGHS_REG_CHECK_TIMEOUT) {
            log_printf("HANG! AHB Idle GRSTCTL:AHBIDL\n");
            errcode = MBED_ERROR_BUSY;
            goto err;
        }
    }

    log_printf("[USB HS] AHB idle after %d loops\n", count);


    count = 0;
    set_reg(r_CORTEX_M_USBOTG_HS_GRSTCTL, 1, USBOTG_HS_GRSTCTL_CSRST);
    while (get_reg(r_CORTEX_M_USBOTG_HS_GRSTCTL, USBOTG_HS_GRSTCTL_CSRST)) {
        if (++count > USBOTGHS_REG_CHECK_TIMEOUT) {
            log_printf("HANG! Core Soft RESET\n");
            errcode = MBED_ERROR_BUSY;
            goto err;
        }
    }
    log_printf("[USB HS] Core acknowledged reset after %d loops\n", count);
    /* 3 PHY clocks wait, (active wait here, as sys_sleep() is too slow */
	for (uint32_t i = 0; i < 0xff; i++) {
		continue;
    }

    /*
     * 5. The software must unmask the following bits in the GINTMSK register.
     */
    log_printf("[USB HS] core init: unmask OTGINT & MMISM Int\n");
	set_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK,
                 USBOTG_HS_GINTMSK_OTGINT_Msk | USBOTG_HS_GINTMSK_MMISM_Msk);

    log_printf("[USB HS] core init: clear SOF (soft reset case)\n");
	clear_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK, USBOTG_HS_GINTMSK_SOFM_Msk);
    /*
     * 6. not needed here.
     */
    /*
     * 7. checking curMod at core init
     */
err:
    return errcode;
}


mbed_error_t usbotghs_initialize_device(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    log_printf("[USB HS] dev init: Device mode initialization...\n");
#if CONFIG_USR_DEV_USBOTGHS_DMA
    log_printf("[USB HS] dev init: Device mode with DMA support\n");
    /* replaced by DMA */
    set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 0, USBOTG_HS_GINTMSK_RXFLVLM);
    set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 0, USBOTG_HS_GINTMSK_NPTXFEM);
#else
    log_printf("[USB HS] dev init: Device mode without DMA support\n");
    set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 1, USBOTG_HS_GINTMSK_RXFLVLM);
//XXX:    set_reg(r_CORTEX_M_USBOTG_HS_GINTMSK, 1, USBOTG_HS_GINTMSK_NPTXFEM);
#endif


#if CONFIG_USR_DEV_USBOTGHS_DMA
    /* DCFG DescDMA bit does not exist on STM32F4 implementation of the IP */
#endif
    log_printf("[USB HS] dev init: set speed to HS\n");
    /* set device speed to High Speed */
	set_reg(r_CORTEX_M_USBOTG_HS_DCFG, 0x0, USBOTG_HS_DCFG_DSPD);
    /* send packets to the application. send handshake based on NAK & STALL bits for
     * current EP */
	set_reg(r_CORTEX_M_USBOTG_HS_DCFG, 0, USBOTG_HS_DCFG_NZLSOHSK);

    /* set periodic (micro)frame interval */
	set_reg(r_CORTEX_M_USBOTG_HS_DCFG, USBOTG_HS_DCFG_PFIVL_INTERVAL_80, USBOTG_HS_DCFG_PFIVL);





#if CONFIG_USR_DEV_USBOTGHS_DMA
    log_printf("[USB HS] dev init: set DMA thresholds\n");
    /* set device threshold */
    /* Arbitrer parking enable (avoid underrun) */
	set_reg(r_CORTEX_M_USBOTG_HS_DTHRCTL, 1, USBOTG_HS_DTHRCTL_ARPEN);
    /*threshold for RxFIFO in DWORDs */
	set_reg(r_CORTEX_M_USBOTG_HS_DTHRCTL, 8, USBOTG_HS_DTHRCTL_RXTHRLEN);
    /* enable threshold for RxFIFO */
	set_reg(r_CORTEX_M_USBOTG_HS_DTHRCTL, 1, USBOTG_HS_DTHRCTL_RXTHREN);
    /*threshold for TxFIFO in DWORDs */
	set_reg(r_CORTEX_M_USBOTG_HS_DTHRCTL, 8, USBOTG_HS_DTHRCTL_RXTHRLEN);
    /* enable threshold for TxFIFO */
	set_reg(r_CORTEX_M_USBOTG_HS_DTHRCTL, 1, USBOTG_HS_DTHRCTL_TXTHREN);

    /* disable threshold for isochronous EP */
	set_reg(r_CORTEX_M_USBOTG_HS_DTHRCTL, 0, USBOTG_HS_DTHRCTL_ISOTHREN);
    /* enable threshold for non-isochronous EP */
	set_reg(r_CORTEX_M_USBOTG_HS_DTHRCTL, 1, USBOTG_HS_DTHRCTL_NONISOTHREN);
#endif
    /* configure the ULPI backend of the core */

    log_printf("[USB HS] dev init: set ULPI backend\n");
    set_reg(r_CORTEX_M_USBOTG_HS_DCTL, 0, USBOTG_HS_DCTL_SDIS);

    log_printf("[USB HS] dev init: enable nominal Ints\n");
    /* enable reset, enumeration done, early suspend, usb suspend & start-of-frame
     * IEP and OEP int are handled at USB reset handling time */
	set_reg_bits(r_CORTEX_M_USBOTG_HS_GINTMSK,
        		 USBOTG_HS_GINTMSK_USBRST_Msk   |
                 USBOTG_HS_GINTMSK_ENUMDNEM_Msk |
                 USBOTG_HS_GINTMSK_ESUSPM_Msk   |
                 USBOTG_HS_GINTMSK_USBSUSPM_Msk);

    log_printf("[USB HS] dev init: unmask the global interrupt msk\n");
    set_reg(r_CORTEX_M_USBOTG_HS_GAHBCFG, 1, USBOTG_HS_GAHBCFG_GINTMSK);
    return errcode;
}

/*
 * TODO: this mode is not yet supported by the device
 */
mbed_error_t usbotghs_initialize_host(void)
{
    mbed_error_t errcode = MBED_ERROR_UNSUPORTED_CMD;

    return errcode;

}

