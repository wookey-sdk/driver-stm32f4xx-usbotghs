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
#include "api/libusbotghs.h"
#include "usbotghs.h"
#include "ulpi.h"

/*
 * Initialize the USB PHY through ULPI interface
 */
mbed_error_t usbotghs_ulpi_reset(void)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint32_t err;

	log_printf("[USB HS] %s\n", __FUNCTION__);
	log_printf("[USB HS] Resetting ULPI through PE13 pin ...\n");
	/* Resetting the ULPI PHY is performed by setting the PE13 pin to 1 during
	 * some milliseconds.
	 */
    /* TODO: the PHY GPIOs should be defined through a generated header,
     * not hardcoded */
	if ((err = sys_cfg(CFG_GPIO_SET, (uint8_t)(((usb_otg_hs_dev_infos.gpios[USB_HS_RESET].port << 4) + usb_otg_hs_dev_infos.gpios[USB_HS_RESET].pin)), 1)) != SYS_E_DONE) {
        errcode = MBED_ERROR_INITFAIL;
        log_printf("failed to reset ULPI: GPIO set syscall returns %d\n", err);
        goto end;
    }
    /* waiting at least 5 milliseconds */
    sys_sleep(SLEEP_MODE_DEEP, 5);
	if ((err = sys_cfg(CFG_GPIO_SET, (uint8_t)(((usb_otg_hs_dev_infos.gpios[USB_HS_RESET].port << 4) + usb_otg_hs_dev_infos.gpios[USB_HS_RESET].pin)), 0)) != SYS_E_DONE) {
        errcode = MBED_ERROR_INITFAIL;
        log_printf("failed to reset ULPI: GPIO clear syscall returns %d\n", err);
        goto end;
    }
end:
    return errcode;
}

