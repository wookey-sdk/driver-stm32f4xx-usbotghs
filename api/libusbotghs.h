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
#ifndef LIBUSBOTGHS_H_
#define LIBUSBOTGHS_H_

#include "libc/types.h"
#include "autoconf.h"


/*
 * EP name abstraction
 */
#define EP0 USBOTG_HS_EP0
#define EP1 USBOTG_HS_EP1
#define EP2 USBOTG_HS_EP2
#define EP3 USBOTG_HS_EP3
#define EP4 USBOTG_HS_EP4
#define EP5 USBOTG_HS_EP5
#define EP6 USBOTG_HS_EP6
#define EP7 USBOTG_HS_EP7

#define MAX_DATA_PACKET_SIZE(ep) (((ep) == 0) ? 64 : 512)

/*
 * The USB OTG support On-The-Go configuration (i.e. Host or Device mode, configurable
 * by software stack. This enumerate define which mode to use
 */
typedef enum {
    USBOTGHS_MODE_HOST,
    USBOTGHS_MODE_DEVICE
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
} usb_ep_toggle_t;

/*
 * USB standard EP type
 */
typedef enum {
    USBOTG_HS_EP_TYPE_CONTROL     = 0,
    USBOTG_HS_EP_TYPE_ISOCHRONOUS = 1,
    USBOTG_HS_EP_TYPE_BULK        = 2,
    USBOTG_HS_EP_TYPE_INT         = 3,
} usbotghs_ep_type_t;


/*********************************************************************************
 * About handlers
 *
 * Handlers are triggered by the USB OTG HS driver on events (typically interrupts)
 * in order to call the corresponding subprogram.
 *
 * Events can be:
 * - data reception
 * - requests reception (i.e. setup packets)
 * - various state events (reset, power-related, errors)
 *
 * handlers for OUT event (reception from the device side)
 * These handlers must be declared from the upper layers (libusbctrl or interfaces)
 *
 * INFO: Remember that USB protocol direction is defined from the host point of view.
 * Receptions are made on OUT endpoints, transmission on IN endpoints.
 */
typedef mbed_error_t (*setup_pkt_handler_t)(uint8_t *setup_pkt,
                                            uint32_t dev_id);

typedef mbed_error_t (*data_pkt_handler_t)(uint8_t *data_pkt,
                                           uint8_t ep_num,
                                   uint8_t dev_id);

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
mbed_error_t usbotghs_declare(void);

/*
 * Core initial setup and config. At the end of the initialization, the Core should
 * have its USB control pipe ready to receive the first requests from the host.
 */
mbed_error_t usbotghs_configure(usbotghs_dev_mode_t mode);

/*
 * Sending data (whatever data type is (i.e. status on control pipe or data on
 * data (Bulk, IT or isochronous) pipe)
 */
mbed_error_t usbotghs_send_data(const uint8_t *src, uint32_t size, uint8_t ep);

/*
 * Receiving data (same as above, but for receiving
 */
mbed_error_t usbotghs_recv_data(uint8_t *dst, uint32_t size, uint8_t ep);

/*
 * Send a special zero-length packet on EP ep
 */
mbed_error_t usbotghs_send_zlp(uint8_t ep);

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
mbed_error_t usbotghs_endpoint_stall(uint8_t ep);

/*
 * Clear the STALL mode for the given EP
 */
mbed_error_t usbotghs_endpoint_stall_clear(uint8_t ep);

/*
 * Activate the given EP (for e.g. to transmit data)
 */
mbed_error_t usbotghs_activate_endpoint(uint8_t ep);

/*
 * Deactivate the given EP (Its configuration is keeped, the EP is *not* deconfigured)
 */
mbed_error_t usbotghs_deactivate_endpoint(uint8_t ep);

/*
 * Configure the given EP in order to be ready to work
 */
mbed_error_t usbotghs_configure_endpoint(uint8_t               id,
                                         usbotghs_ep_type_t    type,
                                         usbotghs_epx_mpsize_t mpsize);

/*
 * Deconfigure the given EP. The EP is no more usable after this call. A new configuration
 * of the EP must be done before reuse it.
 * This function is typically used on SetConfiguration Requests schedule, or on
 * Reset frame reception to reconfigure the Core in a known clear state.
 */
mbed_error_t usbotghs_deconfigure_endpoint(uint8_t ep);


/**
 * usb_driver_set_address - Set the address of the device
 * @addr: Device's address
 */
void usbotghs_driver_set_address(uint16_t addr);

/* Map USB device. TODO */
void usbotghs_bind(void);

void usbotghs_unbind(void);

#endif /*!LIBUSBOTGHS_H_ */
