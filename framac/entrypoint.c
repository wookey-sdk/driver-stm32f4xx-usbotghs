#include "generated/devlist.h"
#include "libusbctrl.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"

#include "framac/entrypoint.h"

#include "api/libusbotghs.h"
#include "usbotghs.h"
#include "usbotghs_fifos.h"


/*
 * Support for Frama-C testing
 */


//@ assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
void Frama_C_update_entropy_8(void) {
  Frama_C_entropy_source_8 = Frama_C_entropy_source_8;
}

//@ assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
void Frama_C_update_entropy_16(void) {
  Frama_C_entropy_source_16 = Frama_C_entropy_source_16;
}

//@ assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
void Frama_C_update_entropy_32(void) {
  Frama_C_entropy_source_32 = Frama_C_entropy_source_32;
}

/*@ requires order: 0 <= min <= max <= 255;
    assigns \result \from min, max, Frama_C_entropy_source_8;
    assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
    ensures result_bounded: min <= \result <= max ;
 */

uint8_t Frama_C_interval_8(uint8_t min, uint8_t max)
{
  uint8_t r,aux;
  Frama_C_update_entropy_8();
  aux = Frama_C_entropy_source_8;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@ requires order: 0 <= min <= max <= 65535;
    assigns \result \from min, max, Frama_C_entropy_source_16;
    assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
    ensures result_bounded: min <= \result <= max ;
 */

uint16_t Frama_C_interval_16(uint16_t min, uint16_t max)
{
  uint16_t r,aux;
  Frama_C_update_entropy_16();
  aux = Frama_C_entropy_source_16;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@ requires order: 0 <= min <= max <= 4294967295;
    assigns \result \from min, max, Frama_C_entropy_source_32;
    assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
    ensures result_bounded: min <= \result <= max ;
 */

uint32_t Frama_C_interval_32(uint32_t min, uint32_t max)
{
  uint32_t r,aux;
  Frama_C_update_entropy_32();
  aux = Frama_C_entropy_source_32;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}


mbed_error_t my_handle_inepevent(uint32_t dev_id __attribute__((unused)),
                                 uint32_t size  __attribute__((unused)),
                                 uint8_t ep __attribute__((unused)))
{
    return MBED_ERROR_NONE;
}
mbed_error_t my_handle_outepevent(uint32_t dev_id __attribute__((unused)),
                                  uint32_t size  __attribute__((unused)),
                                  uint8_t ep __attribute__((unused)))
{
    return MBED_ERROR_NONE;
}

/*
    test for functions defined in driver USB (not all function analysed, only the functions needed for libxDCI)
    nominal and bad parameters

*/

void test_fcn_driver_eva(void)
{

    uint8_t ep_id = Frama_C_interval_8(0,255);
    uint8_t ep_num = Frama_C_interval_8(0,255);
    uint8_t dir8 = Frama_C_interval_8(0,255);
    uint8_t dst = Frama_C_interval_8(0,255);
    uint32_t size = Frama_C_interval_32(0,4294967295);
    uint8_t fifo = Frama_C_interval_8(0,255);
    uint32_t fifo_idx = Frama_C_interval_32(0,4294967295);
    uint32_t fifo_size = Frama_C_interval_32(0,4294967295);
    usbotghs_epx_mpsize_t size_ep = Frama_C_interval_8(0,3);

    uint8_t src = 1 ;

    usbotghs_ep_dir_t dir = Frama_C_interval_8(0,1);
    usbotghs_ep_type_t type = Frama_C_interval_8(0,3);
    usbotghs_ep_state_t state = Frama_C_interval_8(0,9) ;
    usbotghs_dev_mode_t mode = Frama_C_interval_8(0,1);

    usbotghs_declare();
    usbotghs_configure(mode, & usbctrl_handle_inepevent,& usbctrl_handle_outepevent);


    usbotghs_global_stall() ;
    usbotghs_endpoint_set_nak(ep_id, dir) ;
    usbotghs_global_stall_clear();
    usbotghs_endpoint_stall_clear(ep_id, dir);
    usbotghs_deconfigure_endpoint(ep_id);
    usbotghs_activate_endpoint(ep_id,dir);
    usbotghs_deactivate_endpoint( ep_id,dir);
    usbotghs_enpoint_nak( ep_id);
    usbotghs_enpoint_nak_clear( ep_id);
    usbotghs_endpoint_disable( ep_id,     dir);
    usbotghs_endpoint_enable( ep_id,     dir);
    usbotghs_endpoint_clear_nak(ep_id, dir) ;
    usbotghs_endpoint_stall(ep_id, dir) ;
    usbotghs_get_ep_state(ep_id, dir) ;

    usbotghs_ctx.in_eps[EP0].mpsize = Frama_C_interval_16(0,65535);
    uint8_t resp[1024] = { 0 };
    usbotghs_ctx.in_eps[EP0].fifo_lck = 1 ;
    usb_backend_drv_send_data((uint8_t *)&resp, size, EP0);
    usbotghs_ctx.in_eps[EP0].fifo_lck = 0 ;
    usb_backend_drv_send_data((uint8_t *)&resp, 514, EP0);
    usbotghs_ctx.in_eps[4].mpsize = Frama_C_interval_16(0,65535);
    usbotghs_ctx.in_eps[4].id = 4 ;
    usbotghs_ctx.in_eps[4].fifo_lck = 0 ;
    usbotghs_ctx.in_eps[4].configured = 1 ;
    usb_backend_drv_send_data((uint8_t *)&resp, size, 4);
    usb_backend_drv_send_data((uint8_t *)&resp, size, 8);
    usbotghs_send_zlp(ep_id);
    usbotghs_txfifo_flush(ep_id);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,64,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,128,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,512,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,1024,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_configure(mode, & my_handle_inepevent,& my_handle_outepevent);
    usbotghs_set_recv_fifo((uint8_t *)&resp, size, 0);
    usbotghs_set_recv_fifo((uint8_t *)&resp, size, 1);

    /*
        TODO : send_data analyse is not enough generalised
    */

}

void main(void)
{
    test_fcn_driver_eva() ;
}
