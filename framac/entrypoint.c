#include "generated/devlist.h"
#include "libusbctrl.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"

#include "framac/entrypoint.h"

#include "api/libusbotghs.h"
#include "usbotghs.h"
#include "usbotghs_fifos.h"
#include "usbotghs_handler.h"


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

/***************************************************************************
 * requested prototypes and callbacks implementations
 */

mbed_error_t usbctrl_handle_earlysuspend(uint32_t dev_id __attribute__((unused))) {
    return MBED_ERROR_NONE;
}

mbed_error_t usbctrl_handle_reset(uint32_t dev_id __attribute__((unused))) {
    return MBED_ERROR_NONE;
}

mbed_error_t usbctrl_handle_usbsuspend(uint32_t dev_id __attribute__((unused))) {

    return MBED_ERROR_NONE;
}

mbed_error_t usbctrl_handle_inepevent(uint32_t dev_id __attribute__((unused)),
                                      uint32_t size __attribute__((unused)),
                                      uint8_t ep __attribute__((unused))) {
    return MBED_ERROR_NONE;
}

mbed_error_t usbctrl_handle_outepevent(uint32_t dev_id __attribute__((unused)),
                                       uint32_t size __attribute__((unused)),
                                       uint8_t ep __attribute__((unused))) {
    return MBED_ERROR_NONE;
}

mbed_error_t usbctrl_handle_wakeup(uint32_t dev_id __attribute__((unused))) {
    return MBED_ERROR_NONE;
}



/*
    test for functions defined in driver USB (not all function analysed, only the functions needed for libxDCI)
    nominal and bad parameters

*/

uint8_t resp[4096];

void init_driver(void)
{
    mbed_error_t errcode;
    uint8_t ep_id = Frama_C_interval_8(0,255);
    usbotghs_ep_type_t type = Frama_C_interval_8(0,3);
    usbotghs_dev_mode_t mode = Frama_C_interval_8(0,255);
    usbotghs_ep_dir_t dir = Frama_C_interval_8(0,1);

    errcode = usbotghs_declare();
    /*  assert errcode == MBED_ERROR_NONE; */
    errcode = usbotghs_configure(mode, & usbctrl_handle_inepevent,& usbctrl_handle_outepevent);
    /*  assert errcode != MBED_ERROR_NONE; */

    /* Here, we set, even for EP0, generic, empty callbacks (same for all EPs, as the EP0 control plane proof is handled in
     * USBxDCI, not here. */
    errcode = usbotghs_configure(USBOTGHS_MODE_DEVICE, &handler_ep, &handler_ep);

    usbotghs_set_recv_fifo(&resp[0], 512, EP0);
    usbotghs_set_address(0);
}

void test_fcn_driver_eva(void)
{

    uint8_t ep_id = Frama_C_interval_8(0,255);
    uint8_t ep_num = Frama_C_interval_8(0,255);
    uint8_t dir8 = Frama_C_interval_8(0,255);
    uint8_t dst = Frama_C_interval_8(0,255);
    uint32_t size = Frama_C_interval_32(64,4096);
    usbotghs_epx_mpsize_t size_ep = Frama_C_interval_8(0,3);
    usbotghs_dev_mode_t mode = Frama_C_interval_8(0,1);
    usbotghs_ep_type_t type_ep = Frama_C_interval_8(0,3);

    uint8_t src = 1 ;

    usbotghs_ep_dir_t dir = Frama_C_interval_8(0,2);
    usbotghs_ep_type_t type = Frama_C_interval_8(0,3);
    usbotghs_ep_state_t state = Frama_C_interval_8(0,9) ;

    usbotghs_get_ep_mpsize(type_ep);
    usbotghs_get_speed();
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

    usbotghs_send_data((uint8_t *)&resp[0], 512, EP0);
    usbotghs_send_data((uint8_t *)&resp[0], 16, EP0);
    usbotghs_send_data((uint8_t *)&resp[0], 19, EP0);
    usbotghs_send_data((uint8_t *)&resp[0], 1024, EP0);
#if 0
    //usbotghs_ctx.in_eps[EP0].mpsize = Frama_C_interval_16(0,65535);
    /* manual lock update for reentrency test purpose only */
    usbotghs_ctx.in_eps[EP0].fifo_lck = 1 ;
    usbotghs_send_data((uint8_t *)&resp[0], size, EP0);
    usbotghs_ctx.in_eps[EP0].fifo_lck = 0 ;

    usbotghs_send_data((uint8_t *)&resp[0], 512, EP0);
    /* manual set of EP 4 */
    usbotghs_ctx.in_eps[4].mpsize = Frama_C_interval_16(0,65535);
    usbotghs_ctx.in_eps[4].id = 4 ;
    usbotghs_ctx.in_eps[4].fifo_lck = 0 ;
    usbotghs_ctx.in_eps[4].configured = 1 ;
    /* send data on EP 4 */

    usbotghs_send_data((uint8_t *)&resp[0], size, 4);
#endif
    /* send data on invalid EP */
    usbotghs_send_data((uint8_t *)&resp[0], size, 8);

    usbotghs_configure_endpoint(1,type,USB_BACKEND_DRV_EP_DIR_OUT, 512,USB_BACKEND_EP_ODDFRAME,&handler_ep);

    usbotghs_send_zlp(1);
    usbotghs_send_zlp(0);

    if (ep_id < USBOTGHS_MAX_IN_EP) {
        /* txfifo_flush is an internal funtion, ep_id is required as < MAX_IN_EP */
        usbotghs_txfifo_flush(ep_id);
    }
#if 0
    /* representative of EP MPSize standard for ctrl EP */
    usbotghs_ctx.in_eps[EP0].mpsize = 64;

    usbotghs_configure_endpoint(ep_id,type,dir,64,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_configure_endpoint(ep_id,type,dir,128,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_configure_endpoint(ep_id,type,dir,512,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_configure_endpoint(ep_id,type,dir,1024,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_configure(mode, & my_handle_inepevent,& my_handle_outepevent);
#endif
    usbotghs_set_recv_fifo((uint8_t *)&resp[0], size, 0);
    usbotghs_set_recv_fifo((uint8_t *)&resp[0], size, 1);
    usbotghs_set_recv_fifo((uint8_t *)&resp[0], size, 7); /* inexistant EP */

    /* trying to set fifo while locked */
    usbotghs_ctx.out_eps[1].fifo_lck = true;
    usbotghs_set_recv_fifo((uint8_t *)&resp[0], size, 1);
    usbotghs_ctx.out_eps[1].fifo_lck = false;

#if 0
    usbotghs_configure_endpoint(ep_id,type,dir,64,USB_BACKEND_EP_ODDFRAME,&handler_ep);
#endif
    /* error cases */
    usbotghs_set_recv_fifo(NULL, 128, 0);
    usbotghs_set_recv_fifo(NULL, 128, 8);
    usbotghs_set_recv_fifo((uint8_t *)&resp[0], 0, 0);

    /* valid case */
    usbotghs_set_recv_fifo((uint8_t *)&resp[0], 128, 0);
    usbotghs_send_data((uint8_t *)&resp[0], 512, EP0);

    /* EP 1 */
    usbotghs_configure_endpoint(1,type,USB_BACKEND_DRV_EP_DIR_OUT, 512,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_activate_endpoint(1, USB_BACKEND_DRV_EP_DIR_OUT);
    /* reading 0 bytes from EP 1 */
    /* EP 2 */
    usbotghs_configure_endpoint(2,type,USB_BACKEND_DRV_EP_DIR_IN, 512,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_set_recv_fifo((uint8_t *)&resp[0], 512, 2);
    usbotghs_activate_endpoint(2, USB_BACKEND_DRV_EP_DIR_IN);
    usbotghs_send_data((uint8_t *)&resp[0], 64, 2);
    usbotghs_send_data((uint8_t *)&resp[0], 68, 2);
    usbotghs_send_data((uint8_t *)&resp[0], 500, 2);
    usbotghs_send_data((uint8_t *)&resp[0], 512, 2);
    /* 4 bytes padding check in write_core_fifo(): */
    usbotghs_send_data((uint8_t *)&resp[0], 513, 2);
    usbotghs_send_data((uint8_t *)&resp[0], 514, 2);
    usbotghs_send_data((uint8_t *)&resp[0], 515, 2);

    /* simulating async lock */
    usbotghs_ctx.in_eps[2].fifo_lck = true;
    usbotghs_send_data((uint8_t *)&resp[0], 512, 2);
    usbotghs_ctx.in_eps[2].fifo_lck = false;


    usbotghs_txfifo_flush_all();
    /*
        TODO : send_data analyse is not enough generalised
    */

}


/*@
  @ requires \separated(((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), &usbotghs_ctx);
  @ assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx;
  */
void test_fcn_isr_events(void)
{
    uint32_t intsts = 0;
    uint32_t intmsk = 0;

    /* TODO: set core register to valid content (or controlled interval) to
     * check all switch/if control cases of handlers */
    /* first reset */
    intsts = (uint32_t)(1 << 12);
    intmsk = (uint32_t)(1 << 12);
    USBOTGHS_IRQHandler((uint8_t)OTG_HS_IRQ, intsts, intmsk);
    /* enumdone */
    intsts = (uint32_t)(1 << 13);
    intmsk = (uint32_t)(1 << 13);
    USBOTGHS_IRQHandler((uint8_t)OTG_HS_IRQ, intsts, intmsk);

    usbotghs_set_address(42);

    /* set recv FIFO for EP0 */
    usbotghs_set_recv_fifo((uint8_t *)&resp[0], 512, 0);
    /* looping on any */

    /* set amount to read to 2048 for EP1 */
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 1, USBOTG_HS_GRXSTSP_EPNUM);
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 2048, USBOTG_HS_GRXSTSP_BCNT);
    /*@
      @ loop invariant 0 <= i <= 31;
      @ loop assigns intsts, intmsk, i, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx;
      @ loop variant 31 - i;
      */
    for (uint8_t i = 0; i < 31; ++i) {
        /* @ assert 0 <= i <= 31; */
        intsts = (uint32_t)(1 << i);
        intmsk = (uint32_t)(1 << i);
        USBOTGHS_IRQHandler((uint8_t)OTG_HS_IRQ, intsts, intmsk);
    }

    usbotghs_configure_endpoint(1,USBOTG_HS_EP_TYPE_BULK, USBOTG_HS_EP_DIR_OUT, 512,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    /* emulate data in recv FIFO (replacing setup pkt content) */
    usbotghs_set_recv_fifo((uint8_t *)&resp[0], 512, 1);
    usbotghs_activate_endpoint(1, USB_BACKEND_DRV_EP_DIR_OUT);
    usbotghs_ctx.out_eps[1].fifo_idx = 256;

    /* Here we set the EPNum to 1, bcnt=512 */
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 1, USBOTG_HS_GRXSTSP_EPNUM);
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 512, USBOTG_HS_GRXSTSP_BCNT);

    /* handling OEPInt Handler */
    intsts = (1 << 19) | (1 << 4);
    intmsk = (1 << 19) | (1 << 4);
    USBOTGHS_IRQHandler((uint8_t)OTG_HS_IRQ, intsts, intmsk);

    /* Here we set the EPNum to 1, bcnt=16 */
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 1, USBOTG_HS_GRXSTSP_EPNUM);
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 16, USBOTG_HS_GRXSTSP_BCNT);

    /* handling OEPInt Handler */
    intsts = (1 << 19) | (1 << 4);
    intmsk = (1 << 19) | (1 << 4);
    USBOTGHS_IRQHandler((uint8_t)OTG_HS_IRQ, intsts, intmsk);

    /* Here we set the EPNum to 1, bcnt=6 */
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 1, USBOTG_HS_GRXSTSP_EPNUM);
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 6, USBOTG_HS_GRXSTSP_BCNT);

    /* handling OEPInt Handler */
    intsts = (1 << 19) | (1 << 4);
    intmsk = (1 << 19) | (1 << 4);
    USBOTGHS_IRQHandler((uint8_t)OTG_HS_IRQ, intsts, intmsk);

    /* Here we set the EPNum to 1, bcnt=5 */
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 1, USBOTG_HS_GRXSTSP_EPNUM);
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 5, USBOTG_HS_GRXSTSP_BCNT);

    /* handling OEPInt Handler */
    intsts = (1 << 19) | (1 << 4);
    intmsk = (1 << 19) | (1 << 4);
    USBOTGHS_IRQHandler((uint8_t)OTG_HS_IRQ, intsts, intmsk);

    /* Here we set the EPNum to 4 (not configured), bcnt=5 */
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 4, USBOTG_HS_GRXSTSP_EPNUM);
    set_reg(r_CORTEX_M_USBOTG_HS_GRXSTSP, 5, USBOTG_HS_GRXSTSP_BCNT);

    /* handling OEPInt Handler */
    intsts = (1 << 19) | (1 << 4);
    intmsk = (1 << 19) | (1 << 4);
    USBOTGHS_IRQHandler((uint8_t)OTG_HS_IRQ, intsts, intmsk);



    /* transmission check (iepint) */
    usbotghs_configure_endpoint(2,USBOTG_HS_EP_TYPE_BULK, USBOTG_HS_EP_DIR_IN, 16,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_activate_endpoint(2, USB_BACKEND_DRV_EP_DIR_IN);

    usbotghs_send_data((uint8_t *)&resp[0], 512, EP0);

    /* sending fifo_size + 1/2 fifo_size */
    usbotghs_send_data((uint8_t *)&resp[0], 768, 2);


    /* HID typical endpoint: both direction, interrupt mode */
    usbotghs_configure_endpoint(3,USBOTG_HS_EP_TYPE_INT, USBOTG_HS_EP_DIR_BOTH, 64,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_activate_endpoint(3, USB_BACKEND_DRV_EP_DIR_IN);
    usbotghs_activate_endpoint(3, USB_BACKEND_DRV_EP_DIR_OUT);
    usbotghs_set_recv_fifo(&resp[0], 128, 3);
    usbotghs_send_data((uint8_t *)&resp[0], 128, 3);
    usbotghs_send_zlp(3);

    return;
}

void main(void)
{
    init_driver();
    test_fcn_driver_eva() ;
    test_fcn_isr_events() ;
}
