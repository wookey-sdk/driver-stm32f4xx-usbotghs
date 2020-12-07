#ifndef ENTRY_H_
#define ENTRY_H_

#include "libc/types.h"

bool reset_requested = false;

#define MAX_EPx_PKT_SIZE 512

extern volatile uint8_t Frama_C_entropy_source_8 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
extern volatile uint16_t Frama_C_entropy_source_16 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
extern volatile uint32_t Frama_C_entropy_source_32 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));

/*@ requires order: 0 <= min <= max <= 255;
    assigns \result \from min, max, Frama_C_entropy_source_8;
    assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
    ensures result_bounded: min <= \result <= max ;
 */
uint8_t Frama_C_interval_8(uint8_t min, uint8_t max);

/*@ requires order: 0 <= min <= max <= 65535;
    assigns \result \from min, max, Frama_C_entropy_source_16;
    assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
    ensures result_bounded: min <= \result <= max ;
 */
uint16_t Frama_C_interval_16(uint16_t min, uint16_t max);

/*@ requires order: 0 <= min <= max <= 4294967295;
    assigns \result \from min, max, Frama_C_entropy_source_32;
    assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
    ensures result_bounded: min <= \result <= max ;
 */
uint32_t Frama_C_interval_32(uint32_t min, uint32_t max);


/*@
  @ assigns \nothing;
  */
 mbed_error_t handler_ep(uint32_t dev_id, uint32_t size, uint8_t ep_id)
{
        mbed_error_t errcode = MBED_ERROR_NONE;
            return errcode;
}

/*@
  @ assigns \nothing;
  */
mbed_error_t my_handle_inepevent(uint32_t dev_id,
                                 uint32_t size,
                                 uint8_t ep);


/*@
  @ assigns \nothing;
  */
mbed_error_t my_handle_outepevent(uint32_t dev_id,
                                  uint32_t size,
                                  uint8_t ep);

/* local definition of control plane reset handling (not a part of this proof, see
 * usbtcrl proof for the effective control plane reset function
 */
/*@
  @ assigns \nothing;
  */
mbed_error_t usbctrl_handle_reset(uint32_t dev_id);

/*@
  @ assigns \nothing;
  */
mbed_error_t usbctrl_handle_earlysuspend(uint32_t dev_id);

/*@
  @ assigns \nothing;
  */
mbed_error_t usbctrl_handle_usbsuspend(uint32_t dev_id);

/*@
  @ assigns \nothing;
  */
mbed_error_t usbctrl_handle_inepevent(uint32_t dev_id, uint32_t size, uint8_t ep);

/*@
  @ assigns \nothing;
  */
mbed_error_t usbctrl_handle_outepevent(uint32_t dev_id, uint32_t size, uint8_t ep);

/*@
  @ assigns \nothing;
  */
mbed_error_t usbctrl_handle_wakeup(uint32_t dev_id);

void test_fcn_driver_eva(void) ;

#endif/*!ENTRY_H_*/
