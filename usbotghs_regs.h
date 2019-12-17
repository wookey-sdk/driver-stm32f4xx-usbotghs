#ifndef STM32F4XX_USB_HS_REGS_H
# define STM32F4XX_USB_HS_REGS_H

# include "libc/regutils.h"
# include "libc/types.h"
#include "generated/usb_otg_hs.h"

#define USB_HS_DIEPCTL0_MPSIZ_64BYTES      0
#define USB_HS_DIEPCTL0_MPSIZ_32BYTES      1
#define USB_HS_DIEPCTL0_MPSIZ_16BYTES      2
#define USB_HS_DIEPCTL0_MPSIZ_8BYTES       3
#define USB_HS_DIEPCTL_EPTYP_CONTROL       0
#define USB_HS_DIEPCTL_EPTYP_ISOCHRO       1
#define USB_HS_DIEPCTL_EPTYP_BULK          2
#define USB_HS_DIEPCTL_EPTYP_INT           3
#define USB_HS_DOEPCTL_EPTYP_CONTROL       0
#define USB_HS_DOEPCTL_EPTYP_ISOCHRO       1
#define USB_HS_DOEPCTL_EPTYP_BULK          2
#define USB_HS_DOEPCTL_EPTYP_INT           3


/* Only registers needed for device mode are defined */
# define r_CORTEX_M_USB_HS_GOTGCTL		REG_ADDR(USB_OTG_HS_BASE + 0x000)
# define r_CORTEX_M_USB_HS_GOTGINT		REG_ADDR(USB_OTG_HS_BASE + 0x004)
# define r_CORTEX_M_USB_HS_GAHBCFG		REG_ADDR(USB_OTG_HS_BASE + 0x008)
# define r_CORTEX_M_USB_HS_GUSBCFG		REG_ADDR(USB_OTG_HS_BASE + 0x00C)
# define r_CORTEX_M_USB_HS_GRSTCTL		REG_ADDR(USB_OTG_HS_BASE + 0x010)
# define r_CORTEX_M_USB_HS_GINTSTS		REG_ADDR(USB_OTG_HS_BASE + 0x014)
# define r_CORTEX_M_USB_HS_GINTMSK		REG_ADDR(USB_OTG_HS_BASE + 0x018)
# define r_CORTEX_M_USB_HS_GRXSTSR		REG_ADDR(USB_OTG_HS_BASE + 0x01c)
# define r_CORTEX_M_USB_HS_GRXSTSP		REG_ADDR(USB_OTG_HS_BASE + 0x020)
# define r_CORTEX_M_USB_HS_GRXFSIZ		REG_ADDR(USB_OTG_HS_BASE + 0x024)
# define r_CORTEX_M_USB_HS_DIEPTXF0		REG_ADDR(USB_OTG_HS_BASE + 0x028)
# define r_CORTEX_M_USB_HS_GI2CCTL		REG_ADDR(USB_OTG_HS_BASE + 0x030)
# define r_CORTEX_M_USB_HS_GCCFG		REG_ADDR(USB_OTG_HS_BASE + 0x038)
# define r_CORTEX_M_USB_HS_CID			REG_ADDR(USB_OTG_HS_BASE + 0x03c)
# define r_CORTEX_M_USB_HS_DIEPTXF(EP)		REG_ADDR(USB_OTG_HS_BASE + 0x100 + ((EP) * 0x4))
# define r_CORTEX_M_USB_HS_DCFG			REG_ADDR(USB_OTG_HS_BASE + 0x800)
# define r_CORTEX_M_USB_HS_DCTL			REG_ADDR(USB_OTG_HS_BASE + 0x804)
# define r_CORTEX_M_USB_HS_DSTS			REG_ADDR(USB_OTG_HS_BASE + 0x808)
# define r_CORTEX_M_USB_HS_DIEPMSK		REG_ADDR(USB_OTG_HS_BASE + 0x810)
# define r_CORTEX_M_USB_HS_DOEPMSK		REG_ADDR(USB_OTG_HS_BASE + 0x814)
# define r_CORTEX_M_USB_HS_DAINT		REG_ADDR(USB_OTG_HS_BASE + 0x818)
# define r_CORTEX_M_USB_HS_DAINTMSK		REG_ADDR(USB_OTG_HS_BASE + 0x81C)
# define r_CORTEX_M_USB_HS_DVBUSDIS		REG_ADDR(USB_OTG_HS_BASE + 0x828)
# define r_CORTEX_M_USB_HS_DVBUSPULSE		REG_ADDR(USB_OTG_HS_BASE + 0x82c)
# define r_CORTEX_M_USB_HS_DTHRCTL		REG_ADDR(USB_OTG_HS_BASE + 0x830)
# define r_CORTEX_M_USB_HS_DIEPEMPMSK		REG_ADDR(USB_OTG_HS_BASE + 0x834)
# define r_CORTEX_M_USB_HS_DEACHINT		REG_ADDR(USB_OTG_HS_BASE + 0x838)
# define r_CORTEX_M_USB_HS_DEACHINTMSK		REG_ADDR(USB_OTG_HS_BASE + 0x83c)
# define r_CORTEX_M_USB_HS_DIEPEACHMSK1		REG_ADDR(USB_OTG_HS_BASE + 0x844)
# define r_CORTEX_M_USB_HS_DOEPEACHMSK1		REG_ADDR(USB_OTG_HS_BASE + 0x884)
# define r_CORTEX_M_USB_HS_DIEPCTL(EP)		REG_ADDR(USB_OTG_HS_BASE + 0x900 + ((EP) * 0x20))
# define r_CORTEX_M_USB_HS_DIEPINT(EP)		REG_ADDR(USB_OTG_HS_BASE + 0x908 + ((EP) * 0x20))
# define r_CORTEX_M_USB_HS_DIEPTSIZ(EP)		REG_ADDR(USB_OTG_HS_BASE + 0x910 + ((EP) * 0x20))
# define r_CORTEX_M_USB_HS_DIEPDMA(EP)		REG_ADDR(USB_OTG_HS_BASE + 0x914 + ((EP) * 0x20))
# define r_CORTEX_M_USB_HS_DTXFSTS(EP)		REG_ADDR(USB_OTG_HS_BASE + 0x918 + ((EP) * 0x20))
# define r_CORTEX_M_USB_HS_DOEPCTL(EP)		REG_ADDR(USB_OTG_HS_BASE + 0xb00 + ((EP) * 0x20))
# define r_CORTEX_M_USB_HS_DOEPINT(EP)		REG_ADDR(USB_OTG_HS_BASE + 0xb08 + ((EP) * 0x20))
# define r_CORTEX_M_USB_HS_DOEPTSIZ(EP)		REG_ADDR(USB_OTG_HS_BASE + 0xb10 + ((EP) * 0x20))
# define r_CORTEX_M_USB_HS_DOEPDMA(EP)		REG_ADDR(USB_OTG_HS_BASE + 0xb14 + ((EP) * 0x20))
# define r_CORTEX_M_USB_HS_PCGCCTL		REG_ADDR(USB_OTG_HS_BASE + 0xe00)

/* FIFO buffers */
# define USB_HS_DEVICE_FIFO(EP)			REG_ADDR(USB_OTG_HS_BASE + (0x1000 * ((EP) + 1)))

/* Control and status register */
# define USB_HS_GOTGCTL_SRQSCS_Pos		0
# define USB_HS_GOTGCTL_SRQSCS_Msk		((uint32_t)1 << USB_HS_GOTGCTL_SRQSCS_Pos)
# define USB_HS_GOTGCTL_SRQ_Pos			1
# define USB_HS_GOTGCTL_SRQ_Msk			((uint32_t)1 << USB_HS_GOTGCTL_SRQ_Pos)
# define USB_HS_GOTGCTL_HNGSCS_Pos		8
# define USB_HS_GOTGCTL_HNGSCS_Msk		((uint32_t)1 << USB_HS_GOTGCTL_HNGSCS_Pos)
# define USB_HS_GOTGCTL_HNPRQ_Pos		9
# define USB_HS_GOTGCTL_HNPRQ_Msk		((uint32_t)1 << USB_HS_GOTGCTL_HNPRQ_Pos)
# define USB_HS_GOTGCTL_HSHNPEN_Pos		10
# define USB_HS_GOTGCTL_HSHNPEN_Msk		((uint32_t)1 << USB_HS_GOTGCTL_HSHNPEN_Pos)
# define USB_HS_GOTGCTL_DHNPEN_Pos		11
# define USB_HS_GOTGCTL_DHNPEN_Msk		((uint32_t)1 << USB_HS_GOTGCTL_DHNPEN_Pos)
# define USB_HS_GOTGCTL_CIDSTS_Pos		16
# define USB_HS_GOTGCTL_CIDSTS_Msk		((uint32_t)1 << USB_HS_GOTGCTL_CIDSTS_Pos)
# define USB_HS_GOTGCTL_DBCT_Pos		17
# define USB_HS_GOTGCTL_DBCT_Msk		((uint32_t)1 << USB_HS_GOTGCTL_DBCT_Pos)
# define USB_HS_GOTGCTL_ASVLD_Pos		18
# define USB_HS_GOTGCTL_ASVLD_Msk		((uint32_t)1 << USB_HS_GOTGCTL_ASVLD_Pos)
# define USB_HS_GOTGCTL_BSVLD_Pos		19
# define USB_HS_GOTGCTL_BSVLD_Msk		((uint32_t)1 << USB_HS_GOTGCTL_BSVLD_Pos)

/* Interrupt register */
# define UBS_HS_GOTGINT_SEDET_Pos		2
# define UBS_HS_GOTGINT_SEDET_Msk		((uint32_t)1 << USB_HS_GOTGINT_SEDET_Pos)
# define UBS_HS_GOTGINT_SRSSCHG_Pos		8
# define UBS_HS_GOTGINT_SRSSCHG_Msk		((uint32_t)1 << USB_HS_GOTGINT_SRSSCHG_Pos)
# define UBS_HS_GOTGINT_HNSSCHG_Pos		9
# define UBS_HS_GOTGINT_HNSSCHG_Msk		((uint32_t)1 << USB_HS_GOTGINT_HNSSCHG_Pos)
# define UBS_HS_GOTGINT_HNGDET_Pos		17
# define UBS_HS_GOTGINT_HNGDET_Msk		((uint32_t)1 << USB_HS_GOTGINT_HNGDET_Pos)
# define UBS_HS_GOTGINT_ADTOCHG_Pos		18
# define UBS_HS_GOTGINT_ADTOCHG_Msk		((uint32_t)1 << USB_HS_GOTGINT_ADTOCHG_Pos)
# define UBS_HS_GOTGINT_DBCDNE_Pos		19
# define UBS_HS_GOTGINT_DBCDNE_Msk		((uint32_t)1 << USB_HS_GOTGINT_DBCDNE_Pos)

/* AHB configuration register */
# define USB_HS_GAHBCFG_GINTMSK_Pos		0
# define USB_HS_GAHBCFG_GINTMSK_Msk		((uint32_t)1 << USB_HS_GAHBCFG_GINTMSK_Pos)
# define USB_HS_GAHBCFG_HBSTLEN_Pos		1
# define USB_HS_GAHBCFG_HBSTLEN_Msk		((uint32_t)0xf << USB_HS_GAHBCFG_HBSTLEN_Pos)
#	define USB_HS_GAHBCFG_HBSTLEN_SINGLE	0
#	define USB_HS_GAHBCFG_HBSTLEN_INCR	1
#	define USB_HS_GAHBCFG_HBSTLEN_INCR4	3
#	define USB_HS_GAHBCFG_HBSTLEN_INCR8	5
#	define USB_HS_GAHBCFG_HBSTLEN_INCR16	7
# define USB_HS_GAHBCFG_DMAEN_Pos		5
# define USB_HS_GAHBCFG_DMAEN_Msk		((uint32_t)1 << USB_HS_GAHBCFG_DMAEN_Pos)
# define USB_HS_GAHBCFG_TXFELVL_Pos		7
# define USB_HS_GAHBCFG_TXFELVL_Msk		((uint32_t)1 << USB_HS_GAHBCFG_TXFELVL_Pos)
# define USB_HS_GAHBCFG_PTXFELVL_Pos		8
# define USB_HS_GAHBCFG_PTXFELVL_Msk		((uint32_t)1 << USB_HS_GAHBCFG_PTXFELVL_Pos)

/* USB configuration register */
# define USB_HS_GUSBCFG_TOCAL_Pos		0
# define USB_HS_GUSBCFG_TOCAL_Msk		((uint32_t)0x7 << USB_HS_GUSBCFG_TOCAL_Pos)
/* [RB]: the following fields are used by ST stack USB HS initialization
 * but they are NOT in the datasheet ...
 */
# define USB_HS_GUSBCFG_PHYIF_Pos		3
# define USB_HS_GUSBCFG_PHYIF_Msk		((uint32_t)1 << USB_HS_GUSBCFG_PHYIF_Pos)
# define USB_HS_GUSBCFG_UTMISEL_Pos		4
# define USB_HS_GUSBCFG_UTMISEL_Msk		((uint32_t)1 << USB_HS_GUSBCFG_UTMISEL_Pos)
# define USB_HS_GUSBCFG_FSINTF_Pos		5
# define USB_HS_GUSBCFG_FSINTF_Msk		((uint32_t)1 << USB_HS_GUSBCFG_FSINTF_Pos)
/****/
# define USB_HS_GUSBCFG_PHYSEL_Pos		6
# define USB_HS_GUSBCFG_PHYSEL_Msk		((uint32_t)1 << USB_HS_GUSBCFG_PHYSEL_Pos)
/* [RB]: the following fields are used by ST stack USB HS initialization
 * but they are NOT in the datasheet ...
 */
# define USB_HS_GUSBCFG_DDRSEL_Pos		7
# define USB_HS_GUSBCFG_DDRSEL_Msk		((uint32_t)1 << USB_HS_GUSBCFG_DDRSEL_Pos)
/****/
# define USB_HS_GUSBCFG_SRPCAP_Pos		8
# define USB_HS_GUSBCFG_SRPCAP_Msk		((uint32_t)1 << USB_HS_GUSBCFG_SRPCAP_Pos)
# define USB_HS_GUSBCFG_HNPCAP_Pos		9
# define USB_HS_GUSBCFG_HNPCAP_Msk		((uint32_t)1 << USB_HS_GUSBCFG_HNPCAP_Pos)
# define USB_HS_GUSBCFG_TRDT_Pos		10
# define USB_HS_GUSBCFG_TRDT_Msk		((uint32_t)0xf << USB_HS_GUSBCFG_TRDT_Pos)
# define USB_HS_GUSBCFG_PHYLPCS_Pos		15
# define USB_HS_GUSBCFG_PHYLPCS_Msk		((uint32_t)1 << USB_HS_GUSBCFG_PHYLPCS_Pos)
# define USB_HS_GUSBCFG_ULPIFSLS_Pos		17
# define USB_HS_GUSBCFG_ULPIFSLS_Msk		((uint32_t)1 << USB_HS_GUSBCFG_ULPIFSLS_Pos)
# define USB_HS_GUSBCFG_ULPIAR_Pos		18
# define USB_HS_GUSBCFG_ULPIAR_Msk		((uint32_t)1 << USB_HS_GUSBCFG_ULPIAR_Pos)
# define USB_HS_GUSBCFG_ULPICSM_Pos		19
# define USB_HS_GUSBCFG_ULPICSM_Msk		((uint32_t)1 << USB_HS_GUSBCFG_ULPICSM_Pos)
# define USB_HS_GUSBCFG_ULPIEVBUSD_Pos		20
# define USB_HS_GUSBCFG_ULPIEVBUSD_Msk		((uint32_t)1 << USB_HS_GUSBCFG_ULPIEVBUSD_Pos)
# define USB_HS_GUSBCFG_ULPIVBUSI_Pos		21
# define USB_HS_GUSBCFG_ULPIVBUSI_Msk		((uint32_t)1 << USB_HS_GUSBCFG_ULPIVBUSI_Pos)
# define USB_HS_GUSBCFG_TSDPS_Pos		22
# define USB_HS_GUSBCFG_TSDPS_Msk		((uint32_t)1 << USB_HS_GUSBCFG_TSDPS_Pos)
# define USB_HS_GUSBCFG_PCCI_Pos		23
# define USB_HS_GUSBCFG_PCCI_Msk		((uint32_t)1 << USB_HS_GUSBCFG_PCCI_Pos)
# define USB_HS_GUSBCFG_PTCI_Pos		24
# define USB_HS_GUSBCFG_PTCI_Msk		((uint32_t)1 << USB_HS_GUSBCFG_PTCI_Pos)
# define USB_HS_GUSBCFG_ULPIIPD_Pos		25
# define USB_HS_GUSBCFG_ULPIIPD_Msk		((uint32_t)1 << USB_HS_GUSBCFG_ULPIIPD_Pos)
# define USB_HS_GUSBCFG_FHMOD_Pos		29
# define USB_HS_GUSBCFG_FHMOD_Msk		((uint32_t)1 << USB_HS_GUSBCFG_FHMOD_Pos)
# define USB_HS_GUSBCFG_FDMOD_Pos		30
# define USB_HS_GUSBCFG_FDMOD_Msk		((uint32_t)1 << USB_HS_GUSBCFG_FDMOD_Pos)
# define USB_HS_GUSBCFG_CTXPKT_Pos		31
# define USB_HS_GUSBCFG_CTXPKT_Msk		((uint32_t)1 << USB_HS_GUSBCFG_CTXPKT_Pos)

/* Reset register */
# define USB_HS_GRSTCTL_CSRST_Pos		0
# define USB_HS_GRSTCTL_CSRST_Msk		((uint32_t)1 << USB_HS_GRSTCTL_CSRST_Pos)
# define USB_HS_GRSTCTL_HSRST_Pos		1
# define USB_HS_GRSTCTL_HSRST_Msk		((uint32_t)1 << USB_HS_GRSTCTL_HSRST_Pos)
# define USB_HS_GRSTCTL_FCRST_Pos		2
# define USB_HS_GRSTCTL_FCRST_Msk		((uint32_t)1 << USB_HS_GRSTCTL_FCRST_Pos)
# define USB_HS_GRSTCTL_RXFFLSH_Pos		4
# define USB_HS_GRSTCTL_RXFFLSH_Msk		((uint32_t)1 << USB_HS_GRSTCTL_RXFFLSH_Pos)
# define USB_HS_GRSTCTL_TXFFLSH_Pos		5
# define USB_HS_GRSTCTL_TXFFLSH_Msk		((uint32_t)1 << USB_HS_GRSTCTL_TXFFLSH_Pos)
# define USB_HS_GRSTCTL_TXFNUM_Pos		6
# define USB_HS_GRSTCTL_TXFNUM_Msk		((uint32_t)0x1f << USB_HS_GRSTCTL_TXFNUM_Pos)
# define USB_HS_GRSTCTL_DMAREQ_Pos		30
# define USB_HS_GRSTCTL_DMAREQ_Msk		((uint32_t)1 << USB_HS_GRSTCTL_DMAREQ_Pos)
# define USB_HS_GRSTCTL_AHBIDL_Pos		31
# define USB_HS_GRSTCTL_AHBIDL_Msk		((uint32_t)1 << USB_HS_GRSTCTL_AHBIDL_Pos)

/* Core interrupt register */
# define USB_HS_GINTSTS_CMOD_Pos		0
# define USB_HS_GINTSTS_CMOD_Msk		((uint32_t)1 << USB_HS_GINTSTS_CMOD_Pos)
# define USB_HS_GINTSTS_MMIS_Pos		1
# define USB_HS_GINTSTS_MMIS_Msk		((uint32_t)1 << USB_HS_GINTSTS_MMIS_Pos)
# define USB_HS_GINTSTS_OTGINT_Pos		2
# define USB_HS_GINTSTS_OTGINT_Msk		((uint32_t)1 << USB_HS_GINTSTS_OTGINT_Pos)
# define USB_HS_GINTSTS_SOF_Pos			3
# define USB_HS_GINTSTS_SOF_Msk			((uint32_t)1 << USB_HS_GINTSTS_SOF_Pos)
# define USB_HS_GINTSTS_RXFLVL_Pos		4
# define USB_HS_GINTSTS_RXFLVL_Msk		((uint32_t)1 << USB_HS_GINTSTS_RXFLVL_Pos)
# define USB_HS_GINTSTS_NPTXFE_Pos		5
# define USB_HS_GINTSTS_NPTXFE_Msk		((uint32_t)1 << USB_HS_GINTSTS_NPTXFE_Pos)
# define USB_HS_GINTSTS_GINAKEFF_Pos		6
# define USB_HS_GINTSTS_GINAKEFF_Msk		((uint32_t)1 << USB_HS_GINTSTS_GINAKEFF_Pos)
# define USB_HS_GINTSTS_GOUTNAKEFF_Pos		7
# define USB_HS_GINTSTS_GOUTNAKEFF_Msk		((uint32_t)1 << USB_HS_GINTSTS_GOUTNAKEFF_Pos)
# define USB_HS_GINTSTS_ESUSP_Pos		10
# define USB_HS_GINTSTS_ESUSP_Msk		((uint32_t)1 << USB_HS_GINTSTS_ESUSP_Pos)
# define USB_HS_GINTSTS_USBSUSP_Pos		11
# define USB_HS_GINTSTS_USBSUSP_Msk		((uint32_t)1 << USB_HS_GINTSTS_USBSUSP_Pos)
# define USB_HS_GINTSTS_USBRST_Pos		12
# define USB_HS_GINTSTS_USBRST_Msk		((uint32_t)1 << USB_HS_GINTSTS_USBRST_Pos)
# define USB_HS_GINTSTS_ENUMDNE_Pos		13
# define USB_HS_GINTSTS_ENUMDNE_Msk		((uint32_t)1 << USB_HS_GINTSTS_ENUMDNE_Pos)
# define USB_HS_GINTSTS_ISOODRP_Pos		14
# define USB_HS_GINTSTS_ISOODRP_Msk		((uint32_t)1 << USB_HS_GINTSTS_ISOODRP_Pos)
# define USB_HS_GINTSTS_EOPF_Pos		15
# define USB_HS_GINTSTS_EOPF_Msk		((uint32_t)1 << USB_HS_GINTSTS_EOPF_Pos)
# define USB_HS_GINTSTS_EPMISM_Pos       	17
# define USB_HS_GINTSTS_EPMISM_Msk       	((uint32_t)1 << USB_FS_GINTSTS_EPMISM_Pos)
# define USB_HS_GINTSTS_IEPINT_Pos		18
# define USB_HS_GINTSTS_IEPINT_Msk		((uint32_t)1 << USB_HS_GINTSTS_IEPINT_Pos)
# define USB_HS_GINTSTS_OEPINT_Pos		19
# define USB_HS_GINTSTS_OEPINT_Msk		((uint32_t)1 << USB_HS_GINTSTS_OEPINT_Pos)
# define USB_HS_GINTSTS_IISOIXFR_Pos		20
# define USB_HS_GINTSTS_IISOIXFR_Msk		((uint32_t)1 << USB_HS_GINTSTS_IISOIXFR_Pos)
# define USB_HS_GINTSTS_IPXFR_Pos		21
# define USB_HS_GINTSTS_IPXFR_Msk		((uint32_t)1 << USB_HS_GINTSTS_IPXFR_Pos)
# define USB_HS_GINTSTS_DATAFSUSP_Pos		22
# define USB_HS_GINTSTS_DATAFSUSP_Msk		((uint32_t)1 << USB_HS_GINTSTS_DATAFSUSP_Pos)
# define USB_HS_GINTSTS_HPRTINT_Pos		24
# define USB_HS_GINTSTS_HPRTINT_Msk		((uint32_t)1 << USB_HS_GINTSTS_HPRTINT_Pos)
# define USB_HS_GINTSTS_HCINT_Pos		25
# define USB_HS_GINTSTS_HCINT_Msk		((uint32_t)1 << USB_HS_GINTSTS_HCINT_Pos)
# define USB_HS_GINTSTS_PTXFE_Pos		26
# define USB_HS_GINTSTS_PTXFE_Msk		((uint32_t)1 << USB_HS_GINTSTS_PTXFE_Pos)
# define USB_HS_GINTSTS_CIDSCHG_Pos		28
# define USB_HS_GINTSTS_CIDSCHG_Msk		((uint32_t)1 << USB_HS_GINTSTS_CIDSCHG_Pos)
# define USB_HS_GINTSTS_DISCINT_Pos		29
# define USB_HS_GINTSTS_DISCINT_Msk		((uint32_t)1 << USB_HS_GINTSTS_DISCINT_Pos)
# define USB_HS_GINTSTS_SRQINT_Pos		30
# define USB_HS_GINTSTS_SRQINT_Msk		((uint32_t)1 << USB_HS_GINTSTS_SRQINT_Pos)
# define USB_HS_GINTSTS_WKUPINT_Pos		31
# define USB_HS_GINTSTS_WKUPINT_Msk		((uint32_t)1 << USB_HS_GINTSTS_WKUPINT_Pos)

/* Interrupt mask register */
# define USB_HS_GINTMSK_MMISM_Pos		1
# define USB_HS_GINTMSK_MMISM_Msk		((uint32_t)1 << USB_HS_GINTMSK_MMISM_Pos)
# define USB_HS_GINTMSK_OTGINT_Pos		2
# define USB_HS_GINTMSK_OTGINT_Msk		((uint32_t)1 << USB_HS_GINTMSK_OTGINT_Pos)
# define USB_HS_GINTMSK_SOFM_Pos		3
# define USB_HS_GINTMSK_SOFM_Msk		((uint32_t)1 << USB_HS_GINTMSK_SOFM_Pos)
# define USB_HS_GINTMSK_RXFLVLM_Pos		4
# define USB_HS_GINTMSK_RXFLVLM_Msk		((uint32_t)1 << USB_HS_GINTMSK_RXFLVLM_Pos)
# define USB_HS_GINTMSK_NPTXFEM_Pos		5
# define USB_HS_GINTMSK_NPTXFEM_Msk		((uint32_t)1 << USB_HS_GINTMSK_NPTXFEM_Pos)
# define USB_HS_GINTMSK_GINAKEFFM_Pos		6
# define USB_HS_GINTMSK_GINAKEFFM_Msk		((uint32_t)1 << USB_HS_GINTMSK_GINAKEFFM_Pos)
# define USB_HS_GINTMSK_GOUTNAKEFFM_Pos		7
# define USB_HS_GINTMSK_GOUTNAKEFFM_Msk		((uint32_t)1 << USB_HS_GINTMSK_GOUTNAKEFFM_Pos)
# define USB_HS_GINTMSK_ESUSPM_Pos		10
# define USB_HS_GINTMSK_ESUSPM_Msk		((uint32_t)1 << USB_HS_GINTMSK_ESUSPM_Pos)
# define USB_HS_GINTMSK_USBSUSPM_Pos		11
# define USB_HS_GINTMSK_USBSUSPM_Msk		((uint32_t)1 << USB_HS_GINTMSK_USBSUSPM_Pos)
# define USB_HS_GINTMSK_USBRST_Pos		12
# define USB_HS_GINTMSK_USBRST_Msk		((uint32_t)1 << USB_HS_GINTMSK_USBRST_Pos)
# define USB_HS_GINTMSK_ENUMDNEM_Pos		13
# define USB_HS_GINTMSK_ENUMDNEM_Msk		((uint32_t)1 << USB_HS_GINTMSK_ENUMDNEM_Pos)
# define USB_HS_GINTMSK_ISOODRPM_Pos		14
# define USB_HS_GINTMSK_ISOODRPM_Msk		((uint32_t)1 << USB_HS_GINTMSK_ISOODRPM_Pos)
# define USB_HS_GINTMSK_EOPFM_Pos		15
# define USB_HS_GINTMSK_EOPFM_Msk		((uint32_t)1 << USB_HS_GINTMSK_EOPFM_Pos)
# define USB_HS_GINTMSK_EPMISM_Pos		17
# define USB_HS_GINTMSK_EPMISM_Msk		((uint32_t)1 << USB_HS_GINTMSK_EPMISM_Pos)
# define USB_HS_GINTMSK_IEPINT_Pos		18
# define USB_HS_GINTMSK_IEPINT_Msk		((uint32_t)1 << USB_HS_GINTMSK_IEPINT_Pos)
# define USB_HS_GINTMSK_OEPINT_Pos		19
# define USB_HS_GINTMSK_OEPINT_Msk		((uint32_t)1 << USB_HS_GINTMSK_OEPINT_Pos)
# define USB_HS_GINTMSK_IISOIXFRM_Pos		20
# define USB_HS_GINTMSK_IISOIXFRM_Msk		((uint32_t)1 << USB_HS_GINTMSK_IISOIXFRM_Pos)
# define USB_HS_GINTMSK_IISOOXFRM_Pos		21
# define USB_HS_GINTMSK_IISOOXFRM_Msk		((uint32_t)1 << USB_HS_GINTMSK_IISOOXFRM_Pos)
# define USB_HS_GINTMSK_FSUSPM_Pos		22
# define USB_HS_GINTMSK_FSUSPM_Msk		((uint32_t)1 << USB_HS_GINTMSK_FSUSPM_Pos)
# define USB_HS_GINTMSK_PRTIM_Pos		24
# define USB_HS_GINTMSK_PRTIM_Msk		((uint32_t)1 << USB_HS_GINTMSK_PRTIM_Pos)
# define USB_HS_GINTMSK_HCIM_Pos		25
# define USB_HS_GINTMSK_HCIM_Msk		((uint32_t)1 << USB_HS_GINTMSK_HCIM_Pos)
# define USB_HS_GINTMSK_PTXFEM_Pos		26
# define USB_HS_GINTMSK_PTXFEM_Msk		((uint32_t)1 << USB_HS_GINTMSK_PTXFEM_Pos)
# define USB_HS_GINTMSK_CIDSCHGM_Pos		28
# define USB_HS_GINTMSK_CIDSCHGM_Msk		((uint32_t)1 << USB_HS_GINTMSK_CIDSCHGM_Pos)
# define USB_HS_GINTMSK_DISCINT_Pos		29
# define USB_HS_GINTMSK_DISCINT_Msk		((uint32_t)1 << USB_HS_GINTMSK_DISCINT_Pos)
# define USB_HS_GINTMSK_SRQIM_Pos		30
# define USB_HS_GINTMSK_SRQIM_Msk		((uint32_t)1 << USB_HS_GINTMSK_SRQIM_Pos)
# define USB_HS_GINTMSK_WUIM_Pos		31
# define USB_HS_GINTMSK_WUIM_Msk		((uint32_t)1 << USB_HS_GINTMSK_WUIM_Pos)

/* Receive status debug read/pop registers */
# define USB_HS_GRXSTSR_EPNUM_Pos		0
# define USB_HS_GRXSTSR_EPNUM_Msk		((uint32_t)0xf << USB_HS_GRXSTSR_EPNUM_Pos)
# define USB_HS_GRXSTSR_BCNT_Pos		4
# define USB_HS_GRXSTSR_BCNT_Msk		((uint32_t)0x7ff << USB_HS_GRXSTSR_BCNT_Pos)
# define USB_HS_GRXSTSR_DPID_Pos		15
# define USB_HS_GRXSTSR_DPID_Msk		((uint32_t)0x3 << USB_HS_GRXSTSR_DPID_Pos)
# define USB_HS_GRXSTSR_PKTSTS_Pos		17
# define USB_HS_GRXSTSR_PKTSTS_Msk		((uint32_t)0xf << USB_HS_GRXSTSR_PKTSTS_Pos)
#	define USB_HS_GRXSTSR_PKTSTS_GLOBAL_OUT_NAK		1
#	define USB_HS_GRXSTSR_PKTSTS_OUT_DATA			2
#	define USB_HS_GRXSTSR_PKTSTS_OUT_TRANFER_COMPLETE	3
#	define USB_HS_GRXSTSR_PKTSTS_SETUP_TRANSACTION_COMPLETE	4
#	define USB_HS_GRXSTSR_PKTSTS_SETUP_DATA			6
# define USB_HS_GRXSTSR_FRMNUM_Pos		21
# define USB_HS_GRXSTSR_FRMNUM_Msk		((uint32_t)0x7f << USB_HS_GRXSTSR_FRMNUM_Pos)

/* Receive FIFO size register */
# define USB_HS_GRXFSIZ_RXFD_Pos		0
# define USB_HS_GRXFSIZ_RXFD_Msk		((uint32_t)0xffff << USB_HS_GRXFSIZ_RXFD_Pos)

/* EP 0 transmit FIFO size register */
# define USB_HS_TX0FSIZ_TX0FSA_Pos		0
# define USB_HS_TX0FSIZ_TX0FSA_Msk		((uint32_t)0xffff << USB_HS_TX0FSIZ_TX0FSA_Pos)
# define USB_HS_TX0FSIZ_T0XFD_Pos		16
# define USB_HS_TX0FSIZ_T0XFD_Msk		((uint32_t)0xffff << USB_HS_TX0FSIZ_T0XFD_Pos)

/* I2C access register */
# define USB_HS_GI2CCTL_RWDATA_Pos		0
# define USB_HS_GI2CCTL_RWDATA_Msk		((uint32_t)0xff << USB_HS_GIT2CCTL_RWDATA_Pos)
# define USB_HS_GI2CCTL_REGADDR_Pos		8
# define USB_HS_GI2CCTL_REGADDR_Msk		((uint32_t)0xff << USB_HS_GIT2CCTL_REGADDR_Pos)
# define USB_HS_GI2CCTL_ADDR_Pos		16
# define USB_HS_GI2CCTL_ADDR_Msk		((uint32_t)0x7f << USB_HS_GIT2CCTL_ADDR_Pos)
# define USB_HS_GI2CCTL_I2CEN_Pos		23
# define USB_HS_GI2CCTL_I2CEN_Msk		((uint32_t)1 << USB_HS_GIT2CCTL_I2CEN_Pos)
# define USB_HS_GI2CCTL_ACK_Pos			24
# define USB_HS_GI2CCTL_ACK_Msk			((uint32_t)1 << USB_HS_GIT2CCTL_ACK_Pos)
# define USB_HS_GI2CCTL_I2CDEVADR_Pos		26
# define USB_HS_GI2CCTL_I2CDEVADR_Msk		((uint32_t)0x3 << USB_HS_GIT2CCTL_I2CDEVADR_Pos)
# define USB_HS_GI2CCTL_I2CDATSE0_Pos		28
# define USB_HS_GI2CCTL_I2CDATSE0_Msk		((uint32_t)1 << USB_HS_GIT2CCTL_I2CDATSE0_Pos)
# define USB_HS_GI2CCTL_RW_Pos			30
# define USB_HS_GI2CCTL_RW_Msk			((uint32_t)1 << USB_HS_GIT2CCTL_RW_Pos)
# define USB_HS_GI2CCTL_BSYDNE_Pos		31
# define USB_HS_GI2CCTL_BSYDNE_Msk		((uint32_t)1 << USB_HS_GIT2CCTL_BSYDNE_Pos)

/* General core configuration register */
# define USB_HS_GCCFG_PWRDWN_Pos		16
# define USB_HS_GCCFG_PWRDWN_Msk		((uint32_t)1 << USB_HS_GCCFG_PWRDWN_Pos)
# define USB_HS_GCCFG_I2CPADEN_Pos		17
# define USB_HS_GCCFG_I2CPADEN_Msk		((uint32_t)1 << USB_HS_GCCFG_I2CPADEN_Pos)
# define USB_HS_GCCFG_VBUSASEN_Pos		18
# define USB_HS_GCCFG_VBUSASEN_Msk		((uint32_t)1 << USB_HS_GCCFG_VBUSASEN_Pos)
# define USB_HS_GCCFG_VBUSBSEN_Pos		19
# define USB_HS_GCCFG_VBUSBSEN_Msk		((uint32_t)1 << USB_HS_GCCFG_VBUSBSEN_Pos)
# define USB_HS_GCCFG_SOFOUTEN_Pos		20
# define USB_HS_GCCFG_SOFOUTEN_Msk		((uint32_t)1 << USB_HS_GCCFG_SOFOUTEN_Pos)
# define USB_HS_GCCFG_NOVBUSSENS_Pos		21
# define USB_HS_GCCFG_NOVBUSSENS_Msk		((uint32_t)1 << USB_HS_GCCFG_NOVBUSSENS_Pos)

/* Core ID register */
# define USB_HS_CID_PRODUCT_ID_Pos		0
# define USB_HS_CID_PRODUCT_ID_Msk		((uint32_t)0xffffffff << USB_HS_CID_PRODUCT_ID_Pos)

/* Device IN endpoint transmit FIFO size register */
# define USB_HS_DIEPTXF_INEPTXSA_Pos		0
# define USB_HS_DIEPTXF_INEPTXSA_Msk		((uint32_t)0xffff << USB_HS_DIEPTXF_INEPTXSA_Pos)
# define USB_HS_DIEPTXF_INEPTXFD_Pos		16
# define USB_HS_DIEPTXF_INEPTXFD_Msk		((uint32_t)0xffff << USB_HS_DIEPTXF_INEPTXFD_Pos)

/* Device configuration register */
# define USB_HS_DCFG_DSPD_Pos			0
# define USB_HS_DCFG_DSPD_Msk			((uint32_t)0x3 << USB_HS_DCFG_DSPD_Pos)
#	define USB_HS_DCFG_DSPD_HS		0
#	define USB_HS_DCFG_DSPD_FS_ULPI		1
#	define USB_HS_DCFG_DSPD_FS		3
# define USB_HS_DCFG_NZLSOHSK_Pos		2
# define USB_HS_DCFG_NZLSOHSK_Msk		((uint32_t)1 << USB_HS_DCFG_NZLSOHSK_Pos)
# define USB_HS_DCFG_DAD_Pos			4
# define USB_HS_DCFG_DAD_Msk			((uint32_t)0x7f << USB_HS_DCFG_DAD_Pos)
# define USB_HS_DCFG_PFIVL_Pos			11
# define USB_HS_DCFG_PFIVL_Msk			((uint32_t)0x3 << USB_HS_DCFG_DAD_Pos)
#	define USB_HS_DCFG_PFIVL_INTERVAL_80	0
#	define USB_HS_DCFG_PFIVL_INTERVAL_85	1
#	define USB_HS_DCFG_PFIVL_INTERVAL_90	2
#	define USB_HS_DCFG_PFIVL_INTERVAL_95	3
# define USB_HS_DCFG_PERSCHIVL_Pos		24
# define USB_HS_DCFG_PERSCHIVL_Msk		((uint32_t)0x3 << USB_HS_DCFG_DAD_Pos)

/* Device control register */
# define USB_HS_DCTL_RWUSIG_Pos			0
# define USB_HS_DCTL_RWUSIG_Msk			((uint32_t)1 << USB_HS_DCTL_RWUSIG_Pos)
# define USB_HS_DCTL_SDIS_Pos			1
# define USB_HS_DCTL_SDIS_Msk			((uint32_t)1 << USB_HS_DCTL_SDIS_Pos)
# define USB_HS_DCTL_GINSTS_Pos			2
# define USB_HS_DCTL_GINSTS_Msk			((uint32_t)1 << USB_HS_DCTL_GINSTS_Pos)
# define USB_HS_DCTL_GONSTS_Pos			3
# define USB_HS_DCTL_GONSTS_Msk			((uint32_t)1 << USB_HS_DCTL_GONSTS_Pos)
# define USB_HS_DCTL_TCTL_Pos			4
# define USB_HS_DCTL_TCTL_Msk			((uint32_t)0x7 << USB_HS_DCTL_TCTL_Pos)
# define USB_HS_DCTL_SGINAK_Pos			7
# define USB_HS_DCTL_SGINAK_Msk			((uint32_t)1 << USB_HS_DCTL_SGINAK_Pos)
# define USB_HS_DCTL_CGINAK_Pos			8
# define USB_HS_DCTL_CGINAK_Msk			((uint32_t)1 << USB_HS_DCTL_CGINAK_Pos)
# define USB_HS_DCTL_SGONAK_Pos			9
# define USB_HS_DCTL_SGONAK_Msk			((uint32_t)1 << USB_HS_DCTL_SGONAK_Pos)
# define USB_HS_DCTL_CGONAK_Pos			10
# define USB_HS_DCTL_CGONAK_Msk			((uint32_t)1 << USB_HS_DCTL_CGONAK_Pos)
# define USB_HS_DCTL_POPRGDNE_Pos		11
# define USB_HS_DCTL_POPRGDNE_Msk		((uint32_t)1 << USB_HS_DCTL_POPRGDNE_Pos)

/* Device status register */
# define USB_HS_DSTS_SUSPSTS_Pos		0
# define USB_HS_DSTS_SUSPSTS_Msk		((uint32_t)1 << USB_HS_DSTS_SUSPSTS_Pos)
# define USB_HS_DSTS_ENUMSPD_Pos		1
# define USB_HS_DSTS_ENUMSPD_Msk		((uint32_t)0x3 << USB_HS_DSTS_ENUMSPD_Pos)
#	define USB_HS_DSTS_ENUMSPD_HS			((uint8_t)0)
#	define USB_HS_DSTS_ENUMSPD_FS			((uint8_t)3)
# define USB_HS_DSTS_EERR_Pos			3
# define USB_HS_DSTS_EERR_Msk			((uint32_t)1 << USB_HS_DSTS_EERR_Pos)
# define USB_HS_DSTS_FNSOF_Pos			8
# define USB_HS_DSTS_FNSOF_Msk			((uint32_t)0x3fff << USB_HS_DSTS_FNSOF_Pos)

/* Device IN enpoint common interrupt mask register */
# define USB_HS_DIEPMSK_XFRCM_Pos		0
# define USB_HS_DIEPMSK_XFRCM_Msk		((uint32_t)1 << USB_HS_DIEPMSK_XFRCM_Pos)
# define USB_HS_DIEPMSK_EPDM_Pos		1
# define USB_HS_DIEPMSK_EPDM_Msk		((uint32_t)1 << USB_HS_DIEPMSK_EPDM_Pos)
# define USB_HS_DIEPMSK_TOM_Pos			3
# define USB_HS_DIEPMSK_TOM_Msk			((uint32_t)1 << USB_HS_DIEPMSK_TOM_Pos)
# define USB_HS_DIEPMSK_ITTXFEMSK_Pos		4
# define USB_HS_DIEPMSK_ITTXFEMSK_Msk		((uint32_t)1 << USB_HS_DIEPMSK_ITTXFEMSK_Pos)
# define USB_HS_DIEPMSK_INEPNMM_Pos		5
# define USB_HS_DIEPMSK_INEPNMM_Msk		((uint32_t)1 << USB_HS_DIEPMSK_INEPNMM_Pos)
# define USB_HS_DIEPMSK_INEMNEM_Pos		6
# define USB_HS_DIEPMSK_INEMNEM_Msk		((uint32_t)1 << USB_HS_DIEPMSK_INEMNEM_Pos)
# define USB_HS_DIEPMSK_TXFURM_Pos		8
# define USB_HS_DIEPMSK_TXFURM_Msk		((uint32_t)1 << USB_HS_DIEPMSK_TXFURM_Pos)
# define USB_HS_DIEPMSK_BIM_Pos			9
# define USB_HS_DIEPMSK_BIM_Msk			((uint32_t)1 << USB_HS_DIEPMSK_BIM_Pos)

/* Device OUT endpoint common interrupt mask register */
# define USB_HS_DOEPMSK_XFRCM_Pos		0
# define USB_HS_DOEPMSK_XFRCM_Msk		((uint32_t)1 << USB_HS_DOEPMSK_XFRCM_Pos)
# define USB_HS_DOEPMSK_EPDM_Pos		1
# define USB_HS_DOEPMSK_EPDM_Msk		((uint32_t)1 << USB_HS_DOEPMSK_XXX_Pos)
# define USB_HS_DOEPMSK_STUPM_Pos		3
# define USB_HS_DOEPMSK_STUPM_Msk		((uint32_t)1 << USB_HS_DOEPMSK_STUPM_Pos)
# define USB_HS_DOEPMSK_OTEPDM_Pos		4
# define USB_HS_DOEPMSK_OTEPDM_Msk		((uint32_t)1 << USB_HS_DOEPMSK_OTEPDM_Pos)
# define USB_HS_DOEPMSK_B2BSTUP_Pos		6
# define USB_HS_DOEPMSK_B2BSTUP_Msk		((uint32_t)1 << USB_HS_DOEPMSK_B2BSTUP_Pos)
# define USB_HS_DOEPMSK_OPEM_Pos		8
# define USB_HS_DOEPMSK_OPEM_Msk		((uint32_t)1 << USB_HS_DOEPMSK_OPEM_Pos)
# define USB_HS_DOEPMSK_BOIM_Pos		9
# define USB_HS_DOEPMSK_BOIM_Msk		((uint32_t)1 << USB_HS_DOEPMSK_BOIM_Pos)

/* Device all endpoints interrupt register */
# define USB_HS_DAINT_IEPINT(EP)		((uint32_t)1 << (EP))
# define USB_HS_DAINT_OEPINT(EP)		((uint32_t)1 << ((EP) + 16))

/* Device all endpoints interrupt mask register */
# define USB_HS_DAINTMSK_IEPM(EP)		((uint32_t)1 << (EP))
# define USB_HS_DAINTMSK_OEPM(EP)		((uint32_t)1 << ((EP) + 16))

/* Device Vbus discharge time register */
# define USB_HS_DVBUSDIS_VBUSDT_Pos		0
# define USB_HS_DVBUSDIS_VBUSDT_Msk		((uint32_t)0xffff << USB_HS_DVBUSDIS_VBUSDT_Pos)

/* Device Vbus pulsing time register */
# define USB_HS_DVBUSPULSE_DVBUSP_Pos		0
# define USB_HS_DVBUSPULSE_DVBUSP_Msk		((uint32_t)0xfff << USB_HS_DVBUSPULSE_DVBUSP_Pos)

/* Device threshold control register */
# define USB_HS_DTHRCTL_NONISOTHREN_Pos		0
# define USB_HS_DTHRCTL_NONISOTHREN_Msk		((uint32_t)1 << USB_HS_DTHRCTL_NONISOTHREN_Pos)
# define USB_HS_DTHRCTL_ISOTHREN_Pos		1
# define USB_HS_DTHRCTL_ISOTHREN_Msk		((uint32_t)1 << USB_HS_DTHRCTL_ISOTHREN_Pos)
# define USB_HS_DTHRCTL_TXTHRLEN_Pos		2
# define USB_HS_DTHRCTL_TXTHRLEN_Msk		((uint32_t)0x1ff << USB_HS_DTHRCTL_TXTHRLEN_Pos)
# define USB_HS_DTHRCTL_RXTHREN_Pos		16
# define USB_HS_DTHRCTL_RXTHREN_Msk		((uint32_t)1 << USB_HS_DTHRCTL_RXTHREN_Pos)
# define USB_HS_DTHRCTL_RXTHRLEN_Pos		17
# define USB_HS_DTHRCTL_RXTHRLEN_Msk		((uint32_t)0x1ff << USB_HS_DTHRCTL_RXTHRLEN_Pos)
# define USB_HS_DTHRCTL_ARPEN_Pos		27
# define USB_HS_DTHRCTL_ARPEN_Msk		((uint32_t)1 << USB_HS_DTHRCTL_ARPEN_Pos)

/* Device IN EP FIFO empty interrupt mask register */
# define USB_HS_DIEPEMPMSK_INEPTXFEM(EP)	((uint32_t)1 << (EP))

/* Device each EP interrupt register */
# define USB_HS_DEACHINT_IEP1INT_Pos		1
# define USB_HS_DEACHINT_IEP1INT_Msk		((uint32_t)1 << USB_HS_DEACHINT_IEP1INT_Pos)
# define USB_HS_DEACHINT_OEP1INT_Pos		17
# define USB_HS_DEACHINT_OEP1INT_Msk		((uint32_t)1 << USB_HS_DEACHINT_OEP1INT_Pos)

/* Device each EP interrupt register mask */
# define USB_HS_DEACHINTMSK_IEP1INTM_Pos	1
# define USB_HS_DEACHINTMSK_IEP1INTM_Msk	((uint32_t)1 << USB_HS_DEACHINTMSK_IEP1INTM_Pos)
# define USB_HS_DEACHINTMSK_OEP1INTM_Pos	17
# define USB_HS_DEACHINTMSK_OEP1INTM_Msk	((uint32_t)1 << USB_HS_DEACHINTMSK_OEP1INTM_Pos)

/* Device each IN EP1 interrupt register */
# define USB_HS_DIEPEACHMSK1_XFRCM_Pos		0
# define USB_HS_DIEPEACHMSK1_XFRCM_Msk		((uint32_t)1 << USB_HS_DIEPEACHMSK1_XFRCM_Pos)
# define USB_HS_DIEPEACHMSK1_EPDM_Pos		1
# define USB_HS_DIEPEACHMSK1_EPDM_Msk		((uint32_t)1 << USB_HS_DIEPEACHMSK1_EPDM_Pos)
# define USB_HS_DIEPEACHMSK1_TOM_Pos		3
# define USB_HS_DIEPEACHMSK1_TOM_Msk		((uint32_t)1 << USB_HS_DIEPEACHMSK1_TOM_Pos)
# define USB_HS_DIEPEACHMSK1_ITTXFEMSK_Pos	4
# define USB_HS_DIEPEACHMSK1_ITTXFEMSK_Msk	((uint32_t)1 << USB_HS_DIEPEACHMSK1_ITTXFEMSK_Pos)
# define USB_HS_DIEPEACHMSK1_INEPNMM_Pos	5
# define USB_HS_DIEPEACHMSK1_INEPNMM_Msk	((uint32_t)1 << USB_HS_DIEPEACHMSK1_INEPNMM_Pos)
# define USB_HS_DIEPEACHMSK1_INEPNEM_Pos	6
# define USB_HS_DIEPEACHMSK1_INEPNEM_Msk	((uint32_t)1 << USB_HS_DIEPEACHMSK1_INEPNEM_Pos)
# define USB_HS_DIEPEACHMSK1_TXFURM_Pos		8
# define USB_HS_DIEPEACHMSK1_TXFURM_Msk		((uint32_t)1 << USB_HS_DIEPEACHMSK1_TXFURM_Pos)
# define USB_HS_DIEPEACHMSK1_BIM_Pos		9
# define USB_HS_DIEPEACHMSK1_BIM_Msk		((uint32_t)1 << USB_HS_DIEPEACHMSK1_BIM_Pos)
# define USB_HS_DIEPEACHMSK1_NAKM_Pos		13
# define USB_HS_DIEPEACHMSK1_NAKM_Msk		((uint32_t)1 << USB_HS_DIEPEACHMSK1_NAKM_Pos)

/* Device each OUT EP1 interrupt register */
# define USB_HS_DOEPEACHMSK1_XFRCM_Pos		0
# define USB_HS_DOEPEACHMSK1_XFRCM_Msk		((uint32_t)1 << USB_HS_DOEPEACHMSK1_XFRCM_Pos)
# define USB_HS_DOEPEACHMSK1_EPDM_Pos		1
# define USB_HS_DOEPEACHMSK1_EPDM_Msk		((uint32_t)1 << USB_HS_DOEPEACHMSK1_EPDM_Pos)
# define USB_HS_DOEPEACHMSK1_AHBERRM_Pos	2
# define USB_HS_DOEPEACHMSK1_AHBERRM_Msk	((uint32_t)1 << USB_HS_DOEPEACHMSK1_AHBERRM_Pos)
# define USB_HS_DOEPEACHMSK1_OPEM_Pos		8
# define USB_HS_DOEPEACHMSK1_OPEM_Msk		((uint32_t)1 << USB_HS_DOEPEACHMSK1_OPEM_Pos)
# define USB_HS_DOEPEACHMSK1_BIM_Pos		9
# define USB_HS_DOEPEACHMSK1_BIM_Msk		((uint32_t)1 << USB_HS_DOEPEACHMSK1_BIM_Pos)
# define USB_HS_DOEPEACHMSK1_BERRM_Pos		12
# define USB_HS_DOEPEACHMSK1_BERRM_Msk		((uint32_t)1 << USB_HS_DOEPEACHMSK1_BERRM_Pos)
# define USB_HS_DOEPEACHMSK1_NAKM_Pos		13
# define USB_HS_DOEPEACHMSK1_NAKM_Msk		((uint32_t)1 << USB_HS_DOEPEACHMSK1_NAKM_Pos)
# define USB_HS_DOEPEACHMSK1_NYETM_Pos		9
# define USB_HS_DOEPEACHMSK1_NYETM_Msk		((uint32_t)1 << USB_HS_DOEPEACHMSK1_NYETM_Pos)

/* Device control IN endpoint X control register */
#define USB_HS_DIEPCTL_MPSIZ_Pos(EP)    0
#define USB_HS_DIEPCTL_MPSIZ_Msk(EP)    ((EP) > 0 ? ((uint32_t)0x7ff << USB_HS_DIEPCTL_MPSIZ_Pos(EP)) \
                     : ((uint32_t)0x3 << USB_HS_DIEPCTL_MPSIZ_Pos(EP)))

# define USB_HS_DIEPCTL_USBAEP_Pos		15
# define USB_HS_DIEPCTL_USBAEP_Msk		((uint32_t)1 << USB_HS_DIEPCTL_USBAEP_Pos)
# define USB_HS_DIEPCTL_DPID_Pos		16 /* applies to isochronous IN EP */
# define USB_HS_DIEPCTL_DPID_Msk		((uint32_t)1 << USB_HS_DIEPCTL_DPID_Pos)
# define USB_HS_DIEPCTL_EONUM_Pos		16 /* applies to interrupt/bulk IN EP */
# define USB_HS_DIEPCTL_EONUM_Msk		((uint32_t)1 << USB_HS_DIEPCTL_DPID_Pos)
# define USB_HS_DIEPCTL_NAKSTS_Pos		17
# define USB_HS_DIEPCTL_NAKSTS_Msk		((uint32_t)1 << USB_HS_DIEPCTL_NAKSTS_Pos)
# define USB_HS_DIEPCTL_EPTYP_Pos		18
# define USB_HS_DIEPCTL_EPTYP_Msk		((uint32_t)0x3 << USB_HS_DIEPCTL_EPTYP_Pos)
#	define USB_HS_DIEPCTL_EPTYP_CONTROL	0
#	define USB_HS_DIEPCTL_EPTYP_ISOCHRO	1
#	define USB_HS_DIEPCTL_EPTYP_BULK	2
#	define USB_HS_DIEPCTL_EPTYP_INT		3
# define USB_HS_DIEPCTL_STALL_Pos		21
# define USB_HS_DIEPCTL_STALL_Msk		((uint32_t)1 << USB_HS_DIEPCTL_STALL_Pos)
# define USB_HS_DIEPCTL_TXFNUM_Pos		22
# define USB_HS_DIEPCTL_TXFNUM_Msk		((uint32_t)0xf << USB_HS_DIEPCTL_TXFNUM_Pos)
# define USB_HS_DIEPCTL_CNAK_Pos		26
# define USB_HS_DIEPCTL_CNAK_Msk		((uint32_t)1 << USB_HS_DIEPCTL_CNAK_Pos)
# define USB_HS_DIEPCTL_SNAK_Pos		27
# define USB_HS_DIEPCTL_SNAK_Msk		((uint32_t)1 << USB_HS_DIEPCTL_SNAK_Pos)
# define USB_HS_DIEPCTL_SD0PID_Pos		28
# define USB_HS_DIEPCTL_SD0PID_Msk		((uint32_t)1 << USB_HS_DIEPCTL_SD0PID_Pos)
# define USB_HS_DIEPCTL_SD1PID_Pos   		29
# define USB_HS_DIEPCTL_SD1PID_Msk   		((uint32_t)1 << USB_HS_DIEPCTL_SD1PID_Pos)
# define USB_HS_DIEPCTL_EPDIS_Pos		30
# define USB_HS_DIEPCTL_EPDIS_Msk		((uint32_t)1 << USB_HS_DIEPCTL_EPDIS_Pos)
# define USB_HS_DIEPCTL_EPENA_Pos		31
# define USB_HS_DIEPCTL_EPENA_Msk		((uint32_t)1 << USB_HS_DIEPCTL_EPENA_Pos)

/* Device endpoint interrupt register */
# define USB_HS_DIEPINT_XFRC_Pos		0
# define USB_HS_DIEPINT_XFRC_Msk		((uint32_t)1 << USB_HS_DIEPINT_XFRC_Pos)
# define USB_HS_DIEPINT_EPDISD_Pos		1
# define USB_HS_DIEPINT_EPDISD_Msk		((uint32_t)1 << USB_HS_DIEPINT_TOC_Pos)
# define USB_HS_DIEPINT_TOC_Pos			3
# define USB_HS_DIEPINT_TOC_Msk			((uint32_t)1 << USB_HS_DIEPINT_TOC_Pos)
# define USB_HS_DIEPINT_ITTXFE_Pos		4
# define USB_HS_DIEPINT_ITTXFE_Msk		((uint32_t)1 << USB_HS_DIEPINT_ITTXFE_Pos)
# define USB_HS_DIEPINT_INEPNE_Pos		6
# define USB_HS_DIEPINT_INEPNE_Msk		((uint32_t)1 << USB_HS_DIEPINT_INEPNE_Pos)
# define USB_HS_DIEPINT_TXFE_Pos		7
# define USB_HS_DIEPINT_TXFE_Msk		((uint32_t)1 << USB_HS_DIEPINT_TXFE_Pos)
# define USB_HS_DIEPINT_TXFIFOUDRN_Pos		8
# define USB_HS_DIEPINT_TXFIFOUDRN_Msk		((uint32_t)1 << USB_HS_DIEPINT_TXFIFOUDRN_Pos)
# define USB_HS_DIEPINT_BNA_Pos			9
# define USB_HS_DIEPINT_BNA_Msk			((uint32_t)1 << USB_HS_DIEPINT_BNA_Pos)
# define USB_HS_DIEPINT_PKTDRPSTS_Pos		11
# define USB_HS_DIEPINT_PKTDRPSTS_Msk		((uint32_t)1 << USB_HS_DIEPINT_PKTDRPSTS_Pos)
# define USB_HS_DIEPINT_BERR_Pos		12
# define USB_HS_DIEPINT_BERR_Msk		((uint32_t)1 << USB_HS_DIEPINT_BERR_Pos)
# define USB_HS_DIEPINT_NAK_Pos			13
# define USB_HS_DIEPINT_NAK_Msk			((uint32_t)1 << USB_HS_DIEPINT_NAK_Pos)

/* Device IN endpoint X transfert size register */
# define USB_HS_DIEPTSIZ_XFRSIZ_Pos(EP)		0
# define USB_HS_DIEPTSIZ_XFRSIZ_Msk(EP)		((EP) > 0 ? ((uint32_t)0x7ffff << USB_HS_DIEPTSIZ_XFRSIZ_Pos(EP)) \
						: ((uint32_t)0x7f << USB_HS_DIEPTSIZ_XFRSIZ_Pos(EP)))
# define USB_HS_DIEPTSIZ_PKTCNT_Pos(EP)		19
# define USB_HS_DIEPTSIZ_PKTCNT_Msk(EP)		((EP) > 0 ? ((uint32_t)0x3ff << USB_HS_DIEPTSIZ_PKTCNT_Pos(EP)) \
						: ((uint32_t)0x3 << USB_HS_DIEPTSIZ_PKTCNT_Pos(EP)))
# define USB_HS_DIEPTSIZ_MCNT_Pos(EP)		29
# define USB_HS_DIEPTSIZ_MCNT_Msk(EP)		((EP) > 0 ? ((uint32_t)0x3 << USB_HS_DIEPTSIZ_MCNT_Pos(EP)) : 0)

/* Device EPx DMA address register */
# define USB_HS_DIEPDMA_DMAADDR_Pos		0
# define USB_HS_DIEPDMA_DMAADDR_Msk		((uint32_t)0xffffffff << USB_HS_DIEPDMA_DMAADDR_Pos)

/* Device IN endpoint transmit FIFO status register */
# define USB_HS_DTXFSTS_INEPTFSAV_Pos		0
# define USB_HS_DTXFSTS_INEPTFSAV_Msk		((uint32_t)0xffff << USB_HS_DTXFSTS_INEPTFSAV_Pos)

/* Device control OUT endpoint X control register */
# define USB_HS_DOEPCTL_MPSIZ_Pos(EP)		0
# define USB_HS_DOEPCTL_MPSIZ_Msk(EP)		((EP) > 0 ? ((uint32_t)0x7ff << USB_HS_DOEPCTL_MPSIZ_Pos(EP)) \
						: ((uint32_t)0x3 << USB_HS_DOEPCTL_MPSIZ_Pos(EP)))
# define USB_HS_DOEPCTL_USBAEP_Pos		15
# define USB_HS_DOEPCTL_USBAEP_Msk		((uint32_t)1 << USB_HS_DOEPCTL_USBAEP_Pos)
# define USB_HS_DOEPCTL_EONUM_Pos(EP)		16
# define USB_HS_DOEPCTL_EONUM_Msk(EP)		((EP) > 0 ? ((uint32_t)1 << USB_HS_DOEPCTL_USBAEP_Pos(EP)) : 0)
# define USB_HS_DOEPCTL_NAKSTS_Pos		17
# define USB_HS_DOEPCTL_NAKSTS_Msk		((uint32_t)1 << USB_HS_DOEPCTL_NAKSTS_Pos)
# define USB_HS_DOEPCTL_EPTYP_Pos		18
# define USB_HS_DOEPCTL_EPTYP_Msk		((uint32_t)0x3 << USB_HS_DOEPCTL_EPTYP_Pos)
#	define USB_HS_DOEPCTL_EPTYP_CONTROL	0
#	define USB_HS_DOEPCTL_EPTYP_ISOCHRO	1
#	define USB_HS_DOEPCTL_EPTYP_BULK	2
#	define USB_HS_DOEPCTL_EPTYP_INT		3
# define USB_HS_DOEPCTL_SNPM_Pos		20
# define USB_HS_DOEPCTL_SNPM_Msk		((uint32_t)1 << USB_HS_DOEPCTL_SNPM_Pos)
# define USB_HS_DOEPCTL_STALL_Pos		21
# define USB_HS_DOEPCTL_STALL_Msk		((uint32_t)1 << USB_HS_DOEPCTL_STALL_Pos)
# define USB_HS_DOEPCTL_CNAK_Pos		26
# define USB_HS_DOEPCTL_CNAK_Msk		((uint32_t)1 << USB_HS_DOEPCTL_CNAK_Pos)
# define USB_HS_DOEPCTL_SNAK_Pos		27
# define USB_HS_DOEPCTL_SNAK_Msk		((uint32_t)1 << USB_HS_DOEPCTL_SNAK_Pos)
# define USB_HS_DOEPCTL_SD0PID_Pos   		28
# define USB_HS_DOEPCTL_SD0PID_Msk   		((uint32_t)1 << USB_HS_DOEPCTL_SD0PID_Pos)
# define USB_HS_DOEPCTL_SD1PID_Pos   		29
# define USB_HS_DOEPCTL_SD1PID_Msk   		((uint32_t)1 << USB_HS_DOEPCTL_SD1PID_Pos)
#if 0
# define USB_HS_DOEPCTL_SD0PID_Pos(EP)		28 /* Applies to interrupt/bulk OUT EP */
# define USB_HS_DOEPCTL_SD0PID_Msk(EP)		((EP) > 0 ? ((uint32_t)1 << USB_HS_DOEPCTL_SD0PID_Pos(EP)) : 0)
# define USB_HS_DOEPCTL_SEVNFRM_Pos(EP)		28 /* Applies to isochronous OUT EP */
# define USB_HS_DOEPCTL_SEVNFRM_Msk(EP)		((EP) > 0 ? ((uint32_t)1 << USB_HS_DOEPCTL_SEVNFRM_Pos(EP)) : 0)
# define USB_HS_DOEPCTL_SD1PID_Pos(EP)		29 /* Applies to interrupt/bulk OUT EP */
# define USB_HS_DOEPCTL_SD1PID_Msk(EP)		((EP) > 0 ? ((uint32_t)1 << USB_HS_DOEPCTL_SD1PID_Pos(EP)) : 0)
# define USB_HS_DOEPCTL_SODDFRM_Pos(EP)		29
# define USB_HS_DOEPCTL_SODDFRM_Msk(EP)		((EP) > 0 ? ((uint32_t)1 << USB_HS_DOEPCTL_SODDFRM_Pos(EP)) : 0)
#endif
# define USB_HS_DOEPCTL_EPDIS_Pos		30
# define USB_HS_DOEPCTL_EPDIS_Msk		((uint32_t)1 << USB_HS_DOEPCTL_EPDIS_Pos)
# define USB_HS_DOEPCTL_EPENA_Pos		31
# define USB_HS_DOEPCTL_EPENA_Msk		((uint32_t)1 << USB_HS_DOEPCTL_EPENA_Pos)

/* Device endpoint interrupt register */
# define USB_HS_DOEPINT_XFRC_Pos		0
# define USB_HS_DOEPINT_XFRC_Msk		((uint32_t)1 << USB_HS_DOEPINT_XFRC_Pos)
# define USB_HS_DOEPINT_EPDISD_Pos		1
# define USB_HS_DOEPINT_EPDISD_Msk		((uint32_t)1 << USB_HS_DOEPINT_EPDISD_Pos)
# define USB_HS_DOEPINT_STUP_Pos		3
# define USB_HS_DOEPINT_STUP_Msk		((uint32_t)1 << USB_HS_DOEPINT_STUP_Pos)
# define USB_HS_DOEPINT_OTEPDIS_Pos		4
# define USB_HS_DOEPINT_OTEPDIS_Msk		((uint32_t)1 << USB_HS_DOEPINT_OTEPDIS_Pos)
# define USB_HS_DOEPINT_B2BSTUP_Pos		6
# define USB_HS_DOEPINT_B2BSTUP_Msk		((uint32_t)1 << USB_HS_DOEPINT_B2BSTUP_Pos)
# define USB_HS_DOEPINT_NYET_Pos		14
# define USB_HS_DOEPINT_NYET_Msk		((uint32_t)1 << USB_HS_DOEPINT_NYET_Pos)

/* Device OUT enpoint 0 transfer size register */
# define USB_HS_DOEPTSIZ_XFRSIZ_Pos(EP)		0
# define USB_HS_DOEPTSIZ_XFRSIZ_Msk(EP)		((EP) > 0 ? ((uint32_t)0x7ffff << USB_HS_DOEPTSIZ_XFRSIZ_Pos(EP)) \
						: ((uint32_t)0x7f << USB_HS_DOEPTSIZ_XFRSIZ_Pos(EP)))
# define USB_HS_DOEPTSIZ_PKTCNT_Pos(EP)		19
# define USB_HS_DOEPTSIZ_PKTCNT_Msk(EP)		((EP) > 0 ? ((uint32_t)0x3ff << USB_HS_DOEPTSIZ_PKTCNT_Pos(EP)) \
						: ((uint32_t)1 << USB_HS_DOEPTSIZ_PKTCNT_Pos(EP)))
# define USB_HS_DOEPTSIZ_STUPCNT_Pos		29 /* Applies to control OUT EP */
# define USB_HS_DOEPTSIZ_STUPCNT_Msk		((uint32_t)3 << USB_HS_DOEPTSIZ_STUPCNT_Pos)
# define USB_HS_DOEPTSIZ_RXDPID_Pos		29 /* Applies to isochronous OUT EP */
# define USB_HS_DOEPTSIZ_RXDPID_Msk		((uint32_t)3 << USB_HS_DOEPTSIZ_RXDPID_Pos)

/* Device EPx DMA address register */
# define USB_HS_DOEPDMA_DMAADDR_Pos		0
# define USB_HS_DOEPDMA_DMAADDR_Msk		((uint32_t)0xffffffff << USB_HS_DOEPDMA_DMAADDR_Pos)

/* Power and clock gating control register */
# define USB_HS_PCGCCTL_STPPCLK_Pos		0
# define USB_HS_PCGCCTL_STPPCLK_Msk		((uint32_t)1 << USB_HS_PCGCCTL_STPPCLK_Pos)
# define USB_HS_PCGCCTL_GATEHCLK_Pos		1
# define USB_HS_PCGCCTL_GATEHCLK_Msk		((uint32_t)1 << USB_HS_PCGCCTL_GATEHCLK_Pos)
# define USB_HS_PCGCCTL_PHYSUSP_Pos		4
# define USB_HS_PCGCCTL_PHYSUSP_Msk		((uint32_t)1 << USB_HS_PCGCCTL_PHYSUSP_Pos)

/* GPIO definitions for ULPI Mode */
# define GPIO_AF10_OTG_HS      10
/* GPIO A */
# define ULPI_D0_PIN           3
# define ULPI_CLK_PIN          5
/* GPIO B */
# define ULPI_D1_PIN           0
# define ULPI_D2_PIN           1
# define ULPI_D7_PIN           5
# define ULPI_D3_PIN           10
# define ULPI_D4_PIN           11
# define ULPI_D5_PIN           12
# define ULPI_D6_PIN           13
/* GPIO C */
# define ULPI_STP_PIN          0
# define ULPI_DIR_PIN          2
# define ULPI_NXT_PIN          3

#endif /* STM32F4XX_USB_HS_REGS_H */
