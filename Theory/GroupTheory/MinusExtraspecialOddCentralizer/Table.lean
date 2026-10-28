module
public import Theory.GroupTheory.MinusExtraspecialOddInvolutions.Calculation
set_option Elab.async false
/-!
# Involution squares in transposition centralizers of the minus extraspecial model

We enumerate the automorphisms of Q₈ * D₈ by their four generator images.
The compact strings store five-bit coordinates; `generatedRow_eq` checks the
entire table against the defining relations in Lean's kernel. The second
certificate checks commuting automorphisms: an involutory transposition has
a fixed square root of the central involution, and a commuting automorphism
cannot square to conjugation by a fixed noncentral involution.

The model and extension modules transport these identities to actual local
centralizers. Source application: Aschbacher–Smith 14.2.17(1), printed p.987.
-/

@[expose] public section
namespace MinusExtraspecial.FixedFourCalculation.OddCentralizer
open Outside OddInvolution
abbrev Triple := B × B × B

def decodeTriples : List Char → List Triple
  | a :: b :: c :: xs => (BitVec.ofNat 5 (a.toNat-65),
      BitVec.ofNat 5 (b.toNat-65),BitVec.ofNat 5 (c.toNat-65)) :: decodeTriples xs
  | _ => []
def row (u : B) : List Triple := decodeTriples (data u.toNat).toList
where data : Nat → String
  | 1 => "EIQEISEKQEKSEQIEQKESIESKFIQFISFKQFKSFQIFQKFSIFSKGIQGISGKQGKSGQIGQKGSIGSKHIQHISHKQHKSHQIHQKHSIHSKMIZMI\\MKZMK\\MZIMZKM\\IM\\KNIZNI\\NKZNK\\NZINZKN\\IN\\KOIZOI\\OKZOK\\OZIOZKO\\IO\\KPIZPI\\PKZPK\\PZIPZKP\\IP\\KUQZUQ\\USZUS\\UZQUZSU\\QU\\SVQZVQ\\VSZVS\\VZQVZSV\\QV\\SWQZWQ\\WSZWS\\WZQWZSW\\QW\\SXQZXQ\\XSZXS\\XZQXZSX\\QX\\S"
  | 3 => "EIQEISEKQEKSEQIEQKESIESKFIQFISFKQFKSFQIFQKFSIFSKGIQGISGKQGKSGQIGQKGSIGSKHIQHISHKQHKSHQIHQKHSIHSKMIZMI\\MKZMK\\MZIMZKM\\IM\\KNIZNI\\NKZNK\\NZINZKN\\IN\\KOIZOI\\OKZOK\\OZIOZKO\\IO\\KPIZPI\\PKZPK\\PZIPZKP\\IP\\KUQZUQ\\USZUS\\UZQUZSU\\QU\\SVQZVQ\\VSZVS\\VZQVZSV\\QV\\SWQZWQ\\WSZWS\\WZQWZSW\\QW\\SXQZXQ\\XSZXS\\XZQXZSX\\QX\\S"
  | 4 => "BIQBISBKQBKSBQIBQKBSIBSKDIQDISDKQDKSDQIDQKDSIDSKFIQFISFKQFKSFQIFQKFSIFSKHIQHISHKQHKSHQIHQKHSIHSKJI]JI_JK]JK_J]IJ]KJ_IJ_KLI]LI_LK]LK_L]IL]KL_IL_KNI]NI_NK]NK_N]IN]KN_IN_KPI]PI_PK]PK_P]IP]KP_IP_KRQ]RQ_RS]RS_R]QR]SR_QR_STQ]TQ_TS]TS_T]QT]ST_QT_SVQ]VQ_VS]VS_V]QV]SV_QV_SXQ]XQ_XS]XS_X]QX]SX_QX_S"
  | 5 => "BIQBISBKQBKSBQIBQKBSIBSKDIQDISDKQDKSDQIDQKDSIDSKEIQEISEKQEKSEQIEQKESIESKGIQGISGKQGKSGQIGQKGSIGSKJI^JI`JK^JK`J^IJ^KJ`IJ`KLI^LI`LK^LK`L^IL^KL`IL`KMI^MI`MK^MK`M^IM^KM`IM`KOI^OI`OK^OK`O^IO^KO`IO`KRQ^RQ`RS^RS`R^QR^SR`QR`STQ^TQ`TS^TS`T^QT^ST`QT`SUQ^UQ`US^US`U^QU^SU`QU`SWQ^WQ`WS^WS`W^QW^SW`QW`S"
  | 6 => "BIQBISBKQBKSBQIBQKBSIBSKDIQDISDKQDKSDQIDQKDSIDSKFIQFISFKQFKSFQIFQKFSIFSKHIQHISHKQHKSHQIHQKHSIHSKJI]JI_JK]JK_J]IJ]KJ_IJ_KLI]LI_LK]LK_L]IL]KL_IL_KNI]NI_NK]NK_N]IN]KN_IN_KPI]PI_PK]PK_P]IP]KP_IP_KRQ]RQ_RS]RS_R]QR]SR_QR_STQ]TQ_TS]TS_T]QT]ST_QT_SVQ]VQ_VS]VS_V]QV]SV_QV_SXQ]XQ_XS]XS_X]QX]SX_QX_S"
  | 7 => "BIQBISBKQBKSBQIBQKBSIBSKDIQDISDKQDKSDQIDQKDSIDSKEIQEISEKQEKSEQIEQKESIESKGIQGISGKQGKSGQIGQKGSIGSKJI^JI`JK^JK`J^IJ^KJ`IJ`KLI^LI`LK^LK`L^IL^KL`IL`KMI^MI`MK^MK`M^IM^KM`IM`KOI^OI`OK^OK`O^IO^KO`IO`KRQ^RQ`RS^RS`R^QR^SR`QR`STQ^TQ`TS^TS`T^QT^ST`QT`SUQ^UQ`US^US`U^QU^SU`QU`SWQ^WQ`WS^WS`W^QW^SW`QW`S"
  | 9 => "EI]EI_EK]EK_E]IE]KE_IE_KFI^FI`FK^FK`F^IF^KF`IF`KGI]GI_GK]GK_G]IG]KG_IG_KHI^HI`HK^HK`H^IH^KH`IH`KMI^MI`MK^MK`M^IM^KM`IM`KNI]NI_NK]NK_N]IN]KN_IN_KOI^OI`OK^OK`O^IO^KO`IO`KPI]PI_PK]PK_P]IP]KP_IP_KR]^R]`R^]R^_R_^R_`R`]R`_T]^T]`T^]T^_T_^T_`T`]T`_Y]^Y]`Y^]Y^_Y_^Y_`Y`]Y`_[]^[]`[^][^_[_^[_`[`][`_"
  | 11 => "EI]EI_EK]EK_E]IE]KE_IE_KFI^FI`FK^FK`F^IF^KF`IF`KGI]GI_GK]GK_G]IG]KG_IG_KHI^HI`HK^HK`H^IH^KH`IH`KMI^MI`MK^MK`M^IM^KM`IM`KNI]NI_NK]NK_N]IN]KN_IN_KOI^OI`OK^OK`O^IO^KO`IO`KPI]PI_PK]PK_P]IP]KP_IP_KR]^R]`R^]R^_R_^R_`R`]R`_T]^T]`T^]T^_T_^T_`T`]T`_Y]^Y]`Y^]Y^_Y_^Y_`Y`]Y`_[]^[]`[^][^_[_^[_`[`][`_"
  | 12 => "BIZBI\\BKZBK\\BZIBZKB\\IB\\KDIZDI\\DKZDK\\DZIDZKD\\ID\\KFI^FI`FK^FK`F^IF^KF`IF`KHI^HI`HK^HK`H^IH^KH`IH`KJI^JI`JK^JK`J^IJ^KJ`IJ`KLI^LI`LK^LK`L^IL^KL`IL`KNIZNI\\NKZNK\\NZINZKN\\IN\\KPIZPI\\PKZPK\\PZIPZKP\\IP\\KUZ^UZ`U\\^U\\`U^ZU^\\U`ZU`\\WZ^WZ`W\\^W\\`W^ZW^\\W`ZW`\\YZ^YZ`Y\\^Y\\`Y^ZY^\\Y`ZY`\\[Z^[Z`[\\^[\\`[^Z[^\\[`Z[`\\"
  | 13 => "BIZBI\\BKZBK\\BZIBZKB\\IB\\KDIZDI\\DKZDK\\DZIDZKD\\ID\\KEI]EI_EK]EK_E]IE]KE_IE_KGI]GI_GK]GK_G]IG]KG_IG_KJI]JI_JK]JK_J]IJ]KJ_IJ_KLI]LI_LK]LK_L]IL]KL_IL_KMIZMI\\MKZMK\\MZIMZKM\\IM\\KOIZOI\\OKZOK\\OZIOZKO\\IO\\KVZ]VZ_V\\]V\\_V]ZV]\\V_ZV_\\XZ]XZ_X\\]X\\_X]ZX]\\X_ZX_\\YZ]YZ_Y\\]Y\\_Y]ZY]\\Y_ZY_\\[Z][Z_[\\][\\_[]Z[]\\[_Z[_\\"
  | 14 => "BIZBI\\BKZBK\\BZIBZKB\\IB\\KDIZDI\\DKZDK\\DZIDZKD\\ID\\KFI^FI`FK^FK`F^IF^KF`IF`KHI^HI`HK^HK`H^IH^KH`IH`KJI^JI`JK^JK`J^IJ^KJ`IJ`KLI^LI`LK^LK`L^IL^KL`IL`KNIZNI\\NKZNK\\NZINZKN\\IN\\KPIZPI\\PKZPK\\PZIPZKP\\IP\\KUZ^UZ`U\\^U\\`U^ZU^\\U`ZU`\\WZ^WZ`W\\^W\\`W^ZW^\\W`ZW`\\YZ^YZ`Y\\^Y\\`Y^ZY^\\Y`ZY`\\[Z^[Z`[\\^[\\`[^Z[^\\[`Z[`\\"
  | 15 => "BIZBI\\BKZBK\\BZIBZKB\\IB\\KDIZDI\\DKZDK\\DZIDZKD\\ID\\KEI]EI_EK]EK_E]IE]KE_IE_KGI]GI_GK]GK_G]IG]KG_IG_KJI]JI_JK]JK_J]IJ]KJ_IJ_KLI]LI_LK]LK_L]IL]KL_IL_KMIZMI\\MKZMK\\MZIMZKM\\IM\\KOIZOI\\OKZOK\\OZIOZKO\\IO\\KVZ]VZ_V\\]V\\_V]ZV]\\V_ZV_\\XZ]XZ_X\\]X\\_X]ZX]\\X_ZX_\\YZ]YZ_Y\\]Y\\_Y]ZY]\\Y_ZY_\\[Z][Z_[\\][\\_[]Z[]\\[_Z[_\\"
  | 17 => "EQ]EQ_ES]ES_E]QE]SE_QE_SFQ^FQ`FS^FS`F^QF^SF`QF`SGQ]GQ_GS]GS_G]QG]SG_QG_SHQ^HQ`HS^HS`H^QH^SH`QH`SJ]^J]`J^]J^_J_^J_`J`]J`_L]^L]`L^]L^_L_^L_`L`]L`_UQ^UQ`US^US`U^QU^SU`QU`SVQ]VQ_VS]VS_V]QV]SV_QV_SWQ^WQ`WS^WS`W^QW^SW`QW`SXQ]XQ_XS]XS_X]QX]SX_QX_SY]^Y]`Y^]Y^_Y_^Y_`Y`]Y`_[]^[]`[^][^_[_^[_`[`][`_"
  | 19 => "EQ]EQ_ES]ES_E]QE]SE_QE_SFQ^FQ`FS^FS`F^QF^SF`QF`SGQ]GQ_GS]GS_G]QG]SG_QG_SHQ^HQ`HS^HS`H^QH^SH`QH`SJ]^J]`J^]J^_J_^J_`J`]J`_L]^L]`L^]L^_L_^L_`L`]L`_UQ^UQ`US^US`U^QU^SU`QU`SVQ]VQ_VS]VS_V]QV]SV_QV_SWQ^WQ`WS^WS`W^QW^SW`QW`SXQ]XQ_XS]XS_X]QX]SX_QX_SY]^Y]`Y^]Y^_Y_^Y_`Y`]Y`_[]^[]`[^][^_[_^[_`[`][`_"
  | 20 => "BQZBQ\\BSZBS\\BZQBZSB\\QB\\SDQZDQ\\DSZDS\\DZQDZSD\\QD\\SFQ^FQ`FS^FS`F^QF^SF`QF`SHQ^HQ`HS^HS`H^QH^SH`QH`SMZ^MZ`M\\^M\\`M^ZM^\\M`ZM`\\OZ^OZ`O\\^O\\`O^ZO^\\O`ZO`\\RQ^RQ`RS^RS`R^QR^SR`QR`STQ^TQ`TS^TS`T^QT^ST`QT`SVQZVQ\\VSZVS\\VZQVZSV\\QV\\SXQZXQ\\XSZXS\\XZQXZSX\\QX\\SYZ^YZ`Y\\^Y\\`Y^ZY^\\Y`ZY`\\[Z^[Z`[\\^[\\`[^Z[^\\[`Z[`\\"
  | 21 => "BQZBQ\\BSZBS\\BZQBZSB\\QB\\SDQZDQ\\DSZDS\\DZQDZSD\\QD\\SEQ]EQ_ES]ES_E]QE]SE_QE_SGQ]GQ_GS]GS_G]QG]SG_QG_SNZ]NZ_N\\]N\\_N]ZN]\\N_ZN_\\PZ]PZ_P\\]P\\_P]ZP]\\P_ZP_\\RQ]RQ_RS]RS_R]QR]SR_QR_STQ]TQ_TS]TS_T]QT]ST_QT_SUQZUQ\\USZUS\\UZQUZSU\\QU\\SWQZWQ\\WSZWS\\WZQWZSW\\QW\\SYZ]YZ_Y\\]Y\\_Y]ZY]\\Y_ZY_\\[Z][Z_[\\][\\_[]Z[]\\[_Z[_\\"
  | 22 => "BQZBQ\\BSZBS\\BZQBZSB\\QB\\SDQZDQ\\DSZDS\\DZQDZSD\\QD\\SFQ^FQ`FS^FS`F^QF^SF`QF`SHQ^HQ`HS^HS`H^QH^SH`QH`SMZ^MZ`M\\^M\\`M^ZM^\\M`ZM`\\OZ^OZ`O\\^O\\`O^ZO^\\O`ZO`\\RQ^RQ`RS^RS`R^QR^SR`QR`STQ^TQ`TS^TS`T^QT^ST`QT`SVQZVQ\\VSZVS\\VZQVZSV\\QV\\SXQZXQ\\XSZXS\\XZQXZSX\\QX\\SYZ^YZ`Y\\^Y\\`Y^ZY^\\Y`ZY`\\[Z^[Z`[\\^[\\`[^Z[^\\[`Z[`\\"
  | 23 => "BQZBQ\\BSZBS\\BZQBZSB\\QB\\SDQZDQ\\DSZDS\\DZQDZSD\\QD\\SEQ]EQ_ES]ES_E]QE]SE_QE_SGQ]GQ_GS]GS_G]QG]SG_QG_SNZ]NZ_N\\]N\\_N]ZN]\\N_ZN_\\PZ]PZ_P\\]P\\_P]ZP]\\P_ZP_\\RQ]RQ_RS]RS_R]QR]SR_QR_STQ]TQ_TS]TS_T]QT]ST_QT_SUQZUQ\\USZUS\\UZQUZSU\\QU\\SWQZWQ\\WSZWS\\WZQWZSW\\QW\\SYZ]YZ_Y\\]Y\\_Y]ZY]\\Y_ZY_\\[Z][Z_[\\][\\_[]Z[]\\[_Z[_\\"
  | 24 => "J]^J]`J^]J^_J_^J_`J`]J`_L]^L]`L^]L^_L_^L_`L`]L`_MZ^MZ`M\\^M\\`M^ZM^\\M`ZM`\\NZ]NZ_N\\]N\\_N]ZN]\\N_ZN_\\OZ^OZ`O\\^O\\`O^ZO^\\O`ZO`\\PZ]PZ_P\\]P\\_P]ZP]\\P_ZP_\\R]^R]`R^]R^_R_^R_`R`]R`_T]^T]`T^]T^_T_^T_`T`]T`_UZ^UZ`U\\^U\\`U^ZU^\\U`ZU`\\VZ]VZ_V\\]V\\_V]ZV]\\V_ZV_\\WZ^WZ`W\\^W\\`W^ZW^\\W`ZW`\\XZ]XZ_X\\]X\\_X]ZX]\\X_ZX_\\"
  | 26 => "J]^J]`J^]J^_J_^J_`J`]J`_L]^L]`L^]L^_L_^L_`L`]L`_MZ^MZ`M\\^M\\`M^ZM^\\M`ZM`\\NZ]NZ_N\\]N\\_N]ZN]\\N_ZN_\\OZ^OZ`O\\^O\\`O^ZO^\\O`ZO`\\PZ]PZ_P\\]P\\_P]ZP]\\P_ZP_\\R]^R]`R^]R^_R_^R_`R`]R`_T]^T]`T^]T^_T_^T_`T`]T`_UZ^UZ`U\\^U\\`U^ZU^\\U`ZU`\\VZ]VZ_V\\]V\\_V]ZV]\\V_ZV_\\WZ^WZ`W\\^W\\`W^ZW^\\W`ZW`\\XZ]XZ_X\\]X\\_X]ZX]\\X_ZX_\\"
  | _ => ""

def generatedRow (u : B) : List Triple :=
  if mul u u != 0 then
    all.flatMap fun v => if mul v v == mul u u && mul v u == mul (inv u) v then
      all.flatMap fun r => if mul r r == 0 && mul r u == mul u r && mul r v == mul v r then
        all.filterMap fun s =>
          if mul s s == 0 && mul s u == mul u s && mul s v == mul v s &&
            mul s r == mul (mul (mul u u) r) s then some (v,r,s) else none
      else []
    else []
  else []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_0 : generatedRow 0 = row 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_1 : generatedRow 1 = row 1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_2 : generatedRow 2 = row 2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_3 : generatedRow 3 = row 3 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_4 : generatedRow 4 = row 4 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_5 : generatedRow 5 = row 5 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_6 : generatedRow 6 = row 6 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_7 : generatedRow 7 = row 7 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_8 : generatedRow 8 = row 8 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_9 : generatedRow 9 = row 9 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_10 : generatedRow 10 = row 10 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_11 : generatedRow 11 = row 11 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_12 : generatedRow 12 = row 12 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_13 : generatedRow 13 = row 13 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_14 : generatedRow 14 = row 14 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_15 : generatedRow 15 = row 15 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_16 : generatedRow 16 = row 16 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_17 : generatedRow 17 = row 17 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_18 : generatedRow 18 = row 18 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_19 : generatedRow 19 = row 19 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_20 : generatedRow 20 = row 20 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_21 : generatedRow 21 = row 21 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_22 : generatedRow 22 = row 22 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_23 : generatedRow 23 = row 23 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_24 : generatedRow 24 = row 24 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_25 : generatedRow 25 = row 25 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_26 : generatedRow 26 = row 26 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_27 : generatedRow 27 = row 27 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_28 : generatedRow 28 = row 28 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_29 : generatedRow 29 = row 29 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_30 : generatedRow 30 = row 30 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem generatedRow_eq_31 : generatedRow 31 = row 31 := by decide +kernel

theorem generatedRow_eq (u : B) : generatedRow u = row u := by
  have hu : u.toNat < 32 := u.isLt
  interval_cases h : u.toNat
  · have he : u = 0 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_0
  · have he : u = 1 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_1
  · have he : u = 2 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_2
  · have he : u = 3 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_3
  · have he : u = 4 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_4
  · have he : u = 5 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_5
  · have he : u = 6 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_6
  · have he : u = 7 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_7
  · have he : u = 8 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_8
  · have he : u = 9 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_9
  · have he : u = 10 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_10
  · have he : u = 11 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_11
  · have he : u = 12 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_12
  · have he : u = 13 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_13
  · have he : u = 14 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_14
  · have he : u = 15 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_15
  · have he : u = 16 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_16
  · have he : u = 17 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_17
  · have he : u = 18 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_18
  · have he : u = 19 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_19
  · have he : u = 20 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_20
  · have he : u = 21 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_21
  · have he : u = 22 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_22
  · have he : u = 23 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_23
  · have he : u = 24 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_24
  · have he : u = 25 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_25
  · have he : u = 26 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_26
  · have he : u = 27 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_27
  · have he : u = 28 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_28
  · have he : u = 29 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_29
  · have he : u = 30 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_30
  · have he : u = 31 := BitVec.eq_of_toNat_eq h
    exact he ▸ generatedRow_eq_31



end MinusExtraspecial.FixedFourCalculation.OddCentralizer
