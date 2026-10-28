module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Checks.Part0
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Checks.Part1
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Checks.Part2
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Checks.Part3
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Checks.Part4
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Checks.Part5
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Checks.Part6
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Checks.Part7
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Checks.Part8
import Mathlib.Tactic.FinCases

/-!
# Collecting the 69 checked batches of short conjugates

Every row below is checked against the fixed ATLAS maps, and every adjacent
key inequality is checked. The batch split affects only kernel resource use.
Source: GLS3 Table 5.3h, p.269; see `source/README.md` for the certificate.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate

public theorem checked_blocks (b : Fin 69) : checkBlock b.val = true := by
  fin_cases b
  · exact checked_block_0
  · exact checked_block_1
  · exact checked_block_2
  · exact checked_block_3
  · exact checked_block_4
  · exact checked_block_5
  · exact checked_block_6
  · exact checked_block_7
  · exact checked_block_8
  · exact checked_block_9
  · exact checked_block_10
  · exact checked_block_11
  · exact checked_block_12
  · exact checked_block_13
  · exact checked_block_14
  · exact checked_block_15
  · exact checked_block_16
  · exact checked_block_17
  · exact checked_block_18
  · exact checked_block_19
  · exact checked_block_20
  · exact checked_block_21
  · exact checked_block_22
  · exact checked_block_23
  · exact checked_block_24
  · exact checked_block_25
  · exact checked_block_26
  · exact checked_block_27
  · exact checked_block_28
  · exact checked_block_29
  · exact checked_block_30
  · exact checked_block_31
  · exact checked_block_32
  · exact checked_block_33
  · exact checked_block_34
  · exact checked_block_35
  · exact checked_block_36
  · exact checked_block_37
  · exact checked_block_38
  · exact checked_block_39
  · exact checked_block_40
  · exact checked_block_41
  · exact checked_block_42
  · exact checked_block_43
  · exact checked_block_44
  · exact checked_block_45
  · exact checked_block_46
  · exact checked_block_47
  · exact checked_block_48
  · exact checked_block_49
  · exact checked_block_50
  · exact checked_block_51
  · exact checked_block_52
  · exact checked_block_53
  · exact checked_block_54
  · exact checked_block_55
  · exact checked_block_56
  · exact checked_block_57
  · exact checked_block_58
  · exact checked_block_59
  · exact checked_block_60
  · exact checked_block_61
  · exact checked_block_62
  · exact checked_block_63
  · exact checked_block_64
  · exact checked_block_65
  · exact checked_block_66
  · exact checked_block_67
  · exact checked_block_68

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
