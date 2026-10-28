module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Data

/-!
# Kernel checks for orbit rows 0 through 1023

Each check certifies the point images of actual ATLAS model words, together
with sorted adjacent inequalities. Source and generation: `../source/generate.py`.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
set_option maxRecDepth 40000
set_option Elab.async false

set_option maxHeartbeats 4000000 in
public theorem checked_block_0 : checkBlock 0 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_1 : checkBlock 1 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_2 : checkBlock 2 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_3 : checkBlock 3 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_4 : checkBlock 4 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_5 : checkBlock 5 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_6 : checkBlock 6 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_7 : checkBlock 7 = true := by decide +kernel

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
