module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Data

/-!
# Kernel checks for orbit rows 1024 through 2047

Each check certifies the point images of actual ATLAS model words, together
with sorted adjacent inequalities. Source and generation: `../source/generate.py`.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
set_option maxRecDepth 40000
set_option Elab.async false

set_option maxHeartbeats 4000000 in
public theorem checked_block_8 : checkBlock 8 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_9 : checkBlock 9 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_10 : checkBlock 10 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_11 : checkBlock 11 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_12 : checkBlock 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_13 : checkBlock 13 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_14 : checkBlock 14 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_15 : checkBlock 15 = true := by decide +kernel

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
