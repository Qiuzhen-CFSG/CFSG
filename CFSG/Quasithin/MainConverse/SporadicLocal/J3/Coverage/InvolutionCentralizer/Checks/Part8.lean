module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Data

/-!
# Kernel checks for orbit rows 8192 through 8721

Each check certifies the point images of actual ATLAS model words, together
with sorted adjacent inequalities. Source and generation: `../source/generate.py`.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
set_option maxRecDepth 40000
set_option Elab.async false

set_option maxHeartbeats 4000000 in
public theorem checked_block_64 : checkBlock 64 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_65 : checkBlock 65 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_66 : checkBlock 66 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_67 : checkBlock 67 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
public theorem checked_block_68 : checkBlock 68 = true := by decide +kernel

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
