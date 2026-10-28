module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.OrbitArithmetic
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary160Basis
/-!
# Kernel-checked degree-160 numerical certificates

Each product has a separate proof budget. The representative dense computation
used 2.56 GiB RSS, so these arithmetic declarations are elaborated sequentially.
This bounds simultaneous temporary reductions without increasing any resource
limit. The scalar and symbolic proofs import these checked results.
Attribution and benchmark: `source/README.md` and `../source/README.md`.
-/
set_option Elab.async false
public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Checks
open Data
theorem a2_check : checkProduct 160 a a a2 = true := by decide +kernel

theorem b2_check : checkProduct 160 b b b2 = true := by decide +kernel

theorem b3_check : checkProduct 160 b b2 b3 = true := by decide +kernel

theorem ab_check : checkProduct 160 a b ab = true := by decide +kernel

theorem ab2_check : checkProduct 160 ab ab ab2 = true := by decide +kernel

theorem ab3_check : checkProduct 160 ab2 ab ab3 = true := by decide +kernel

theorem ab4_check : checkProduct 160 ab2 ab2 ab4 = true := by decide +kernel

theorem ab7_check : checkProduct 160 ab3 ab4 ab7 = true := by decide +kernel

theorem u_check : checkProduct 160 a b2 u = true := by decide +kernel

theorem comm_check : checkProduct 160 u ab comm = true := by decide +kernel

theorem comm2_check : checkProduct 160 comm comm comm2 = true := by decide +kernel

theorem comm4_check : checkProduct 160 comm2 comm2 comm4 = true := by decide +kernel

theorem comm6_check : checkProduct 160 comm4 comm2 comm6 = true := by decide +kernel

theorem comm12_check : checkProduct 160 comm6 comm6 comm12 = true := by decide +kernel

theorem long1_check : checkProduct 160 ab2 u long1 = true := by decide +kernel

theorem long2_check : checkProduct 160 long1 ab long2 = true := by decide +kernel

theorem long_check : checkProduct 160 long2 u long = true := by decide +kernel

theorem longSq_check : checkProduct 160 long long longSq = true := by decide +kernel

theorem longCube_check : checkProduct 160 longSq long longCube = true := by decide +kernel

theorem long6_check : checkProduct 160 longCube longCube long6 = true := by decide +kernel

theorem ba_check : checkProduct 160 b a ba = true := by decide +kernel

theorem t_check : checkSum 160 [u, a, b, ba] t = true := by decide +kernel

theorem tPower2_check : checkProduct 160 t t tPower2 = true := by decide +kernel

theorem tPower3_check : checkProduct 160 tPower2 t tPower3 = true := by decide +kernel

theorem tPower4_check : checkProduct 160 tPower3 t tPower4 = true := by decide +kernel

theorem tPower5_check : checkProduct 160 tPower4 t tPower5 = true := by decide +kernel

theorem tPower6_check : checkProduct 160 tPower5 t tPower6 = true := by decide +kernel

theorem tPower7_check : checkProduct 160 tPower6 t tPower7 = true := by decide +kernel

theorem tPower8_check : checkProduct 160 tPower7 t tPower8 = true := by decide +kernel

theorem tPower9_check : checkProduct 160 tPower8 t tPower9 = true := by decide +kernel

theorem tPower10_check : checkProduct 160 tPower9 t tPower10 = true := by decide +kernel

theorem tPower11_check : checkProduct 160 tPower10 t tPower11 = true := by decide +kernel

theorem tPower12_check : checkProduct 160 tPower11 t tPower12 = true := by decide +kernel

theorem block2_check : checkSum 160 [identity, tPower3, tPower4, tPower5, tPower6, tPower9, tPower10] block2 = true := by decide +kernel

theorem block3_check : checkSum 160 [t, tPower3, tPower4, tPower6, tPower7, tPower8, tPower9, tPower11] block3 = true := by decide +kernel

theorem block4_check : checkSum 160 [identity, tPower2, tPower6, tPower8, tPower10] block4 = true := by decide +kernel

theorem block5_check : checkSum 160 [t, tPower3, tPower5, tPower6, tPower7, tPower8, tPower10, tPower11] block5 = true := by decide +kernel

theorem block6_check : checkSum 160 [identity, t, tPower2, tPower5, tPower6, tPower7, tPower8, tPower9, tPower11] block6 = true := by decide +kernel

theorem block7_check : checkSum 160 [identity, tPower5, tPower7, tPower8, tPower9] block7 = true := by decide +kernel

theorem block8_check : checkSum 160 [identity, t, tPower2, tPower3, tPower4, tPower5, tPower6, tPower7, tPower8, tPower9, tPower10, tPower11] block8 = true := by decide +kernel

theorem block9_check : checkSum 160 [identity, tPower2, tPower4, tPower5, tPower8, tPower10] block9 = true := by decide +kernel

theorem block10_check : checkSum 160 [t, tPower2, tPower3, tPower4, tPower6, tPower7, tPower8, tPower11] block10 = true := by decide +kernel

theorem block11_check : checkSum 160 [tPower4, tPower5, tPower6, tPower7, tPower8, tPower10, tPower11] block11 = true := by decide +kernel

theorem block12_check : checkSum 160 [tPower2, tPower4, tPower5, tPower8, tPower9, tPower10, tPower11] block12 = true := by decide +kernel

theorem block13_check : checkSum 160 [identity, t, tPower3] block13 = true := by decide +kernel

theorem horner12Product_check : checkProduct 160 block13 tPower12 horner12Product = true := by decide +kernel

theorem horner12_check : checkSum 160 [horner12Product, block12] horner12 = true := by decide +kernel

theorem horner11Product_check : checkProduct 160 horner12 tPower12 horner11Product = true := by decide +kernel

theorem horner11_check : checkSum 160 [horner11Product, block11] horner11 = true := by decide +kernel

theorem horner10Product_check : checkProduct 160 horner11 tPower12 horner10Product = true := by decide +kernel

theorem horner10_check : checkSum 160 [horner10Product, block10] horner10 = true := by decide +kernel

theorem horner9Product_check : checkProduct 160 horner10 tPower12 horner9Product = true := by decide +kernel

theorem horner9_check : checkSum 160 [horner9Product, block9] horner9 = true := by decide +kernel

theorem horner8Product_check : checkProduct 160 horner9 tPower12 horner8Product = true := by decide +kernel

theorem horner8_check : checkSum 160 [horner8Product, block8] horner8 = true := by decide +kernel

theorem horner7Product_check : checkProduct 160 horner8 tPower12 horner7Product = true := by decide +kernel

theorem horner7_check : checkSum 160 [horner7Product, block7] horner7 = true := by decide +kernel

theorem horner6Product_check : checkProduct 160 horner7 tPower12 horner6Product = true := by decide +kernel

theorem horner6_check : checkSum 160 [horner6Product, block6] horner6 = true := by decide +kernel

theorem horner5Product_check : checkProduct 160 horner6 tPower12 horner5Product = true := by decide +kernel

theorem horner5_check : checkSum 160 [horner5Product, block5] horner5 = true := by decide +kernel

theorem horner4Product_check : checkProduct 160 horner5 tPower12 horner4Product = true := by decide +kernel

theorem horner4_check : checkSum 160 [horner4Product, block4] horner4 = true := by decide +kernel

theorem horner3Product_check : checkProduct 160 horner4 tPower12 horner3Product = true := by decide +kernel

theorem horner3_check : checkSum 160 [horner3Product, block3] horner3 = true := by decide +kernel

theorem horner2Product_check : checkProduct 160 horner3 tPower12 horner2Product = true := by decide +kernel

theorem horner2_check : checkSum 160 [horner2Product, block2] horner2 = true := by decide +kernel

theorem shift12_check : checkProduct 160 horner2 tPower12 shift12 = true := by decide +kernel

theorem rankOne_check : checkProduct 160 shift12 tPower12 rankOne = true := by decide +kernel

theorem transpose_a_check : checkTranspose 160 a aTranspose = true := by decide +kernel
theorem transpose_b_check : checkTranspose 160 b bTranspose = true := by decide +kernel
theorem transpose_basis_check : checkTranspose 160 Binary160Basis.leftBasis leftColumns = true := by decide +kernel

theorem left_orbit_check :
    checkOrbit 160 aTranspose bTranspose column leftColumns leftParents leftLetters leftWords = true := by
  decide +kernel

theorem right_orbit_check :
    checkOrbit 160 a b covector rightBasis rightParents rightLetters rightWords = true := by
  decide +kernel

theorem right_inverse_check : checkInverse 160 rightInverse rightBasis = true := by decide +kernel

theorem identity_check : checkOne 160 identity = true := by decide +kernel

theorem outer_check : checkOuter 160 column covector rankOne = true := by decide +kernel
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Checks
