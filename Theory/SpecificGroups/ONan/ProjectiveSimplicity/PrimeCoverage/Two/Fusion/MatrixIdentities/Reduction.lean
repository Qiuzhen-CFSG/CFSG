module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootWords
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootCertificate0
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootCertificate1
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootCertificate2
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootCertificate3
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootCertificate4
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootCertificate5
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootCertificate6

/-!
# Reducing the seven O'Nan fusion root powers to matrix products

Six shared products evaluate the four conjugates of A; seven short chains
of products establish the required odd powers by repeated squaring. This
module proves the reduction only: every field of the product certificates
must subsequently be established against the actual numerical matrices.

The witness data and original ATLAS attribution are documented in
`ConjugateData.lean`; the target is the literal GL-word statement in
`Fusion/Certificate.lean`.
-/

namespace ONan.Simplicity.TwoCertificate.Fusion

/-- Shared products evaluating the conjugating words. -/
public structure ConjugateProducts : Prop where
  ba : matrixB * matrixA = RootData.ba
  d : RootData.ba * matrixBInv = RootData.d
  ad : matrixA * RootData.d = RootData.ad
  c : RootData.ad * matrixA = RootData.c
  bc : matrixB * RootData.c = RootData.bc
  f : RootData.bc * matrixBInv = RootData.f

set_option maxRecDepth 4096 in
/-- The numerical conjugates agree with the actual ambient GL words. -/
public theorem root_conjugate_of_products (h : ConjugateProducts) (r : Fin 7) :
    (linearRootWord r : Matrix (Fin 45) (Fin 45) (ZMod 7)) * matrixA *
      ((linearRootWord r)⁻¹ : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)) =
        ![RootData.d, matrixA, RootData.d, RootData.f, RootData.c, matrixA, RootData.d] r := by
  rw [root_conjugate]
  fin_cases r <;>
    simp only [inverseFreeConjugate, h.ba, h.d, h.ad, h.c, h.bc, h.f]

set_option maxRecDepth 4096 in
/-- Product certificates suffice for all seven full linear root powers. -/
public theorem matrix_root_powers_of_products (hc : ConjugateProducts)
    (h0 : RootData.RootProducts0) (h1 : RootData.RootProducts1)
    (h2 : RootData.RootProducts2) (h3 : RootData.RootProducts3)
    (h4 : RootData.RootProducts4) (h5 : RootData.RootProducts5)
    (h6 : RootData.RootProducts6) : MatrixRootPowers := by
  intro r
  rw [root_conjugate_of_products hc]
  fin_cases r
  · exact RootData.root_power_0 h0
  · exact RootData.root_power_1 h1
  · exact RootData.root_power_2 h2
  · exact RootData.root_power_3 h3
  · exact RootData.root_power_4 h4
  · exact RootData.root_power_5 h5
  · exact RootData.root_power_6 h6

end ONan.Simplicity.TwoCertificate.Fusion
