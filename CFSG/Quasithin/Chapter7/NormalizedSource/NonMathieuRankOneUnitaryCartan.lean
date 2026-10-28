module
public import Theory.SpecificGroups.SU3.BinaryMersenneActors
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# A sufficient unitary Cartan bound through central covers

Every Cartan witness contains a cyclic group of order 2ᶜ−1. Faithful
central-quotient descent carries its generator into the actual projective
unitary automorphism group. The Mersenne-order bound gives c ≤ 2s.
This weaker bound suffices for the unitary FWCI contradiction once the
ambient H.2 displacement bound is proved by the final source owner.

Source: Aschbacher--Smith E.3.37 and 7.5.2, printed pp.239,700.
-/
public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE.Section06.FixedPointBounds

/-- A weak Cartan bound for every automorphism subgroup of a perfect
central cover of the literal binary unitary model. -/
theorem unitary_centralCover_cartan_bound
    {X F : Type*} [Group X] [Finite X] [Group.IsPerfect X] [Field F] [Finite F]
    (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2^s)^2) (hconj : ∀ x : F, J.conj x = x^(2^s))
    (e : (X ⧸ center X) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (A : Subgroup (MulAut X)) : nPrime A ≤ 2*s := by
  let f := MulAut.centralQuotientAction e
  have hf : Function.Injective f := MulAut.centralQuotientAction_injective e
  apply nPrime_le_iff.mpr
  intro c w
  let := w.cyclic
  obtain ⟨a,ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic w.cyclicGroup)
  let g := (f.comp A.subtype).comp w.cyclicGroup.subtype
  have hg : Function.Injective g := hf.comp (A.subtype_injective.comp w.cyclicGroup.subtype_injective)
  apply J.binary_mersenne_automorphism_bound hs hcard hconj (g a)
  rw [orderOf_injective g hg,ha,w.card]
end CFSG.Quasithin.Chapter7.NormalizedSource
