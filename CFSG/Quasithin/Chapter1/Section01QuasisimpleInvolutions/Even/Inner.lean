module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Basic
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.SU3.SylowPointwiseInner.Full
public import Theory.SpecificGroups.Suzuki.BorelPointwiseRigidity
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SylowPointwiseInner
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.SylowFixers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.BinarySylowFixers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.Tits.SylowPointwiseInner
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms

/-!
# Marked Sylow-fixer calculations for the even families

The intrinsic matrix and root calculations apply to the actual central quotient
and lift to its perfect cover. In particular, all geometric classification
premises for Sp₄ and G₂ are discharged, and the small G₂ case uses its actual
derived carrier. The large Ree case uses the proved odd-outer calculation;
the Tits endpoint has its separate pointwise-Sylow calculation.

These results establish innerness, not the remaining covering-group exclusions.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.502, with the
automorphism calculations also used in 16.1.6, printed p.1172.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

theorem MarkedInvolution.linearTwo_inner (d : MarkedInvolution α P) {f : ℕ}
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2 ^ f)) :
    α ∈ (MulAut.conj (G := L)).range := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact d.inner_of_model_fixer e Theory.PSL2.aut_fixing_sylow_inner

theorem MarkedInvolution.unitaryThree_inner (d : MarkedInvolution α P) {f : ℕ}
    (hf : 2 ≤ f) (h : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ f)) :
    α ∈ (MulAut.conj (G := L)).range := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let := e.symm.isSimpleGroup
  exact d.inner_of_model_fixer e
    (BenderSuzuki.MatrixGroups.HermitianForm.SylowPointwiseInner.fixing_sylow_eq_mem_conj
      J hf hF hconj)

theorem MarkedInvolution.suzuki_inner (d : MarkedInvolution α P) {m : ℕ}
    (hm : 1 ≤ m)
    (e : L ⧸ center L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    α ∈ (MulAut.conj (G := L)).range :=
  d.inner_of_model_fixer e (fun Q a ha =>
    BenderSuzuki.MatrixGroups.suzuki_aut_fixing_sylow_inner (by omega)
      (MulEquiv.refl _) Q a ha)

/-- Every Bender family forces innerness on the original quasisimple cover. -/
theorem MarkedInvolution.bender_inner (d : MarkedInvolution α P)
    (h : IsBenderModel (L ⧸ center L)) :
    α ∈ (MulAut.conj (G := L)).range := by
  cases h with
  | linear f _ h => exact d.linearTwo_inner h
  | unitary f hf h => exact d.unitaryThree_inner hf h
  | suzuki m hm h => obtain ⟨e⟩ := h; exact d.suzuki_inner hm e

/-- The pointwise-fixer result includes the exceptional field sizes two and four. -/
theorem MarkedInvolution.linearThree_inner (d : MarkedInvolution α P) {f : ℕ}
    (hf : 1 ≤ f) (h : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ f)) :
    α ∈ (MulAut.conj (G := L)).range := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  apply d.inner_of_model_fixer e
  intro Q a ha
  obtain ⟨_, ⟨z, _, rfl⟩, he⟩ :=
    Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv F (by omega) hF
      (MulEquiv.refl _) Q a ha
  exact ⟨z, z.property, he⟩

theorem MarkedInvolution.symplecticFour_inner (d : MarkedInvolution α P) {f : ℕ}
    (hf : 2 ≤ f) (h : ClassicalGroup.IsPSp (L ⧸ center L) 2 (2 ^ f)) :
    α ∈ (MulAut.conj (G := L)).range := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  apply d.inner_of_model_fixer
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
  exact Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.aut_fixing_sylow_inner
    hF (by omega)
    Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram

theorem MarkedInvolution.g2_inner (d : MarkedInvolution α P) {f : ℕ}
    (hf : 2 ≤ f) (h : IsG2At (L ⧸ center L) (2 ^ f)) :
    α ∈ (MulAut.conj (G := L)).range := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hpow : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
  exact d.inner_of_model_fixer e (Atlas.G2.EvenInvolutionGeometry.fixing_sylow_inner
    (Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective (by omega)))

theorem MarkedInvolution.g2Derived_inner (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    α ∈ (MulAut.conj (G := L)).range :=
  d.inner_of_model_fixer e (Atlas.G2.EvenInvolutionGeometry.binary_fixing_sylow_inner
    Atlas.G2.LieAutomorphismExtensions.binaryConjugation_bijective)

theorem MarkedInvolution.binaryLinear_inner (d : MarkedInvolution α P) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (h : ClassicalGroup.IsPSL (L ⧸ center L) n 2) :
    α ∈ (MulAut.conj (G := L)).range := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact d.inner_of_model_fixer
    (e.trans ((Atlas.fieldEquivPSL n eF).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega))))
    (BinaryLinear.OuterCyclic.sylow_fixing_inner hn)

theorem MarkedInvolution.tits_inner (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* Tits.ParrottGroup) :
    α ∈ (MulAut.conj (G := L)).range :=
  d.inner_of_model_fixer e Tits.SylowPointwiseInner.parrott_fixing_sylow_inner

theorem MarkedInvolution.ree_inner (d : MarkedInvolution α P) {m : ℕ}
    (hm : 1 ≤ m) (e : L ⧸ center L ≃* ReeF4.Model m) :
    α ∈ (MulAut.conj (G := L)).range := by
  have ho := (d.centralQuotient_model_inputs e).1
  apply (d.inner_and_center_of_quotient_inner e ?_).1
  exact ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.inner_of_sq_eq_one hm
    (MulAut.centralQuotientAction e α)
    (by simpa only [ho] using pow_orderOf_eq_one (MulAut.centralQuotientAction e α))

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
