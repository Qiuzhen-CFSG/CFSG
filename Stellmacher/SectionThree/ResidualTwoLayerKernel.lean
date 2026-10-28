module

public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Theory.GroupAction.SubgroupConjugation

open BenderSuzuki.External
open scoped commutatorElement

namespace Stellmacher.SectionThree

public theorem residual_two_layer_kernel
    {H : Type*} [Group H] [Finite H]
    (P E D : Subgroup H) (hPE : P ≤ Subgroup.normalizer (E : Set H))
    (hDE : D ≤ E) (hE : IsElementaryAbelian 2 E)
    (hfix : ⁅twoResidualAmbient P, D⁆ = ⊥)
    (hquot : ⁅twoResidualAmbient P, E⁆ ≤ D) :
    ⁅twoResidualAmbient P, E⁆ = ⊥ := by
  classical
  let R := twoResidualAmbient P
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 E := hE
  have hRP : R ≤ P := Subgroup.map_subtype_le _
  let _ : MulDistribMulAction R E :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer R E (hRP.trans hPE)
  let rho : R →* MulAut E := MulDistribMulAction.toMulAut R E
  have hfixed (actor : R) (elem : E) (helem : (elem : H) ∈ D) :
      rho actor elem = elem := by
    apply Subtype.ext
    have hcomm : ⁅(actor : H), (elem : H)⁆ = 1 := by
      have hmem := Subgroup.commutator_mem_commutator actor.property helem
      rw [hfix] at hmem
      exact hmem
    have heq := commutatorElement_eq_one_iff_mul_comm.mp hcomm
    change (actor : H) * (elem : H) * (actor : H)⁻¹ = (elem : H)
    rw [heq]
    simp [mul_assoc]
  have hsquare (actor : R) : rho actor ^ 2 = 1 := by
    apply MulEquiv.ext
    intro elem
    let delta : E := rho actor elem * elem⁻¹
    have hdelta : (delta : H) ∈ D := by
      exact hquot (Subgroup.commutator_mem_commutator actor.property elem.property)
    have hdeltafix := hfixed actor delta hdelta
    have hdeltasq : delta * delta = 1 := by
      have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (delta : H) (hDE hdelta)
      apply Subtype.ext
      simpa [pow_two] using hs
    have hdisp : rho actor elem = delta * elem := by
      simp [delta, mul_assoc]
    change rho actor (rho actor elem) = elem
    calc
      rho actor (rho actor elem) = rho actor (delta * elem) := congrArg _ hdisp
      _ = delta * rho actor elem := by rw [map_mul, hdeltafix]
      _ = delta * (delta * elem) := congrArg (delta * ·) hdisp
      _ = elem := by rw [← mul_assoc, hdeltasq, one_mul]
  have himage : IsPGroup 2 rho.range := by
    intro image
    obtain ⟨actor, hactor⟩ := image.property
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [← hactor] using hsquare actor
  have hquotient : IsPGroup 2 (R ⧸ rho.ker) :=
    himage.of_equiv (QuotientGroup.quotientKerEquivRange rho).symm
  have hker : hktPResidual 2 R ≤ rho.ker :=
    hktPResidual_le rho.ker inferInstance hquotient
  rw [twoResidualAmbient_has_top_twoResidual P] at hker
  apply le_antisymm _ bot_le
  apply Subgroup.commutator_le.mpr
  intro actor hactor elem helem
  have htrivial : rho ⟨actor, hactor⟩ = 1 := hker (by trivial)
  have hpoint := congrArg (fun equiv : MulAut E => equiv ⟨elem, helem⟩) htrivial
  have hconj := congrArg Subtype.val hpoint
  change actor * elem * actor⁻¹ = elem at hconj
  change ⁅actor, elem⁆ = 1
  simp [commutatorElement_def, hconj]

end Stellmacher.SectionThree

