module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.InvolutionCentralizer
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Binary
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Returning conjugates inside the actual group G₂(2)′

The intrinsic center of the derived positive-root Sylow identifies every
Sylow-central involution with A(1) by conjugation inside the derived group.
The long-root Weyl element R is in that group, as is SRS⁻¹ by normality.
These internal conjugators carry A(1) to B(1) and E(1), respectively. Both
roots belong to the derived Sylow, and their existing shear identity shows
that they do not commute. Derived-group Sylow conjugacy transports the pair.

This is the marked-class model input for the G₂(2)′ row of
Aschbacher--Smith 1.1.5(3)(a), Theorem C(3), and Proposition 2.2.2,
printed pp.33, 501--503 and 519--520 (combined 1 March 2004 manuscript).
The imported octonion calculations retain the attribution and license in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinaryMarkedStrongClosure
open BinaryParabolicPair LieParabolicSetup SylowParabolicInvariance

/-- The conjugator recovering the actual central marker belongs to G₂(2)′,
not merely to the full octonion automorphism group. -/
theorem central_isConj_derivedInvolution (R : Sylow 2 DerivedModel)
    (v : DerivedModel) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) : IsConj derivedInvolution v := by
  have hsq : v ^ 2 = 1 := by simpa only [ho] using pow_orderOf_eq_one v
  have hne : v ≠ 1 := by
    intro he
    have hh : (1 : ℕ) = 2 := by simpa only [he, orderOf_one] using ho
    exact (by decide : (1 : ℕ) ≠ 2) hh
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq DerivedModel derivedSylow R
  have hm : (derivedSylow : Subgroup DerivedModel).map (MulAut.conj g).toMonoidHom =
      (R : Subgroup DerivedModel) := congrArg Sylow.toSubgroup hg
  have hv' : v ∈ (derivedSylow : Subgroup DerivedModel).map
      (MulAut.conj g).toMonoidHom := hm.symm ▸ hv
  obtain ⟨y, hy, rfl⟩ := hv'
  have hcent : CentralInvolution (derivedSylow : Subgroup DerivedModel) y := by
    apply (centralInvolution_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      (derivedSylow : Subgroup DerivedModel) y).mp
    rw [hm]
    exact ⟨hm ▸ mem_map_of_mem _ hy, hsq, hc⟩
  have hamb : CentralInvolution derivedSylowAmbient y.val := by
    rw [← derivedSylow_map_subtype]
    exact (centralInvolution_map_iff DerivedModel.subtype DerivedModel.subtype_injective
      (derivedSylow : Subgroup DerivedModel) y).mpr hcent
  obtain ⟨a, ha⟩ := (binary_highestRoot_iff y.val).mpr hamb
  have ha0 : a.toAdd ≠ 0 := by
    intro hzero
    apply hne
    apply Subtype.ext
    change MulAut.conj g.val y.val = 1
    rw [← ha]
    change MulAut.conj g.val (rootA a.toAdd) = 1
    rw [hzero, rootA_zero, map_one]
  have ha1 : a.toAdd = 1 :=
    (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a.toAdd ha0
  have hyz : y = derivedInvolution := by
    apply Subtype.ext
    change y.val = rootA (1 : ZMod 2)
    rw [← ha]
    change rootA a.toAdd = rootA (1 : ZMod 2)
    rw [ha1]
  apply isConj_iff.mpr
  refine ⟨g, ?_⟩
  change MulAut.conj g derivedInvolution = MulAut.conj g y
  rw [hyz]

private theorem standard_sylow_pair :
    ∃ a b : DerivedModel, a ∈ derivedSylow ∧ b ∈ derivedSylow ∧
      IsConj derivedInvolution a ∧ IsConj derivedInvolution b ∧ ¬Commute a b := by
  have hR : (weylR : Model (ZMod 2)) ∈ DerivedModel := by
    change (weylR : Model (ZMod 2)) ∈ commutator (Model (ZMod 2))
    rw [commutator_eq_longRootClosure]
    exact BinaryException.weylR_in_H
  have hB : rootB (1 : ZMod 2) ∈ DerivedModel := by
    change rootB (1 : ZMod 2) ∈ commutator (Model (ZMod 2))
    rw [commutator_eq_longRootClosure]
    exact BinaryException.rootB_in_H 1
  have hE : rootE (1 : ZMod 2) ∈ DerivedModel := by
    change rootE (1 : ZMod 2) ∈ commutator (Model (ZMod 2))
    rw [commutator_eq_longRootClosure]
    exact BinaryException.rootE_in_H 1
  let r : DerivedModel := ⟨weylR, hR⟩
  let q : DerivedModel := ⟨weylS * weylR * weylS⁻¹,
    (inferInstance : DerivedModel.Normal).conj_mem _ hR _⟩
  let a : DerivedModel := ⟨rootB 1, hB⟩
  let b : DerivedModel := ⟨rootE 1, hE⟩
  have ha : a ∈ derivedSylow := by
    change a ∈ (derivedSylow : Subgroup DerivedModel)
    rw [derivedSylow_eq]
    change rootB (1 : ZMod 2) ∈ unipotent
    exact subset_closure (by simp)
  have hb : b ∈ derivedSylow := by
    change b ∈ (derivedSylow : Subgroup DerivedModel)
    rw [derivedSylow_eq]
    change rootE (1 : ZMod 2) ∈ unipotent
    exact subset_closure (by simp)
  have hca : IsConj derivedInvolution a := by
    apply isConj_iff.mpr
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact weylR_rootA (1 : ZMod 2)
  have hcb : IsConj derivedInvolution b := by
    apply isConj_iff.mpr
    refine ⟨q, ?_⟩
    apply Subtype.ext
    change (weylS * weylR * weylS⁻¹) * rootA (1 : ZMod 2) *
      (weylS * weylR * weylS⁻¹)⁻¹ = rootE 1
    have hs : weylS⁻¹ * rootA (1 : ZMod 2) * weylS = rootA 1 := by
      rw [(weylS_commute_rootA (1 : ZMod 2)).inv_left.eq]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    calc
      (weylS * weylR * weylS⁻¹) * rootA (1 : ZMod 2) *
          (weylS * weylR * weylS⁻¹)⁻¹ =
          weylS * (weylR * (weylS⁻¹ * rootA 1 * weylS) * weylR⁻¹) * weylS⁻¹ := by
        group
      _ = weylS * (weylR * rootA 1 * weylR⁻¹) * weylS⁻¹ := by rw [hs]
      _ = rootE 1 := by rw [weylR_rootA, weylS_rootB]
  refine ⟨a, b, ha, hb, hca, hcb, ?_⟩
  intro hab
  have hc : Commute (rootB (1 : ZMod 2)) (rootE 1) := hab.map DerivedModel.subtype
  have he : MulAut.conj (rootE (1 : ZMod 2)) (rootB 1) = rootB 1 := by
    rw [MulAut.conj_apply, hc.symm.eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [ShortRootProducts.rootE_conjugate_rootB, one_mul] at he
  have hz : rootA (1 : ZMod 2) = 1 := mul_right_cancel (he.trans (one_mul _).symm)
  exact one_ne_zero (rootA_injective (hz.trans rootA_zero.symm))

/-- Every actual derived Sylow contains noncommuting internal conjugates
of the given Sylow-central involution. -/
theorem sylow_noncommuting_conjugates (v : DerivedModel)
    (hv : IsSylowCentralInvolution v) (R : Sylow 2 DerivedModel) :
    ∃ a b : R, IsConj v (a : DerivedModel) ∧ IsConj v (b : DerivedModel) ∧
      ¬Commute a b := by
  obtain ⟨ho, P, hvP, hc⟩ := hv
  have hm : IsConj derivedInvolution v := central_isConj_derivedInvolution P v hvP ho
    (fun x hx => (mem_centralizer_singleton_iff.mp (hc hx)).symm)
  obtain ⟨x, y, hx, hy, hcx, hcy, hxy⟩ := standard_sylow_pair
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq DerivedModel derivedSylow R
  have hmap : (derivedSylow : Subgroup DerivedModel).map (MulAut.conj g).toMonoidHom =
      (R : Subgroup DerivedModel) := congrArg Sylow.toSubgroup hg
  let a : R := ⟨MulAut.conj g x, by
    change MulAut.conj g x ∈ (R : Subgroup DerivedModel)
    rw [← hmap]
    exact mem_map_of_mem _ hx⟩
  let b : R := ⟨MulAut.conj g y, by
    change MulAut.conj g y ∈ (R : Subgroup DerivedModel)
    rw [← hmap]
    exact mem_map_of_mem _ hy⟩
  refine ⟨a, b, (hm.symm.trans hcx).trans (isConj_iff.mpr ⟨g, rfl⟩),
    (hm.symm.trans hcy).trans (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
  intro hab
  apply hxy
  apply (MulAut.conj g).injective
  have he := congrArg Subtype.val hab.eq
  exact ((MulAut.conj g).map_mul _ _).trans (he.trans ((MulAut.conj g).map_mul _ _).symm)

end Atlas.G2.BinaryMarkedStrongClosure
