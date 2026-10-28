module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.CharacteristicOuterRestriction
public import Theory.ElementaryAbelian.AutomorphismLinearModel
public import Theory.GroupTheory.NormalizerQuotientNilpotent
public import Theory.AtlasPort.LinearGroups.SL2Order
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Outer restriction for the natural elementary odd kernel

The scalar minus-one element of the actual SL₂(p) quotient lifts to an
involution: it inverts the odd elementary kernel, so its square, which it
also fixes, is trivial. Self-centralization of the generalized Fitting
subgroup and this inversion show that pointwise kernel-fixing automorphisms
are inner. This does not assume the extension splits.

On the two-dimensional prime-field coordinates, perfectness puts the
conjugation image in SL₂(p), and its order proves equality. The determinant
then makes the corresponding normalizer quotient nilpotent. The actual
outer group embeds in that quotient, proving its two-closedness for every
prime allowed by A.3.6(3).

Source: Aschbacher--Smith A.3.6(3), pp.43--45; 11.4.3, p.778.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NaturalOdd

variable {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]

omit [Group.IsPerfect B] in
private theorem natural_inverting_involution (N : Subgroup B) [N.Normal]
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hn : LocalModels.NaturalSL2Action B N p) :
    ∃ t : B, orderOf t = 2 ∧ QuotientGroup.mk' N t ∈ center (B ⧸ N) ∧
      ∀ x : N, (MulAut.conjNormal t : MulAut N) x = x⁻¹ := by
  have hodd : Odd (Nat.card N) := by
    rw [(RadicalStructure.natural_elementary hn).2]
    exact (hp.odd_of_ne_two (by omega)).pow
  obtain ⟨F, _, _, hcard, v, e, hact⟩ := hn
  have h2 : (2 : F) ≠ 0 :=
    GorensteinWalter.two_ne_zero_of_odd_card F (hcard ▸ hp.odd_of_ne_two (by omega))
  obtain ⟨t, ht⟩ := ((e.surjective).comp (QuotientGroup.mk'_surjective N)) (-1)
  change e (QuotientGroup.mk' N t) = -1 at ht
  have hinv (x : N) : (MulAut.conjNormal t : MulAut N) x = x⁻¹ := by
    apply v.injective
    change v ⟨t * x * t⁻¹, _⟩ = _
    rw [hact, ht, map_inv]
    change Multiplicative.ofAdd (Matrix.mulVec (-1 : Matrix (Fin 2) (Fin 2) F)
      (Multiplicative.toAdd (v x))) = (v x)⁻¹
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
    rfl
  have fixed (x : N) (hx : (MulAut.conjNormal t : MulAut N) x = x) : x = 1 := by
    have hs : x ^ 2 = 1 := by
      have he : x⁻¹ = x := (hinv x).symm.trans hx
      rw [pow_two]
      nth_rw 1 [← he]
      exact inv_mul_cancel _
    exact hodd.coprime_two_right.pow_left_bijective.injective (hs.trans (one_pow 2).symm)
  have htN : t ^ 2 ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    change e (QuotientGroup.mk' N (t ^ 2)) = e 1
    rw [map_pow, map_pow, ht, map_one]
    apply Subtype.ext
    simp
  have ht2 : t ^ 2 = 1 := by
    exact congrArg Subtype.val (fixed ⟨t ^ 2, htN⟩ (by
      apply Subtype.ext
      change t * t ^ 2 * t⁻¹ = t ^ 2
      group))
  have htne : t ≠ 1 := by
    intro he
    have hneg : (-1 : SL(2, F)) = 1 := by simpa [he] using ht.symm
    have hh : (-1 : F) = 1 := congrArg (fun a : SL(2, F) => a 0 0) hneg
    apply h2
    linear_combination -hh
  refine ⟨t, orderOf_eq_prime ht2 htne, ?_, hinv⟩
  apply mem_center_iff.mpr
  intro g
  apply e.injective
  simp only [map_mul, ht]
  apply Subtype.ext
  simp

/-- Pointwise fixation of the actual natural kernel detects inner automorphisms. -/
theorem restriction_kernel (hn : A36Natural B) :
    (MulAut.characteristic (fittingSubgroup B)).ker ≤ MulAut.innerSubgroup B := by
  obtain ⟨p, hp, hlarge, ha⟩ := hn.2
  have ha : LocalModels.NaturalSL2Action B (fittingSubgroup B) p := by
    simpa only [hn.1] using ha
  have hself : centralizer (fittingSubgroup B : Set B) ≤ fittingSubgroup B := by
    rw [← hn.1]
    exact centralizer_generalizedFitting_le B
  have hodd : Odd (Nat.card (fittingSubgroup B)) := by
    rw [(RadicalStructure.natural_elementary ha).2]
    exact (hp.odd_of_ne_two (by omega)).pow
  obtain ⟨t, ht, hcentral, hinv⟩ := natural_inverting_involution _ hp hlarge ha
  apply CharacteristicOuterRestriction.restriction_kernel_le_inner_of_involution
    (fittingSubgroup B) hself hodd t ht hcentral
  intro x hx
  have hxN := hself hx.1
  have he : (⟨x, hxN⟩ : fittingSubgroup B)⁻¹ = ⟨x, hxN⟩ := by
    rw [← hinv]
    apply Subtype.ext
    change t * x * t⁻¹ = x
    rw [← (mem_centralizer_singleton_iff.mp hx.2), mul_inv_cancel_right]
  have hs : (⟨x, hxN⟩ : fittingSubgroup B) ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [← he]
    exact inv_mul_cancel _
  have hxone : (⟨x, hxN⟩ : fittingSubgroup B) = 1 :=
    hodd.coprime_two_right.pow_left_bijective.injective (hs.trans (one_pow 2).symm)
  have hxone' : x = 1 := congrArg Subtype.val hxone
  rw [hxone']
  exact one_mem _



private def detKernelEquiv {F : Type*} [Field F] :
    (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).ker ≃* SL(2, F) where
  toFun g := ⟨g.val.val, congrArg Units.val g.property⟩
  invFun g := ⟨Matrix.SpecialLinearGroup.toGL g, Matrix.SpecialLinearGroup.coeToGL_det g⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem natural_action_image (hn : A36Natural B) {p : ℕ} [Fact p.Prime]
    (ha : LocalModels.NaturalSL2Action B (fittingSubgroup B) p)
    (a : MulAut (fittingSubgroup B) ≃* GL (Fin 2) (ZMod p)) :
    (a.toMonoidHom.comp (MulAut.conjNormal : B →* MulAut (fittingSubgroup B))).range =
      (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod p)).ker := by
  let ρ := a.toMonoidHom.comp (MulAut.conjNormal : B →* MulAut (fittingSubgroup B))
  let d := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod p)
  have hk : ρ.ker = fittingSubgroup B := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,
      MulAut.conjNormal_ker_eq_centralizer]
    apply le_antisymm
    · rw [← hn.1]
      exact centralizer_generalizedFitting_le B
    · let := (RadicalStructure.natural_elementary ha).1
      exact Subgroup.le_centralizer (H := fittingSubgroup B)
  have hle : ρ.range ≤ d.ker := by
    rintro _ ⟨b, rfl⟩
    have hh := Abelianization.commutator_subset_ker (d.comp ρ)
    rw [Group.IsPerfect.commutator_eq_top] at hh
    exact hh (mem_top b)
  obtain ⟨F, _, _, hF, _, e, _⟩ := ha
  have hc : Nat.card ρ.range = Nat.card d.ker := by
    calc
      Nat.card ρ.range = Nat.card (B ⧸ ρ.ker) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv).symm
      _ = Nat.card (B ⧸ fittingSubgroup B) :=
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hk).toEquiv
      _ = Nat.card SL(2, F) := Nat.card_congr e.toEquiv
      _ = Nat.card SL(2, ZMod p) := by rw [Atlas.card_sl_two, Atlas.card_sl_two, hF, Nat.card_zmod]
      _ = Nat.card d.ker := (Nat.card_congr detKernelEquiv.toEquiv).symm
  exact eq_of_le_of_card_ge hle hc.ge

private theorem determinant_normalizer_nilpotent {F : Type*} [Field F] :
    Group.IsNilpotent (NormalizerOuterQuotient.Quotient
      (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).ker) := by
  let d := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)
  let N := normalizer (d.ker : Set (GL (Fin 2) F))
  let ψ : NormalizerOuterQuotient.Quotient d.ker →* Fˣ :=
    QuotientGroup.lift (d.ker.subgroupOf N) (d.comp N.subtype) (by
      intro x hx
      exact hx)
  have hk : ψ.ker = ⊥ := by
    apply bot_unique
    intro x hx
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (d.ker.subgroupOf N) x
    exact (QuotientGroup.eq_one_iff _).mpr hx
  exact Subgroup.isNilpotent_of_ker_le_center ψ (by rw [hk]; exact bot_le)

/-- The full outer group of a perfect natural odd-kernel component is nilpotent. -/
theorem outer_nilpotent (hn : A36Natural B) :
    Group.IsNilpotent (MulAut.Outer B) := by
  obtain ⟨p, hp, _, ha⟩ := hn.2
  have ha : LocalModels.NaturalSL2Action B (fittingSubgroup B) p := by
    simpa only [hn.1] using ha
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨he, hcard⟩ := RadicalStructure.natural_elementary ha
  let := he
  let a := IsElementaryAbelian.mulAutLinearEquivOfCard (fittingSubgroup B) hcard
  let f := a.toMonoidHom.comp (MulAut.characteristic (fittingSubgroup B))
  have hk : f.ker ≤ MulAut.innerSubgroup B := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    exact restriction_kernel hn
  apply NormalizerOuterQuotient.nilpotent_quotient_of_map (MulAut.innerSubgroup B) f hk
  have hρ : f.comp (MulAut.conj : B →* MulAut B) =
      a.toMonoidHom.comp (MulAut.conjNormal : B →* MulAut (fittingSubgroup B)) := by
    apply MonoidHom.ext
    intro b
    exact congrArg a (characteristic_conj_eq_conjNormal (fittingSubgroup B) b)
  change Group.IsNilpotent (NormalizerOuterQuotient.Quotient
    (((MulAut.conj : B →* MulAut B).range).map f))
  rw [← MonoidHom.range_comp, hρ, natural_action_image hn ha a]
  exact determinant_normalizer_nilpotent

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NaturalOdd
