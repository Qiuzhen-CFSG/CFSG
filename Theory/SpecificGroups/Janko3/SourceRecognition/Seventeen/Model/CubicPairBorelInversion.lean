module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.PairInvolutionInner
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.PairBorelGeometry
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerKernelInversion
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerThirdModel
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicModelPairEquiv

/-!
# Simultaneous Borel exchange and cubic-kernel inversion

For any isomorphism between the two full pairs, cubic-kernel inversion
corresponds to conjugation by an involution in the sixteen-field pair.
It moves a nontrivial overlap cubic and hence exchanges the two Borels.
This corrects the Borel orientation without changing the cubic complement
or any full projective preimage, including the fixed third overlap.
-/

noncomputable section
open Subgroup Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
local notation "CM" => CubicNormalizerModel.Model
local notation "κ" => CubicNormalizerModel.kernelInversion

private theorem cubic_inversion_squared (x : CM) : κ (κ x) = x := by
  apply SemidirectProduct.ext
  · exact inv_inv x.left
  · rfl

private theorem cubic_pair_cube_inverted (x : CubicNormalizerModel.pair)
    (hx : x ^ 3 = 1) : κ (x : CM) = (x : CM)⁻¹ := by
  let p : CubicNormalizerModel.projectivePair := ⟨x.val.right,x.property⟩
  have hp3 : p ^ 3 = 1 := by
    apply Subtype.ext
    have hh : (x : CM) ^ 3 = 1 := congrArg (fun z : CubicNormalizerModel.pair => (z : CM)) hx
    have hh := congrArg CubicNormalizerModel.projection hh
    change x.val.right ^ 3 = 1
    exact (show CubicNormalizerModel.projection (x : CM) ^ 3 = 1 by
      simpa only [map_pow,map_one] using hh)
  have hp20 : orderOf p ∣ 20 := by
    rw [←CubicNormalizerModel.projectivePair_card]
    exact orderOf_dvd_natCard p
  have hp : p = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by
    simpa using Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp3) hp20))
  have hr : x.val.right = 1 := congrArg Subtype.val hp
  have he : (x : CM) = SemidirectProduct.inl x.val.left := by
    apply SemidirectProduct.ext
    · rfl
    · exact hr
  rw [he,CubicNormalizerModel.kernelInversion_inl,←map_inv]

private theorem cubic_pair_cube_not_fixed (x : CubicNormalizerModel.pair)
    (hx : x ^ 3 = 1) (hne : x ≠ 1) : κ (x : CM) ≠ (x : CM) := by
  intro he
  rw [cubic_pair_cube_inverted x hx] at he
  have h2 : (x : CM) ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [←he]
    exact inv_mul_cancel _
  have h3 : (x : CM) ^ 3 = 1 := congrArg Subtype.val hx
  have hh : (x : CM) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by
    simpa using Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one h3)))
  exact hne (Subtype.ext hh)

/-- Every chosen full-pair identification admits a simultaneous Borel
exchange and cubic-kernel inversion. The conjugating pair element is an
actual involution, and equality holds on every pair element. -/
public theorem exists_pair_borel_inversion (ε : pair ≃* CubicNormalizerModel.pair) :
    ∃ b : pair, b ^ 2 = 1 ∧
      point.map (MulAut.conj (b : Model)).toMonoidHom = oppositePoint ∧
      oppositePoint.map (MulAut.conj (b : Model)).toMonoidHom = point ∧
      ∀ z : pair, κ (ε z : CM) = (ε (MulAut.conj b z) : CM) := by
  let α : MulAut CubicNormalizerModel.pair :=
    (CubicNormalizerModel.kernelInversion.subgroupMap CubicNormalizerModel.pair).trans
      (MulEquiv.subgroupCongr
        (CubicNormalizerModel.kernelInversion_preimage CubicNormalizerModel.projectivePair))
  let φ : MulAut pair := ε.trans (α.trans ε.symm)
  have hε (z : pair) : κ (ε z : CM) = (ε (φ z) : CM) := by
    change κ (ε z : CM) = (ε (ε.symm (α (ε z))) : CM)
    rw [ε.apply_symm_apply]
    rfl
  have hφ : φ * φ = 1 := by
    apply MulEquiv.ext
    intro z
    apply ε.injective
    apply Subtype.ext
    change (ε (φ (φ z)) : CM) = (ε z : CM)
    rw [←hε (φ z),←hε z,cubic_inversion_squared]
  obtain ⟨b,hb,hinner⟩ := pair_involution_inner φ hφ
  have hcompat (z : pair) : κ (ε z : CM) = (ε (MulAut.conj b z) : CM) := by
    rw [←hinner]
    exact hε z
  let u : Multiplicative (ZMod 3) × DihedralGroup 5 := (Multiplicative.ofAdd 1,1)
  have hu3 : u ^ 3 = 1 := by decide +kernel
  have hune : u ≠ 1 := by decide +kernel
  let s : ↥(point ⊓ pair) := overlapEquiv.symm u
  have hs3 : s ^ 3 = 1 := by
    apply overlapEquiv.injective
    rw [map_pow,map_one]
    exact (congrArg (fun v => v ^ 3) (overlapEquiv.apply_symm_apply u)).trans hu3
  have hsne : s ≠ 1 := by
    intro he
    apply hune
    have hh := congrArg overlapEquiv he
    simpa only [s,overlapEquiv.apply_symm_apply,map_one] using hh
  let sp : pair := ⟨s,s.property.2⟩
  have hsp3 : sp ^ 3 = 1 := Subtype.ext
    (congrArg (fun z : ↥(point ⊓ pair) => (z : Model)) hs3)
  have hspne : sp ≠ 1 := fun he => hsne (Subtype.ext
    (congrArg (fun z : pair => (z : Model)) he))
  have hnot : ¬ Commute (b : Model) (s : Model) := by
    intro hc
    have hi : MulAut.conj b sp = sp := by
      apply Subtype.ext
      change (b : Model) * (s : Model) * (b : Model)⁻¹ = (s : Model)
      rw [hc.eq,mul_inv_cancel_right]
    have hx3 : (ε sp) ^ 3 = 1 := by rw [←map_pow,hsp3,map_one]
    have hxne : ε sp ≠ 1 := fun he => hspne (ε.injective (he.trans (map_one ε).symm))
    apply cubic_pair_cube_not_fixed (ε sp) hx3 hxne
    rw [hcompat sp,hi]
  have hpoint : point.map (MulAut.conj (b : Model)).toMonoidHom = oppositePoint :=
    pair_conj_point_eq_opposite_of_not_commute s.property
      (congrArg Subtype.val hs3) b hnot
  refine ⟨b,hb,hpoint,?_,hcompat⟩
  rw [←hpoint,map_map]
  have hcomp : (MulAut.conj (b : Model)).toMonoidHom.comp
      (MulAut.conj (b : Model)).toMonoidHom = MonoidHom.id Model := by
    apply MonoidHom.ext
    intro x
    have hb' : (b : Model) * (b : Model) = 1 := by
      have hh : (b : Model) ^ 2 = 1 := congrArg (fun z : pair => (z : Model)) hb
      simpa only [pow_two] using hh
    change (b : Model) * ((b : Model) * x * (b : Model)⁻¹) * (b : Model)⁻¹ = x
    calc
      _ = ((b : Model) * (b : Model)) * x * ((b : Model) * (b : Model))⁻¹ := by group
      _ = x := by rw [hb',one_mul,inv_one,mul_one]
  rw [hcomp,map_id]

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
