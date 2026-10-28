module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalBlockMaximal

/-!
# Original normalizer inputs for general linear-three completion

A compatible comparison of the two full normalizers transports their literal
inclusions to a completion in the original ambient group, using source-proved
generation as an explicit premise. It retains the entire intersection and
transports the source cube-in-middle witness in either orientation. The
prepared-row application preserves the equality with the original exponent.

For the native comparison, conjugation by the original common normalizer
acts on both pure parabolics when it normalizes the source S. Transport uses
all three maps of the same comparison and retains both endpoint equations
and the whole-overlap equation. The native paired cubic relation gives its
unique global PSL₃ action with both endpoint equations. The source cubic
relation gives full ambient order and faithful extension recognition; ambient
simplicity then gives the actual PSL₃ isomorphism and IsPSL witness.

Source: Aschbacher–Smith 5.3.1–2,7, pp.658–660, F.4.3,8–9,49,
pp.274,278–279,298–299 (`refs/quasithin.pdf`). The source owner retains
normalization of S, full-normalizer comparison, ambient generation and the
Hall-quotient cubic witness and final endpoint gluing. The conditional
recognition below discharges the completion step under those source inputs.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion
open ChapterF.SourceCompletion
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G] (L K : Subgroup G)
variable {F : Type*} [Field F] (E : SourceExtension F)

abbrev NormalizerComparison :=
  RankTwoAmalgam.Iso
    (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (K : Set G))) E.amalgam ⊕
  RankTwoAmalgam.Iso
    (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (K : Set G))) E.amalgam.reverse

/-- Generation is an explicit SOURCE input; the carrier here is the original G. -/
def normalizerCompletion (e : NormalizerComparison L K E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (K : Set G) = ⊤) : Completion E G :=
  match e with
  | .inl f => (RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _
      inf_le_left inf_le_right hgen).comapIso f.symm
  | .inr f => UnitaryNonbinary.Generated.reverseCompletion
      ((RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _
        inf_le_left inf_le_right hgen).comapIso f.symm)

theorem normalizerCompletion_ranges (e : NormalizerComparison L K E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (K : Set G) = ⊤) :
    let c := normalizerCompletion L K E e hgen
    (c.left.range = normalizer (L : Set G) ∧ c.right.range = normalizer (K : Set G)) ∨
    (c.left.range = normalizer (K : Set G) ∧ c.right.range = normalizer (L : Set G)) := by
  cases e with
  | inl f =>
    left
    simp only [normalizerCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range,
      RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range,and_self]
  | inr f =>
    right
    change (RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _ _ _ hgen |>.comapIso f.symm).right.range = _ ∧
      (RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _ _ _ hgen |>.comapIso f.symm).left.range = _
    simp only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range,
      RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range,and_self]

theorem normalizerCompletion_middle (e : NormalizerComparison L K E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (K : Set G) = ⊤) :
    (normalizerCompletion L K E e hgen).middle.range =
      normalizer (L : Set G) ⊓ normalizer (K : Set G) := by
  cases e with
  | inl f =>
    simp only [normalizerCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range,
      RankTwoAmalgam.FaithfulCompletion.ofSubgroups_middle_range]
  | inr f =>
    change ((RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _ _ _ hgen |>.comapIso f.symm).right.comp
      E.amalgam.left).range = _
    have hh := congrArg MonoidHom.range
      (RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _ _ _ hgen |>.comapIso f.symm).compatible.symm
    exact hh.trans ((RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range _ f.symm).trans
      (RankTwoAmalgam.FaithfulCompletion.ofSubgroups_middle_range _ _ _ _ _ _))

theorem normalizerCompletion_overlap (e : NormalizerComparison L K E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (K : Set G) = ⊤) :
    let c := normalizerCompletion L K E e hgen
    c.left.range ⊓ c.right.range = c.middle.range := by
  dsimp only
  rw [normalizerCompletion_middle]
  rcases normalizerCompletion_ranges L K E e hgen with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · rw [hl,hr]
  · rw [hl,hr,inf_comm]

/-- Transport the literal source witness, reversing its two elements together
when the native endpoint comparison has the opposite orientation. -/
theorem normalizerCompletion_apartment_input (e : NormalizerComparison L K E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (K : Set G) = ⊤)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (K : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (K : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (K : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G)) :
    let c := normalizerCompletion L K E e hgen
    c.left.range ⊓ c.right.range = c.middle.range ∧
    ∃ u v : G, u ∈ c.left.range ∧ v ∈ c.right.range ∧
      u ∉ c.middle.range ∧ v ∉ c.middle.range ∧ u^2=1 ∧ v^2=1 ∧
      (u*v)^3 ∈ c.middle.range := by
  dsimp only
  refine ⟨normalizerCompletion_overlap L K E e hgen,?_⟩
  rw [normalizerCompletion_middle]
  rcases normalizerCompletion_ranges L K E e hgen with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · exact ⟨s,t,hl ▸ hs,hr ▸ ht,hsout,htout,hs2,ht2,hcube⟩
  · have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs2)
    have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
    have hrev : (t*s)^3 ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G) := by
      simpa only [←inv_pow,mul_inv_rev,hsi,hti] using
        (normalizer (L : Set G) ⊓ normalizer (K : Set G)).inv_mem hcube
    exact ⟨t,s,hl ▸ ht,hr ▸ hs,htout,hsout,ht2,hs2,hrev⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G] [Finite G]

/-- The actual prepared linear row supplies the original exponent to the
full-normalizer completion input. Ambient generation and the source cubic
witness remain explicit, including in the even-degree and field-four cases. -/
theorem Preparation.linear_full_normalizer_completion_input
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (E : SourceExtension F) (e : LinearCompletion.NormalizerComparison L (residual H) E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (residual H : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :
    m = n ∧ 1 < m ∧
    let c := LinearCompletion.normalizerCompletion L (residual H) E e hgen
    c.middle.range = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
    c.left.range ⊓ c.right.range = c.middle.range ∧
    ∃ u v : G, u ∈ c.left.range ∧ v ∈ c.right.range ∧
      u ∉ c.middle.range ∧ v ∉ c.middle.range ∧ u^2=1 ∧ v^2=1 ∧
      (u*v)^3 ∈ c.middle.range := by
  have hmn := (d.linear_amalgam_blocks h hH.1.1.2 hp F hm hF he).1
  exact ⟨hmn,hmn.symm ▸ h.exponent,
    LinearCompletion.normalizerCompletion_middle L (residual H) E e hgen,
    LinearCompletion.normalizerCompletion_apartment_input L (residual H) E e hgen
      s t hs ht hsout htout hs2 ht2 hcube⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion
variable {G : Type*} [Group G] (L K S : Subgroup G)

/-- Normalizing the original S and both factors normalizes both pure parabolics. -/
theorem normalizes_parabolics
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (i : Fin 2) : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤
      normalizer (ChapterF.Source.parabolic ![L,K] S i : Set G) := by
  let N := normalizer (L : Set G) ⊓ normalizer (K : Set G)
  have hJ (j : Fin 2) : N ≤ normalizer (![L,K] j : Set G) := by
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right
  have hb (j : Fin 2) : N ≤ normalizer (ChapterF.Source.borel (![L,K] j) S : Set G) := by
    have hi := (le_inf hS (hJ j)).trans inf_normalizer_le_normalizer_inf
    exact (le_inf (hJ j) (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf ((le_inf (hJ i) hS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
    (hb (ChapterF.Source.other i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Literal conjugation on both original pure parabolics and their whole intersection. -/
def sourceMiddleAction
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G)) :
    (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
      RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (sourceParabolicAmalgam ![L,K] S) where
  toFun g :=
    { left := (ChapterF.Source.parabolic ![L,K] S 0).normalizerMonoidHom
        (inclusion (normalizes_parabolics L K S hS 0) g)
      middle := (ChapterF.Source.parabolic ![L,K] S 0 ⊓
        ChapterF.Source.parabolic ![L,K] S 1).normalizerMonoidHom
        (inclusion ((le_inf (normalizes_parabolics L K S hS 0)
          (normalizes_parabolics L K S hS 1)).trans inf_normalizer_le_normalizer_inf) g)
      right := (ChapterF.Source.parabolic ![L,K] S 1).normalizerMonoidHom
        (inclusion (normalizes_parabolics L K S hS 1) g)
      left_commutes _ := Subtype.ext rfl
      right_commutes _ := Subtype.ext rfl }
  map_one' := by apply RankTwoAmalgam.Iso.ext <;> ext x <;> simp
  map_mul' a b := by apply RankTwoAmalgam.Iso.ext <;> ext x <;> simp [mul_assoc]

variable {U V Y : Type*} [Group U] [Group V] [Group Y] {β : RankTwoAmalgam U V Y}

/-- Transport the actual common-normalizer action through the same three marked maps. -/
def transportedMiddleAction
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) β) :
    (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
      RankTwoAmalgam.Iso β β :=
  (RankTwoAmalgam.automorphismConjEquiv e).toMonoidHom.comp (sourceMiddleAction L K S hS)

/-- Both endpoint equations and the whole-overlap equation hold pointwise. -/
theorem transportedMiddleAction_equations
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) β)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    (∀ x, (e.left.symm ((transportedMiddleAction L K S hS e g).left x)).val =
      g.val * (e.left.symm x).val * g.val⁻¹) ∧
    (∀ x, (e.middle.symm ((transportedMiddleAction L K S hS e g).middle x)).val =
      g.val * (e.middle.symm x).val * g.val⁻¹) ∧
    (∀ x, (e.right.symm ((transportedMiddleAction L K S hS e g).right x)).val =
      g.val * (e.right.symm x).val * g.val⁻¹) := by
  refine ⟨?_,?_,?_⟩
  · intro x
    change (e.left.symm (e.left _)).val = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  · intro x
    change (e.middle.symm (e.middle _)).val = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  · intro x
    change (e.right.symm (e.right _)).val = _
    rw [MulEquiv.symm_apply_apply]
    rfl

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
open ChapterF.SourceCompletion.LinearThreeEven Matrix.PSL3.SmallCompletion

/-- The actual transported common-normalizer action supplies the native paired
cubic word. This is a relation input to the remaining marked small-cover proof,
not yet an ambient automorphism lift. -/
theorem transportedMiddleAction_paired_cube
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F))
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    let c := (modelCompletion F).pairCompletion
      ((modelCompletion F).comapIso (transportedMiddleAction L K S hS e g))
    (c.left ⟨reflection F false,reflection_mem F false⟩ *
      c.right ⟨reflection F true,reflection_mem F true⟩)^3 = 1 :=
  paired_reflections_cube F hF hn (transportedMiddleAction L K S hS e g)
/-- The same native relation for the transported opposite source orientation. -/
theorem transportedMiddleAction_reverse_cube
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    (((transportedMiddleAction L K S hS e g).left
        ⟨reflection F true,reflection_mem F true⟩).val *
      ((transportedMiddleAction L K S hS e g).right
        ⟨reflection F false,reflection_mem F false⟩).val)^3 = 1 :=
  reverse_reflection_images_cube F hF hn (transportedMiddleAction L K S hS e g)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G] (L K S : Subgroup G)
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual common normalizer acts on the concrete PSL₃ carrier. -/
def nativeMiddleAction
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F))
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* MulAut PSL(3,F) :=
  (nativeLiftHom F hF hn).comp (transportedMiddleAction L K S hS e)

/-- Both original endpoint conjugations and the WHOLE overlap are preserved
by the same global action, through the given compatible comparison. -/
theorem nativeMiddleAction_equations
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F))
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    (∀ x, nativeMiddleAction L K S hS e hF hn g (e.left x).val =
      (e.left ((sourceMiddleAction L K S hS g).left x)).val) ∧
    (∀ b, nativeMiddleAction L K S hS e hF hn g (e.middle b).val =
      (e.middle ((sourceMiddleAction L K S hS g).middle b)).val) ∧
    (∀ y, nativeMiddleAction L K S hS e hF hn g (e.right y).val =
      (e.right ((sourceMiddleAction L K S hS g).right y)).val) := by
  let a := transportedMiddleAction L K S hS e g
  refine ⟨?_,?_,?_⟩
  · intro x
    change nativeLift F hF hn a (e.left x).val = _
    rw [nativeLift_left]
    change (e.left ((sourceMiddleAction L K S hS g).left (e.left.symm (e.left x)))).val = _
    rw [e.left.symm_apply_apply]
  · intro b
    change nativeLift F hF hn a (e.middle b).val = _
    rw [nativeLift_middle]
    change (e.middle ((sourceMiddleAction L K S hS g).middle (e.middle.symm (e.middle b)))).val = _
    rw [e.middle.symm_apply_apply]
  · intro y
    change nativeLift F hF hn a (e.right y).val = _
    rw [nativeLift_right]
    change (e.right ((sourceMiddleAction L K S hS g).right (e.right.symm (e.right y)))).val = _
    rw [e.right.symm_apply_apply]

/-- The opposite source comparison lifts to the same concrete native carrier. -/
def nativeMiddleReverseAction
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* MulAut PSL(3,F) :=
  (nativeReverseLiftHom F hF hn).comp (transportedMiddleAction L K S hS e)

theorem nativeMiddleReverseAction_equations
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    (∀ x, nativeMiddleReverseAction L K S hS e hF hn g (e.left x).val =
      (e.left ((sourceMiddleAction L K S hS g).left x)).val) ∧
    (∀ b, nativeMiddleReverseAction L K S hS e hF hn g (e.middle b).val =
      (e.middle ((sourceMiddleAction L K S hS g).middle b)).val) ∧
    (∀ y, nativeMiddleReverseAction L K S hS e hF hn g (e.right y).val =
      (e.right ((sourceMiddleAction L K S hS g).right y)).val) := by
  let a := transportedMiddleAction L K S hS e g
  refine ⟨?_,?_,?_⟩
  · intro x
    change nativeReverseLiftHom F hF hn a (e.left x).val = _
    rw [nativeReverseLift_left]
    change (e.left ((sourceMiddleAction L K S hS g).left (e.left.symm (e.left x)))).val = _
    rw [e.left.symm_apply_apply]
  · intro b
    change nativeReverseLiftHom F hF hn a (e.middle b).val = _
    rw [nativeReverseLift_middle]
    change (e.middle ((sourceMiddleAction L K S hS g).middle (e.middle.symm (e.middle b)))).val = _
    rw [e.middle.symm_apply_apply]
  · intro y
    change nativeReverseLiftHom F hF hn a (e.right y).val = _
    rw [nativeReverseLift_right]
    change (e.right ((sourceMiddleAction L K S hS g).right (e.right.symm (e.right y)))).val = _
    rw [e.right.symm_apply_apply]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G] [Finite G] (L K : Subgroup G)
variable {F : Type*} [Field F] [Finite F] [CharP F 2] (E : SourceExtension F)

/-- The original full normalizers and the actual source cubic witness determine
full ambient order. Source generation is retained explicitly. -/
theorem normalizerCompletion_card_eq
    (e : NormalizerComparison L K E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (K : Set G) = ⊤)
    {n : ℕ} (hF : Nat.card F=2^n)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (K : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (K : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (K : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G)) :
    Nat.card G = Nat.card E.carrier := by
  obtain ⟨ho,u,v,hu,hv,huout,hvout,hu2,hv2,huv⟩ :=
    normalizerCompletion_apartment_input L K E e hgen s t hs ht hsout htout hs2 ht2 hcube
  exact Completion.card_eq_extension_of_cube_mem_middle
    (normalizerCompletion L K E e hgen) ho hF u v hu hv huout hvout hu2 hv2 huv

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G] (L K S : Subgroup G)
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Extending the actual compatible action preserves its entire kernel. -/
theorem nativeMiddleAction_ker
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F))
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    (nativeMiddleAction L K S hS e hF hn).ker = (sourceMiddleAction L K S hS).ker := by
  change ((nativeLiftHom F hF hn).comp
    ((RankTwoAmalgam.automorphismConjEquiv e).toMonoidHom.comp (sourceMiddleAction L K S hS))).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ (nativeLiftHom_injective F hF hn),
    MonoidHom.ker_comp_of_injective _ _ (RankTwoAmalgam.automorphismConjEquiv e).injective]

theorem nativeMiddleReverseAction_ker
    (hS : normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (S : Set G))
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    (nativeMiddleReverseAction L K S hS e hF hn).ker = (sourceMiddleAction L K S hS).ker := by
  change ((nativeReverseLiftHom F hF hn).comp
    ((RankTwoAmalgam.automorphismConjEquiv e).toMonoidHom.comp (sourceMiddleAction L K S hS))).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ (nativeReverseLiftHom_injective F hF hn),
    MonoidHom.ker_comp_of_injective _ _ (RankTwoAmalgam.automorphismConjEquiv e).injective]

/-- The original ambient full-normalizer coset action has trivial kernel. -/
theorem normalizerCompletion_action_injective (E : SourceExtension F)
    (e : NormalizerComparison L K E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (K : Set G) = ⊤) :
    Function.Injective (MulAction.toPermHom G
      (Completion.Vertex (normalizerCompletion L K E e hgen))) :=
  Completion.vertex_action_injective (normalizerCompletion L K E e hgen)
    (normalizerCompletion_overlap L K E e hgen)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G] [Finite G] (L K : Subgroup G)
variable {F : Type*} [Field F] [Finite F] [CharP F 2] (E : SourceExtension F)

/-- The literal full-normalizer pair recognizes a faithful type-preserving
extension. The source must supply generation and cube membership in its whole
intersection; neither an order bound nor a literal cubic relation is assumed. -/
theorem normalizerCompletion_recognition
    (e : NormalizerComparison L K E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (K : Set G) = ⊤)
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (K : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (K : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (K : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G)) :
    Nat.card G=Nat.card E.carrier ∧
    ∃ a : G →* MulAut PSL(3,F), Function.Injective a ∧
      ChapterF.SourceCompletion.UnitaryNonbinary.inner PSL(3,F) ≤ a.range ∧
      (∀g,ChapterF.SourceCompletion.UnitaryNonbinary.PreservesTypes
        (Matrix.PSL3.LinearThree.pointParabolic F) (Matrix.PSL3.LinearThree.lineParabolic F) (a g)) ∧
      (∀x : E.left,a ((normalizerCompletion L K E e hgen).left x)=x.val) ∧
      (∀y : E.right,a ((normalizerCompletion L K E e hgen).right y)=y.val) := by
  obtain ⟨ho,u,v,hu,hv,huout,hvout,hu2,hv2,huv⟩ :=
    normalizerCompletion_apartment_input L K E e hgen s t hs ht hsout htout hs2 ht2 hcube
  exact Completion.faithful_extension_recognition
    (normalizerCompletion L K E e hgen) ho hF hn u v hu hv huout hvout hu2 hv2 huv

/-- Ambient simplicity identifies the original group with the native carrier. -/
theorem normalizerCompletion_simple_equiv [IsSimpleGroup G]
    (e : NormalizerComparison L K E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (K : Set G) = ⊤)
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (K : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (K : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (K : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G)) :
    Nonempty (G ≃* PSL(3,F)) := by
  obtain ⟨ho,u,v,hu,hv,huout,hvout,hu2,hv2,huv⟩ :=
    normalizerCompletion_apartment_input L K E e hgen s t hs ht hsout htout hs2 ht2 hcube
  exact Completion.simple_recognition
    (normalizerCompletion L K E e hgen) ho hF hn u v hu hv huout hvout hu2 hv2 huv

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.LinearCompletion

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G] [Finite G]

/-- The original prepared row yields PSL₃ at its original exponent, in either
comparison orientation, once its full normalizers and source apartment are supplied. -/
theorem Preparation.linear_full_normalizer_recognition
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (E : SourceExtension F) (e : LinearCompletion.NormalizerComparison L (residual H) E)
    (hgen : normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (residual H : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :
    m=n ∧ 1<m ∧ ClassicalGroup.IsPSL G 3 (2^n) ∧ Nonempty (G ≃* PSL(3,F)) := by
  have hmn := (d.linear_amalgam_blocks h hH.1.1.2 hp F hm hF he).1
  have hm' : 1<m := hmn.symm ▸ h.exponent
  let : IsSimpleGroup G := h.qtke.simple
  have hc := LinearCompletion.normalizerCompletion_simple_equiv L (residual H) E e hgen hF hm'
    s t hs ht hsout htout hs2 ht2 hcube
  exact ⟨hmn,hm',⟨F,inferInstance,inferInstance,hmn ▸ hF,hc⟩,hc⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
