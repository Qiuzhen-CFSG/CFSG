module

public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Defs
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.GroupTheory.AutomorphismSquareRank

/-!
# Factor reduction for the binary determinant-action normalizer

The concrete SL₂(4) is identified with A₅ through its centerless projective
quotient. Its proper subgroups are therefore solvable. A nonsolvable subgroup
of the square has a surjective coordinate projection. If the other projection
is proper, its kernel projects to a nontrivial normal subgroup of SL₂(4), so
the subgroup contains the whole first coordinate factor.

Automorphisms of a centerless quasisimple square preserve or interchange the
two factors. In the preserving case, two surjective projections of a pointwise
fixed subgroup force both automorphisms to be trivial. Conjugation through the
faithful binary matrix action retains the literal factor images and proves the
normalizer reduction consumed by `InvolutionResidual.Preserving`.

Source application: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual

private theorem sl_center : center SL = ⊥ :=
  Subgroup.card_eq_one.mp
    (BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one (CharTwo.neg_eq 1))

private def slProjectiveEquiv : SL ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  ((QuotientGroup.quotientMulEquivOfEq sl_center).trans QuotientGroup.quotientBot).symm

private def slAlternatingEquiv : SL ≃* alternatingGroup (Fin 5) :=
  slProjectiveEquiv.trans (Classical.choice
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (by rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field])))

private theorem sl_proper_solvable (H : Subgroup SL) (hH : H ≠ ⊤) :
    Group.IsSolvable H :=
  alternatingGroup.isSolvable_subgroup_of_equiv_five slAlternatingEquiv H hH

private instance sl_simple : IsSimpleGroup SL := by
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 5))
  exact slAlternatingEquiv.isSimpleGroup

private instance sl_perfect : Group.IsPerfect SL := by
  let := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by
    rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
    decide)
  exact Group.IsPerfect.ofSurjective (f := slProjectiveEquiv.symm.toMonoidHom)
    slProjectiveEquiv.symm.surjective

private instance sl_quasisimple : IsQuasisimple SL :=
  { simple := slProjectiveEquiv.symm.isSimpleGroup }

section Abstract
variable {S T : Type*} [Group S] [Group T] [IsSimpleGroup S]

private theorem left_factor_le (R : Subgroup (S × T))
    (hn : ¬ Group.IsSolvable R)
    (hfst : Function.Surjective ((MonoidHom.fst S T).comp R.subtype))
    (hsnd : Group.IsSolvable ((MonoidHom.snd S T).comp R.subtype).range) :
    (MonoidHom.inl S T).range ≤ R := by
  let p : R →* S := (MonoidHom.fst S T).comp R.subtype
  let q : R →* T := (MonoidHom.snd S T).comp R.subtype
  let N : Subgroup S := q.ker.map p
  let : N.Normal := q.normal_ker.map p hfst
  have hN : N = ⊤ := by
    apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal N inferInstance).resolve_left
    intro hbot
    apply hn
    let : Group.IsSolvable q.range := hsnd
    apply Group.isSolvable_of_isSolvable_injective (f := q.rangeRestrict)
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro r hr
    have hrq : q r = 1 := congrArg Subtype.val hr
    have hrp : p r = 1 := by
      apply mem_bot.mp
      rw [← hbot]
      exact ⟨r, hrq, rfl⟩
    apply Subtype.ext
    exact Prod.ext hrp hrq
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ N := hN ▸ mem_top s
  obtain ⟨r, hrq, hrs⟩ := hs
  have he : (r : S × T) = (s, 1) := Prod.ext hrs hrq
  change (s, 1) ∈ R
  exact he ▸ r.property
end Abstract

private theorem nonsolvable_projections (R : Subgroup G) (hn : ¬ Group.IsSolvable R) :
    ((MonoidHom.fst SL SL).comp R.subtype).range = ⊤ ∨
      ((MonoidHom.snd SL SL).comp R.subtype).range = ⊤ := by
  by_contra! hh
  let p := (MonoidHom.fst SL SL).comp R.subtype
  let q := (MonoidHom.snd SL SL).comp R.subtype
  let : Group.IsSolvable p.range := sl_proper_solvable _ hh.1
  let : Group.IsSolvable q.range := sl_proper_solvable _ hh.2
  apply hn
  apply Group.isSolvable_of_isSolvable_injective
    (f := p.rangeRestrict.prod q.rangeRestrict)
  intro r s h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x => (x.1 : SL)) h) (congrArg (fun x => (x.2 : SL)) h)

private theorem right_factor_le (R : Subgroup G) (hn : ¬ Group.IsSolvable R)
    (hsnd : Function.Surjective ((MonoidHom.snd SL SL).comp R.subtype))
    (hfst : Group.IsSolvable ((MonoidHom.fst SL SL).comp R.subtype).range) :
    (MonoidHom.inr SL SL).range ≤ R := by
  let e : G ≃* G := MulEquiv.prodComm
  let R' := R.map e.toMonoidHom
  have hn' : ¬ Group.IsSolvable R' := by
    intro h
    let : Group.IsSolvable (R.map e.toMonoidHom) := h
    exact hn (Group.isSolvable_of_isSolvable_injective (f := (Subgroup.equivMapOfInjective R e.toMonoidHom e.injective).toMonoidHom)
      (Subgroup.equivMapOfInjective R e.toMonoidHom e.injective).injective)
  have hs' : Function.Surjective ((MonoidHom.fst SL SL).comp R'.subtype) := by
    intro s
    obtain ⟨r, hr⟩ := hsnd s
    exact ⟨e.subgroupMap R r, hr⟩
  have hp' : ((MonoidHom.snd SL SL).comp R'.subtype).range =
      ((MonoidHom.fst SL SL).comp R.subtype).range := by
    ext s
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨x, hx⟩ := (Subgroup.equivMapOfInjective R e.toMonoidHom e.injective).surjective r
      exact ⟨x, congrArg (fun y : R' => (y : G).2) hx⟩
    · rintro ⟨r, rfl⟩
      exact ⟨e.subgroupMap R r, rfl⟩
  have hle := left_factor_le R' hn' hs' (hp' ▸ hfst)
  rintro _ ⟨s, rfl⟩
  obtain ⟨x, hx, he⟩ := hle ⟨s, rfl⟩
  have he' : x = (1, s) := Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  change (1, s) ∈ R
  exact he' ▸ hx

/-- A pointwise fixed nonsolvable subgroup either contains a coordinate factor,
or forces the preserving automorphism of the square to be the identity. -/
private theorem preserving_automorphism_reduction (a b : MulAut SL) (R : Subgroup G)
    (hn : ¬ Group.IsSolvable R) (hf : ∀ r : R, (a.prodCongr b) (r : G) = (r : G)) :
    (a = 1 ∧ b = 1) ∨ (MonoidHom.inl SL SL).range ≤ R ∨
      (MonoidHom.inr SL SL).range ≤ R := by
  let p := (MonoidHom.fst SL SL).comp R.subtype
  let q := (MonoidHom.snd SL SL).comp R.subtype
  have ha (hp : p.range = ⊤) : a = 1 := by
    apply MulEquiv.ext
    intro s
    obtain ⟨r, rfl⟩ := MonoidHom.range_eq_top.mp hp s
    exact congrArg Prod.fst (hf r)
  have hb (hq : q.range = ⊤) : b = 1 := by
    apply MulEquiv.ext
    intro s
    obtain ⟨r, rfl⟩ := MonoidHom.range_eq_top.mp hq s
    exact congrArg Prod.snd (hf r)
  rcases nonsolvable_projections R hn with hp | hq
  · by_cases hq : q.range = ⊤
    · exact Or.inl ⟨ha hp, hb hq⟩
    · exact Or.inr (Or.inl (left_factor_le R hn (MonoidHom.range_eq_top.mp hp)
        (sl_proper_solvable _ hq)))
  · by_cases hp : p.range = ⊤
    · exact Or.inl ⟨ha hp, hb hq⟩
    · exact Or.inr (Or.inr (right_factor_le R hn (MonoidHom.range_eq_top.mp hq)
        (sl_proper_solvable _ hp)))

/-- Conjugation by a binary normalizer either interchanges the two factors,
centralizes the whole image, or its pointwise fixed nonsolvable subgroup
contains a full coordinate factor. -/
theorem normalizer_factor_reduction (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (R : Subgroup G) (hn : ¬ Group.IsSolvable R)
    (hc : ∀ r : R, Commute t (linearAction (r : G))) :
    SwapsFactors t ∨ (∀ g : G, Commute t (linearAction g)) ∨
      (MonoidHom.inl SL SL).range ≤ R ∨ (MonoidHom.inr SL SL).range ≤ R := by
  have hi : Function.Injective linearAction := by
    intro g h he
    exact action_injective (congrArg LinearEquiv.toLinearMap he)
  let e : G ≃* linearAction.range := MonoidHom.ofInjective hi
  let a : MulAut G := MulAut.congr e.symm (linearAction.range.normalizerMonoidHom ⟨t, ht⟩)
  have ha (g : G) : linearAction (a g) = t * linearAction g * t⁻¹ := by
    change (e (e.symm _)).val = _
    rw [e.apply_symm_apply]
    rfl
  have hr (r : R) : a (r : G) = (r : G) := by
    apply hi
    rw [ha]
    exact (hc r).mul_inv_cancel
  rcases Theory.GroupTheory.AutomorphismSquare.normal_form sl_center a with
    ⟨b, c, he⟩ | ⟨b, c, he⟩
  · rcases preserving_automorphism_reduction b c R hn (fun r => he ▸ hr r) with
      ⟨hb, hc⟩ | hR
    · right; left
      intro g
      have hag : a g = g := by rw [he, hb, hc]; rfl
      have hh := ha g
      rw [hag] at hh
      exact (eq_mul_inv_iff_mul_eq.mp hh).symm
    · exact Or.inr (Or.inr hR)
  · left
    constructor
    · apply le_antisymm
      · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
        refine ⟨c s, ?_⟩
        change linearAction (1, c s) = t * linearAction (s, 1) * t⁻¹
        rw [← ha]
        simp [he, MulEquiv.prodCongr]
      · rintro _ ⟨s, rfl⟩
        refine ⟨linearAction (c.symm s, 1), ⟨c.symm s, rfl⟩, ?_⟩
        change t * linearAction (c.symm s, 1) * t⁻¹ = linearAction (1, s)
        rw [← ha]
        simp [he, MulEquiv.prodCongr]
    · apply le_antisymm
      · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
        refine ⟨b s, ?_⟩
        change linearAction (b s, 1) = t * linearAction (1, s) * t⁻¹
        rw [← ha]
        simp [he, MulEquiv.prodCongr]
      · rintro _ ⟨s, rfl⟩
        refine ⟨linearAction (1, b.symm s), ⟨b.symm s, rfl⟩, ?_⟩
        change t * linearAction (1, b.symm s) * t⁻¹ = linearAction (s, 1)
        rw [← ha]
        simp [he, MulEquiv.prodCongr]

end ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual
