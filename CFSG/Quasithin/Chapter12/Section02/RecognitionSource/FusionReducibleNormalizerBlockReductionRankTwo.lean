module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerModelBounds
public import Theory.Representation.BinaryPermutation.SixCoreSylowFixed

/-!
# The two reducible rank-two block branches

The actual A₆ augmentation core has a fixed line and at most four Sylow-fixed
vectors. Transfer these bounds through L/C_L(V), keeping that quotient
separate from L/O₂(L). The chosen-module normalizer theorem excludes escape.
The genuine G₂ Weyl action gives the same conclusion through its literal
natural quotient. Both retained intrinsic block-construction contracts
therefore follow by contradiction from their escaping hypothesis.

Source: Aschbacher–Smith 3.3.24–25 and 12.2.16, pp.599–600,800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource BinaryPermutation
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Fixed-space cardinalities transport through the actual faithful-action quotient. -/
theorem chosen_sylow_fixed_card_le_of_faithful_model
    (D : ChosenModule T L V)
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {σ : Representation (ZMod 2) A W}
    (e : letI := D.actionCentralizer_normal; ActionEquiv D.faithfulAction σ)
    {b : ℕ} (hb : ∀ P : Sylow 2 A, Nat.card (fixedSpace σ (P : Subgroup A)) ≤ b) :
    Nat.card (V ⊓ centralizer (T : Set G) : Subgroup G) ≤ b := by
  let := D.actionCentralizer_normal
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  obtain ⟨R,hR⟩ := (T.subtype le_sup_right).exists_subgroupOf_eq_of_normal X
  let eL : X ≃* L := subgroupOfEquivOfLe (le_sup_left : L ≤ H)
  let P := R.mapSurjective (f := eL.toMonoidHom) eL.surjective
  have hP : ∀ l ∈ (P : Subgroup L), (l : G) ∈ (T : Subgroup G) := by
    rintro l ⟨r,hr,rfl⟩
    rw [hR] at hr
    exact hr
  let q : L →* A := e.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L))
  have hq : Function.Surjective q := e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let S := P.mapSurjective hq
  let coord (v : V) : D.space := (D.spaceEquiv.symm v).toAdd
  have hcoord (v : V) : ((coord v).val.toMul.val : G) = v :=
    (D.spaceEquiv_apply (coord v)).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
  let f : (V ⊓ centralizer (T : Set G) : Subgroup G) → fixedSpace σ (S : Subgroup A) :=
    fun v => ⟨e.linearEquiv (coord ⟨v,v.property.1⟩), by
      intro a
      obtain ⟨l,hl,he⟩ := a.property
      have hc : D.chosenAction l (coord ⟨v,v.property.1⟩) = coord ⟨v,v.property.1⟩ := by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Subtype.ext
        change (l:G) * ((coord ⟨v,v.property.1⟩).val.toMul.val : G) * (l:G)⁻¹ =
          ((coord ⟨v,v.property.1⟩).val.toMul.val : G)
        rw [hcoord]
        exact mul_inv_eq_iff_eq_mul.mpr (v.property.2 l (hP l hl))
      have hh : σ (q l) (e.linearEquiv (coord ⟨v,v.property.1⟩)) =
          e.linearEquiv (coord ⟨v,v.property.1⟩) :=
        (e.intertwines (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l)
          (coord ⟨v,v.property.1⟩)).symm.trans (congrArg e.linearEquiv hc)
      exact (congrArg (fun b : A => σ b (e.linearEquiv (coord ⟨v,v.property.1⟩)))
        he.symm).trans hh⟩
  have hf : Function.Injective f := by
    intro v w hh
    have he := e.linearEquiv.injective (congrArg Subtype.val hh)
    have he' := congrArg (fun x : D.space => (x.val.toMul.val : G)) he
    rw [hcoord,hcoord] at he'
    exact Subtype.ext he'
  exact (Nat.card_le_card_of_injective f hf).trans (hb S)

/-- The faithful six-letter core marking gives the original fixed line. -/
theorem six_core_fixed_card_eq_two (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (alternatingCoreRepresentation (Fin 6))) :
    Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) = 2 := by
  let := D.actionCentralizer_normal
  let f : G2WeylModel.Fixed D → ZMod 2 := fun v => (e.linearEquiv v.val).val 0
  have hconstant (v : G2WeylModel.Fixed D) :
      e.linearEquiv v.val = 0 ∨ e.linearEquiv v.val = sixCoreConstant := by
    apply (sixCore_fixed_iff _).mp
    intro a
    obtain ⟨q,rfl⟩ := e.groupEquiv.surjective a
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective ((centralizer (V : Set G)).subgroupOf L) q
    rw [←e.intertwines]
    apply congrArg e.linearEquiv
    exact Subtype.ext (v.property ((subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l))
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    apply e.linearEquiv.injective
    have he' : (e.linearEquiv v.val).val 0 = (e.linearEquiv w.val).val 0 := he
    rcases hconstant v with hv | hv <;> rcases hconstant w with hw | hw
    · exact hv.trans hw.symm
    · rw [hv,hw] at he'
      exact (zero_ne_one (show (0 : ZMod 2) = 1 from he')).elim
    · rw [hv,hw] at he'
      exact (one_ne_zero (show (1 : ZMod 2) = 0 from he')).elim
    · exact hv.trans hw.symm
  have hup : Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) ≤ 2 := by
    rw [← Nat.card_congr (ChosenCover.fixedEquiv D)]
    simpa only [Nat.card_zmod] using Nat.card_le_card_of_injective f hf
  have hlo : 1 < Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) := by
    by_contra hn
    have hs := Finite.card_le_one_iff_subsingleton.mp (Nat.le_of_not_gt hn)
    apply hne
    apply bot_unique
    intro x hx
    exact congrArg Subtype.val (@Subsingleton.elim _ hs ⟨x,hx⟩ 1)
  omega

/-- The genuine A₆ augmentation core rules out Sylow-normalizer escape. -/
theorem sylow_normalizer_le_of_alternatingSix_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (alternatingCoreRepresentation (Fin 6))) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_chosen_fixed_bounds h D structural hnone
    (six_core_fixed_card_eq_two D hne e)
    (chosen_sylow_fixed_card_le_of_faithful_model D e SixCoreSylow.card_fixed_le_four)

/-- The complete retained A₆ block-construction contract, on its faithful actor. -/
theorem alternatingSixBlockConstruction : AlternatingSixBlockConstruction T L V := by
  intro h D structural hnone hne hescape e
  exact (hescape (sylow_normalizer_le_of_alternatingSix_core h D structural hnone hne e)).elim

/-- The complete retained G₂ block-construction contract, on L/O₂(L). -/
theorem g2BlockConstruction : G2BlockConstruction T L V := by
  intro h D structural hnone hne hescape e
  exact (hescape (sylow_normalizer_le_of_g2_weyl_model h D structural hnone hne e)).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
