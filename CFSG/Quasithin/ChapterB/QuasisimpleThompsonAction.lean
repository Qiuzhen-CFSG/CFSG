module
public import CFSG.Quasithin.ChapterB.AdequateThompsonFactorization
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Quasisimple actors from Thompson movement

Adequate Thompson factorization forces the actual component image to be
quasisimple whenever the Thompson subgroup moves the reduced module.
A centralizing Thompson image would be a normal two-subgroup, so the
quasisimple commutator dichotomy gives the full component as commutator.
A maximum elementary subgroup then witnesses an FF action on the literal
centralizer quotient, without changing the original component or kernel.
Source: Aschbacher–Smith10.2.9, printed p.751, using B.2.5 and B.5.6.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.InternalThompsonAction
universe u
variable {H : Type u} [Group H] [Finite H]

/-- Nontrivial Thompson movement forces the actual normal component image
to be quasisimple, by the complete adequate factorization alternatives. -/
theorem quasisimple_of_thompson_movement {𝒦 : GroupClass.{u}}
    (classification : SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (hH : IsSQTK 𝒦 H) (P : Sylow 2 H) (K W : Subgroup H)
    [K.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    (hK : K.IsCComponent) (hKP : K ⊔ (P : Subgroup H) = ⊤)
    (hcore : pCore 2 (ActionQuotient W) = ⊥)
    (hmove : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H)) :
    IsQuasisimple (K.map (actionMk W)) := by
  by_contra hnq
  exact hmove (AdequateThompsonFactorization.thompson_factorization
    classification hH P K W hK hKP hcore hnq).1

omit [Finite H] in
/-- The actual nonzero Thompson image has full commutator with the normal
quasisimple actor. A zero commutator would make it a normal two-subgroup. -/
theorem commutator_thompson_eq (P : Sylow 2 H) (K W : Subgroup H)
    [K.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    (hKP : K ⊔ (P : Subgroup H) = ⊤)
    (hcore : pCore 2 (ActionQuotient W) = ⊥)
    [IsQuasisimple (K.map (actionMk W))]
    (hmove : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H)) :
    ⁅K.map (actionMk W), (elementaryAbelianMaxJ (P : Subgroup H)).map (actionMk W)⁆ =
      K.map (actionMk W) := by
  let q := actionMk W
  let B := K.map q
  let R := elementaryAbelianMaxJ (P : Subgroup H)
  let E := R.map q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : B.Normal := (inferInstance : K.Normal).map q hq
  have hgen : B ⊔ (P : Subgroup H).map q = ⊤ := by
    rw [←Subgroup.map_sup,hKP,map_top_of_surjective _ hq]
  have hne : ⁅B,E⁆ ≠ ⊥ := by
    intro hz
    have hBC : B ≤ centralizer (E : Set (ActionQuotient W)) :=
      commutator_eq_bot_iff_le_centralizer.mp hz
    have hPR : (P : Subgroup H) ≤ normalizer (R : Set H) :=
      (P : Subgroup H).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
    have hPE : (P : Subgroup H).map q ≤ normalizer (E : Set (ActionQuotient W)) :=
      (map_mono hPR).trans (le_normalizer_map q)
    have hEN : E.Normal := normalizer_eq_top_iff.mp (top_unique (by
      rw [←hgen]
      exact sup_le (hBC.trans (Subgroup.centralizer_le_normalizer _)) hPE))
    have hER : IsPGroup 2 E :=
      (P.isPGroup'.to_le (show R ≤ (P : Subgroup H) from sSup_le fun _ hA => hA.1)).map q
    have hbot : E = ⊥ := eq_bot_iff.mpr (hcore ▸ (show E ≤ pCore 2 (ActionQuotient W) from
      le_sSup ⟨hEN,hER⟩))
    apply hmove
    simpa only [q, actionMk, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hbot
  have hB : IsComponent (ActionQuotient W) B :=
    ⟨(inferInstance : B.Normal).isSubnormal, inferInstance⟩
  rcases hB.commutator_dichotomy E with hb | he
  · exact (hne hb).elim
  · exact le_antisymm (commutator_le_left B E)
      ((le_iSup_conjugates B E).trans he.symm.le)

/-- A maximum elementary subgroup witnessing Thompson movement gives a
best offender on the faithful literal centralizer quotient action. -/
theorem isFFModule_of_thompson_movement (P : Sylow 2 H) (W : Subgroup H)
    [W.Normal] [IsElementaryAbelian 2 W]
    (hmove : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H)) :
    IsFFModule (V := Additive W) (action W) := by
  by_contra hff
  apply hmove
  apply sSup_le
  intro A hA
  have hz : A.map (actionMk W) = ⊥ := by
    by_contra hn
    apply hff
    apply (isFFModule_iff_exists_bestOffender (action W)).mpr
    exact ⟨_, NormalElementaryQuotient.maxElementary_isBestOffender W
      (actionMk W) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (P : Subgroup H) A ((IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal P) hA hn⟩
  simpa only [actionMk, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
/-- The quasisimple component belongs to the actual offender actor used by
B.5. The proof retains the full quotient representation. -/
theorem component_le_offenderSubgroup (P : Sylow 2 H) (K W : Subgroup H)
    [K.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    (hKP : K ⊔ (P : Subgroup H) = ⊤)
    (hcore : pCore 2 (ActionQuotient W) = ⊥)
    [IsQuasisimple (K.map (actionMk W))]
    (hmove : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H)) :
    K.map (actionMk W) ≤ offenderSubgroup (action W) := by
  let : (offenderSubgroup (action W)).Normal := offenderSubgroup_normal _
  rw [←commutator_thompson_eq P K W hKP hcore hmove]
  exact (commutator_mono le_rfl (thompson_image_le P W)).trans (commutator_le_right _ _)

end CFSG.Quasithin.ChapterB.InternalThompsonAction
