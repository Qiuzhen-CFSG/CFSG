module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The linear-four specialization of the complete G.6.4

For an actor isomorphic to the actual binary linear group in dimension four,
G.6.4's exchanged-factor alternative is impossible: a nonidentity element
normally generates this simple group, while the two commuting factors
normalize one another. In the single-factor alternative the group orders
select exactly the natural four-dimensional linear model. The resulting
marking includes both an actor isomorphism and an intertwining linear map;
a dimension or a group-family label is not substituted for that marking.

For an irreducible faithful action, nontrivial displacement generates the
whole module. A displacement bound of one therefore constructs the rank
and generation hypotheses needed by the full known-simple G.6.4 theorem.
`SourceApplication` applies this to actual sections of H_C/V_H through the
canonical two-core quotient, retaining the original conjugation action.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), G.6.4, printed pp.345–346, and the last paragraph
of the proof of 13.8.28, printed p.966.
-/

public section
open Subgroup Representation.BinaryOffender
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open ChapterG.Section06
universe u v
variable {A : Type u} [Group A] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {a : A}

private theorem linear_card (n : ℕ) :
    Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

private theorem no_two_factors (d : TwoFactors ρ a)
    (hgen : normalClosure ({a} : Set A) = ⊤) : False := by
  have hn : d.first ⊔ d.second ≤ normalizer (d.first : Set A) := by
    apply sup_le d.first.le_normalizer
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [d.commute]
    exact bot_le
  rw [d.join_eq, hgen] at hn
  obtain ⟨t, _, _, _, ht⟩ := d.extension
  have he : d.first = d.second :=
    (mem_normalizer_iff_map_conj_eq.mp (hn (mem_top t))).symm.trans ht
  apply d.second_nontrivial
  simpa only [he, inf_idem] using d.disjoint

private theorem factor_four_of_card (hcard : Nat.card A = 20160)
    (h : FactorModel ρ ⊤ ⊤) : HasModelOn ρ ⊤ ⊤ (binaryLinearAction 4) := by
  rcases h with ⟨n, hn, hn5, hm⟩ | ⟨n, hn, hn8, hm⟩ | ⟨n, hn, hm⟩
  · have hc : Nat.card (LinearGroup n) = 20160 :=
      (Nat.card_congr hm.choose.toEquiv).symm.trans
        ((Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv).trans hcard)
    rw [linear_card] at hc
    have he : n = 4 := by
      interval_cases n
      all_goals norm_num [Fin.prod_univ_succ] at hc
      rfl
    exact he ▸ hm
  · have hc : Nat.card (Equiv.Perm (Fin n)) = 20160 :=
      (Nat.card_congr hm.choose.toEquiv).symm.trans
        ((Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv).trans hcard)
    simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hc
    interval_cases n <;> norm_num at hc
  · have hc : Nat.card (Equiv.Perm (Fin n)) = 20160 :=
      (Nat.card_congr hm.choose.toEquiv).symm.trans
        ((Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv).trans hcard)
    simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hc
    rcases hn with rfl | rfl <;> norm_num at hc

/-- The actual L₄(2) actor selects the marked natural four-space from G.6.4. -/
theorem linearFour_model_of_rank_one
    {Cover : Type u} [Group Cover] {q : Cover →* A}
    (h : Hypotheses KnownSimple.IsKnownSimple ρ a q)
    (e : A ≃* LinearGroup 4)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    HasModelOn ρ ⊤ ⊤ (binaryLinearAction 4) := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 4 (by decide)
  let : IsSimpleGroup A := (e.trans (projectiveEquivLinear (by decide : 0 < 4)).symm).isSimpleGroup
  have hgen : normalClosure ({a} : Set A) = ⊤ := by
    apply (inferInstance : (normalClosure ({a} : Set A)).Normal).eq_bot_or_eq_top.resolve_left
    intro he
    have ha : a ∈ normalClosure ({a} : Set A) := subset_normalClosure (Set.mem_singleton a)
    rw [he] at ha
    exact h.nonidentity ha
  have hc : Nat.card A = 20160 := by
    rw [Nat.card_congr e.toEquiv, linear_card]
    norm_num [Fin.prod_univ_succ]
  rcases (ChapterG.Section06.lemma_G_6_4 h hrank).1 with ho | ho
  · obtain ⟨_, hm, hw⟩ := ho
    rw [hw] at hm
    exact factor_four_of_card hc hm
  · obtain ⟨ht⟩ := ho
    exact (no_two_factors ht hgen).elim

private theorem irreducible_displacement_generated
    [Representation.IsIrreducible ρ] (hf : Function.Injective ρ) (ha : a ≠ 1) :
    conjugateDisplacementSpan ρ a ⊤ = ⊤ := by
  let S : Subrepresentation ρ := {
    toSubmodule := conjugateDisplacementSpan ρ a ⊤
    apply_mem_toSubmodule := by
      intro g v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨b, _, w, rfl⟩ := hv
        exact Submodule.subset_span ⟨g * b, mem_top _, w, by rw [map_mul, Module.End.mul_apply]⟩
      | zero => simp
      | add v w _ _ hv hw =>
        simpa only [map_add] using (conjugateDisplacementSpan ρ a ⊤).add_mem hv hw
      | smul c v _ hv =>
        simpa only [map_smul] using (conjugateDisplacementSpan ρ a ⊤).smul_mem c hv }
  rcases eq_bot_or_eq_top S with hs | hs
  · exfalso
    apply ha
    apply hf
    rw [map_one]
    ext v
    apply sub_eq_zero.mp
    have hv : ρ a v - v ∈ S.toSubmodule :=
      Submodule.subset_span ⟨1, mem_top _, v, by simp⟩
    rw [hs] at hv
    exact hv
  · exact congrArg Subrepresentation.toSubmodule hs

/-- On an irreducible faithful action of the actual binary linear-four group,
small nontrivial displacement supplies all the module hypotheses of G.6.4. -/
theorem irreducible_linearFour_model
    [Finite W] [Representation.IsIrreducible ρ]
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* A) (hq : Function.Surjective q)
    (hcover : IsSQTK KnownSimple.IsKnownSimple Cover)
    (hcore : pCore 2 A = ⊥) (hf : Function.Injective ρ)
    (e : A ≃* LinearGroup 4) (ha2 : a ^ 2 = 1) (ha : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1) :
    HasModelOn ρ ⊤ ⊤ (binaryLinearAction 4) := by
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 := by
    have hn : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≠ 0 := by
      intro hz
      have he := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
      apply ha
      apply hf
      rw [map_one]
      exact sub_eq_zero.mp he
    omega
  apply linearFour_model_of_rank_one (q := q) ?_ e hrank
  exact {
    finite_group := Finite.of_surjective q hq
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := hcover
    quotient_surjective := hq
    twoCore := hcore
    faithful := hf
    involution := ha2
    nonidentity := ha
    displacement_rank := hr.trans (by decide)
    generated := irreducible_displacement_generated hf ha }

end CFSG.Quasithin.Chapter13.Section08.LinearFour
