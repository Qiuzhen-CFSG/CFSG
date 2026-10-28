module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Contracts
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank

/-!
# Lifting the A₆ actor generation bound to the ambient group

Self-centralization of F*(G), together with the trivial center of A₆, makes
conjugation on L faithful. Transport through the given isomorphism L ≃ A₆
therefore preserves elementary actors and their ranks. Every inner conjugator
lifts explicitly to an element of L, and injectivity reflects the generated
subgroup containment.

The checked Sylow model gives rank at most three for every elementary actor
in Aut(A₆), and at most two for an actor outside the natural S₆. Choosing one
outside involution reduces that whole branch to three-conjugate generation.
The two concrete finite calculations in `Contracts` remain explicit inputs.

Source: Aschbacher–Smith K.1.1, printed p.452 (PDF p.463), citing GM02
Theorem 6.2/Table 6.3; the generalized Fitting centralizer theorem supplies
the faithful action. No representation hypothesis is used in the lift.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open AlternatingSix.ShadowLocal

namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual generalized Fitting A₆ has trivial relative centralizer. -/
theorem centralizer_eq_bot (L : Subgroup G) (hL : L = generalizedFitting G)
    (e : L ≃* A6) : centralizer (L : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxL : x ∈ L := by
    rw [hL]
    exact centralizer_generalizedFitting_le G (by simpa only [hL] using hx)
  have hz : e ⟨x, hxL⟩ ∈ center A6 := by
    rw [mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hx z z.property)
  rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6)), mem_bot] at hz
  have he : (⟨x, hxL⟩ : L) = 1 := e.injective (hz.trans (map_one e).symm)
  exact congrArg Subtype.val he

/-- Conjugation on the given component, in the supplied A₆ coordinates. -/
noncomputable def ambientAction (L : Subgroup G) [L.Normal] (e : L ≃* A6) :
    G →* AutA6 := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

/-- Self-centralization makes the ambient action faithful. -/
theorem ambientAction_injective (L : Subgroup G) [L.Normal]
    (hL : L = generalizedFitting G) (e : L ≃* A6) :
    Function.Injective (ambientAction L e) :=
  (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L (centralizer_eq_bot L hL e))

omit [Finite G] in
/-- On L, the action is exactly the inner action through e. -/
theorem ambientAction_on_component (L : Subgroup G) [L.Normal] (e : L ≃* A6)
    (x : L) : ambientAction L e x = MulAut.conj (e x) := by
  change MulAut.congr e (MulAut.conjNormal (x : G)) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

/-- Inner conjugators lift to L and give the full ambient generation contract. -/
theorem actorGeneration_of_inner_budget
    (hbudget : ElementaryInnerConjugateBudget A6 6) : ActorGeneration.{u} := by
  intro G _ _ L hL e A hA
  let : L.Normal := hL ▸ inferInstance
  let f := ambientAction L e
  have hf : Function.Injective f := ambientAction_injective L hL e
  let B := A.map f
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo B := by
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hb
    apply hA.1
    apply Subgroup.map_injective hf
    simpa only [Subgroup.map_bot] using hb
  have hr : rank B = rank A := by
    unfold rank
    exact congrArg (Nat.log 2) (Subgroup.card_map_of_injective hf)
  obtain ⟨n, c, hn, hc⟩ := hbudget B hB
  let d : Fin n → G := fun i => (e.symm (c i) : G)
  have hd (i : Fin n) : f (d i) = MulAut.conj (c i) := by
    change ambientAction L e (e.symm (c i)) = _
    rw [ambientAction_on_component, e.apply_symm_apply]
  refine ⟨n, d, by simpa only [hr] using hn, ?_⟩
  apply (Subgroup.map_le_map_iff_of_injective hf).mp
  rw [Subgroup.map_iSup]
  have hmap (i : Fin n) :
      (A.map (MulAut.conj (d i)).toMonoidHom).map f =
        B.map (MulAut.conj (MulAut.conj (c i))).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    change f (d i * a * (d i)⁻¹) =
      MulAut.conj (c i) * f a * (MulAut.conj (c i))⁻¹
    rw [map_mul, map_mul, map_inv, hd]
  simp_rw [hmap]
  apply le_trans _ hc
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨e ⟨l, hl⟩, (ambientAction_on_component L e ⟨l, hl⟩).symm⟩

/-- The actual automorphism group has elementary two-rank at most three. -/
theorem rank_le_three (A : Subgroup AutA6) (hA : IsElementaryTwo A) :
    rank A ≤ 3 := by
  let : IsElementaryAbelian 2 A := hA.2
  have h := Nat.log_mono_right (b := 2) (elementary_card_le_eight A)
  exact h.trans (by decide : Nat.log 2 8 ≤ 3)

/-- Every elementary actor outside the natural permutation group has rank at most two. -/
theorem rank_le_two_of_not_le_natural (A : Subgroup AutA6) (hA : IsElementaryTwo A)
    (hn : ¬ A ≤ natural) : rank A ≤ 2 := by
  let : IsElementaryAbelian 2 A := hA.2
  have hc : Nat.card A ≤ 7 := by
    have h := mt (elementary_le_natural_of_eight_le A) hn
    omega
  exact (Nat.log_mono_right hc).trans (by decide : Nat.log 2 7 ≤ 2)

/-- Three conjugates of an outside involution give the budget for the entire actor. -/
theorem exceptional_actor_generation (hgen : ExceptionalInvolutionGeneration)
    (A : Subgroup AutA6) (hA : IsElementaryTwo A) (hn : ¬ A ≤ natural) :
    ∃ c : Fin 3 → A6, 3 * rank A ≤ 6 ∧
      AlternatingSix.ShadowLocal.inner ≤ ⨆ i, A.map (MulAut.conj (MulAut.conj (c i))).toMonoidHom := by
  classical
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ A, t ∉ natural := Set.not_subset.mp hn
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨c, hc⟩ := hgen t (elemPow_eq_one_of_isElementaryAbelian t ht) htn
  refine ⟨c, by have := rank_le_two_of_not_le_natural A hA hn; omega, hc.trans ?_⟩
  apply iSup_mono
  intro i
  apply zpowers_le.mpr
  exact mem_map_of_mem (MulAut.conj (MulAut.conj (c i))).toMonoidHom ht

/-- The natural and exceptional calculations exhaust all elementary actors. -/
theorem inner_budget_of_cases (hnatural : NaturalGeneration)
    (hexceptional : ExceptionalInvolutionGeneration) : ElementaryInnerConjugateBudget A6 6 := by
  classical
  intro A hA
  by_cases hn : A ≤ natural
  · exact hnatural A hA hn
  · obtain ⟨c, hc, hgen⟩ := exceptional_actor_generation hexceptional A hA hn
    exact ⟨3, c, hc, hgen⟩

end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof
