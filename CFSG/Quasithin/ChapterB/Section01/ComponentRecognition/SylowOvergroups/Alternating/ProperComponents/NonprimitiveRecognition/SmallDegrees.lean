module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.Definitions
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion

/-!
# Initial degrees and the whole alternating group

A component of Aₘ for m ≥ 5 is the whole group. Below degree five the
symmetric group is solvable, and every proper subgroup of A₅ is solvable.
These facts supply the base cases of degree induction without extra
recognition hypotheses.

Source: the elementary alternating-group facts used in the overgroup
argument of Aschbacher–Smith B.1.13, printed p.74 (PDF p.85).
-/

public section
open Subgroup MulAction Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

private theorem component_alternating_equiv {m : ℕ} (hm : 5 ≤ m)
    (D : Subgroup (alternatingGroup (Fin m))) (hD : IsComponent _ D) :
    Nonempty (D ≃* alternatingGroup (Fin m)) := by
  let : IsQuasisimple (alternatingGroup (Fin m)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simpa using hm)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin m)) :=
        alternatingGroup.isSimpleGroup (by simpa using hm)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ m by omega)))).trans
          QuotientGroup.quotientBot).isSimpleGroup }
  have ht : IsComponent (alternatingGroup (Fin m)) ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩
  exact ⟨(MulEquiv.subgroupCongr (hD.eq_of_le ht le_top)).trans topEquiv⟩

theorem alternating_top_component_models {m : ℕ} (hm : 5 ≤ m)
    (D : Subgroup (⊤ : Subgroup (alternatingGroup (Fin m)))) (hD : IsComponent _ D) :
    AlternatingSubgroupModels m D := by
  let e : (⊤ : Subgroup (alternatingGroup (Fin m))) ≃* alternatingGroup (Fin m) := topEquiv
  obtain ⟨d⟩ := component_alternating_equiv hm _ (hD.map_equiv e)
  exact Or.inl ⟨m, by omega, le_rfl,
    ⟨(Subgroup.equivMapOfInjective D e.toMonoidHom e.injective).trans d⟩⟩

theorem alternating_all_sylow_component_models_small {m : ℕ} (hm : m ≤ 5) :
    AlternatingAllSylowComponentModels m := by
  intro S X hS D hD
  by_cases hm5 : m = 5
  · subst m
    by_cases hX : X = ⊤
    · subst X
      exact alternating_top_component_models (by omega) D hD
    · let : Group.IsSolvable X := alternatingGroup.isSolvable_subgroup_five_of_ne_top X hX
      exact (not_isComponent_of_solvable D hD).elim
  · have hm4 : m ≤ 4 := by omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin m) ≤ Fintype.card (Fin 4) by simpa using hm4)
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin m)) :=
      Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
    exact (not_isComponent_of_solvable D hD).elim


/-- Actual model isomorphisms transport the stated ambient degree unchanged. -/
theorem AlternatingSubgroupModels.of_mulEquiv {m : ℕ} {A B : Type*}
    [Group A] [Group B] (h : AlternatingSubgroupModels m B) (e : A ≃* B) :
    AlternatingSubgroupModels m A := by
  rcases h with ⟨n, hn, hnm, ⟨d⟩⟩ | ⟨hm, ⟨d⟩⟩
  · exact Or.inl ⟨n, hn, hnm, ⟨e.trans d⟩⟩
  · exact Or.inr ⟨hm, ⟨e.trans d⟩⟩

private theorem center_eq_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center B = ⊥) : center A = ⊥ := by
  apply bot_unique
  intro a ha
  have hb := (Subgroup.centerCongr e ⟨a, ha⟩).property
  have he : e a = 1 := mem_bot.mp (h ▸ hb)
  exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))

/-- Every nontrivial perfect group with one of the actual source models is
centerless. Perfectness excludes the abelian degree-three alternative. -/
theorem alternating_models_center_eq_bot {m : ℕ} {G : Type*} [Group G]
    [Nontrivial G] [Group.IsPerfect G] (h : AlternatingSubgroupModels m G) :
    center G = ⊥ := by
  rcases h with ⟨n, hn, _, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
  · by_cases hn4 : 4 ≤ n
    · exact center_eq_bot_of_equiv e (alternatingGroup.center_eq_bot (by simpa using hn4))
    · have hn3 : n = 3 := by omega
      subst n
      obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le
        (show Fintype.card (Fin 3) ≤ Fintype.card (Fin 4) by decide)
      let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
      let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
        Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective j)
      have hsol : Group.IsSolvable G :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      exact (Group.IsPerfect.not_isSolvable G hsol).elim
  · exact center_eq_bot_of_equiv (e.trans Matrix.PSL3Two.equiv.symm)
      Matrix.PSL3Two.center_eq_bot

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
