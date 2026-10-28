module

public import Theory.Representation.BinaryOffender.RankOneNormalClosureSections
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.InitialReduction
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The original moved space and its faithful action section

Rank one makes every ambient invariant subspace either fixed by the normal
closure or equal to the whole module. For the moved space of a nontrivial
perfect normal subgroup, the first alternative contradicts perfectness and
faithfulness. Hence in the quasisimple branch the actual B.5.1 moved space is
all of V, without any fixed-space splitting assumption.

The original cyclic offender and full offender generation also pass to the
literal subquotient action. Thus its B.4 actor is the whole normal closure;
no abstract model, quotient reconstruction, or new classification input is used.
Source: Aschbacher–Smith, G.6.2–4, pp.345–346, and B.5.1(1).
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.rank_one_invariant_fixed_or_top
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (U : Submodule (ZMod 2) V) (hU : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ U) :
    subspaceCommutator ρ U (normalClosure ({a} : Set G)) = ⊥ ∨ U = ⊤ := by
  let := h.finite_module
  by_cases hm : U.map (ρ a - LinearMap.id) = ⊥
  · left
    rw [← conjugateSpanBy_zpowers_top a]
    apply fixedSpace_conjugateSpanBy ρ a ⊤ U hU
    intro v hv
    have hd : ρ a v - v ∈ U.map (ρ a - LinearMap.id) := ⟨v, hv, rfl⟩
    exact sub_eq_zero.mp (by simpa only [hm, Submodule.mem_bot] using hd)
  · right
    have hle : U.map (ρ a - LinearMap.id) ≤ LinearMap.range (ρ a - LinearMap.id) :=
      by rintro _ ⟨v, _, rfl⟩; exact LinearMap.mem_range_self _ v
    have hdim := Submodule.finrank_mono hle
    have hpos : 0 < Module.finrank (ZMod 2) (U.map (ρ a - LinearMap.id)) :=
      Nat.pos_of_ne_zero (fun hz => hm (Submodule.finrank_eq_zero.mp hz))
    have he : U.map (ρ a - LinearMap.id) = LinearMap.range (ρ a - LinearMap.id) :=
      Submodule.eq_of_le_of_finrank_eq hle (by omega)
    apply lemma_G_6_2_3 ρ a h.generated ⊤ (conjugateSpanBy_zpowers_top a) U hU
    rw [← he]
    rintro _ ⟨v, hv, rfl⟩
    exact U.sub_mem ((hU (mem_top a) v).2 hv) hv

theorem Hypotheses.rank_one_perfect_normal_moved
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (N : Subgroup G) [N.Normal] [Group.IsPerfect N]
    (hle : N ≤ normalClosure ({a} : Set G)) (hne : N ≠ ⊥) :
    subspaceCommutator ρ ⊤ N = ⊤ := by
  have hU : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ N) := by
    apply subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by simp))
    rw [normalizer_eq_top]
  rcases h.rank_one_invariant_fixed_or_top ht (subspaceCommutator ρ ⊤ N) hU with hc | ht
  · have hn : subspaceCommutator ρ (subspaceCommutator ρ ⊤ N) N = ⊥ := by
      apply bot_unique
      apply le_trans (b := subspaceCommutator ρ (subspaceCommutator ρ ⊤ N)
        (normalClosure ({a} : Set G)))
      · apply Submodule.span_mono
        rintro _ ⟨n, hn, v, hv, rfl⟩
        exact ⟨n, hle hn, v, hv, rfl⟩
      · exact hc.le
    have hf : subspaceCommutator ρ ⊤ N ≤ fixedSpace ρ N := by
      intro v hv n
      exact (subspaceCommutator_eq_bot_iff ρ (subspaceCommutator ρ ⊤ N) N).mp hn hv n
    have hall : (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ N :=
      le_fixedSpace_of_commutator_le_fixedSpace ρ N ⊤
        (le_subspaceStabilizer ρ ⊤ (by simp)) hf
    apply (hne ?_).elim
    apply (eq_bot_iff_forall N).mpr
    intro n hn
    apply h.faithful
    ext v
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_one, Module.End.one_apply] using hall (show v ∈ (⊤ : Submodule (ZMod 2) V) from Submodule.mem_top) ⟨n, hn⟩
  · exact ht

open ChapterB.QuasisimpleSource

theorem Hypotheses.rank_one_quasisimple_section_top
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (hq : IsQuasisimple (generalizedFitting (normalClosure ({a} : Set G))))
    (s : MovedSection (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G)))) :
    s.space.toSubmodule = ⊤ := by
  let := h.finite_group
  let K := normalClosure ({a} : Set G)
  let F := generalizedFitting K
  let N := F.map K.subtype
  let e : F ≃* N := F.equivMapOfInjective K.subtype K.subtype_injective
  let : IsQuasisimple F := hq
  let : IsQuasisimple N := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (N ⧸ center N) := IsQuasisimple.simple
  let : Nontrivial N := (QuotientGroup.mk'_surjective (center N)).nontrivial
  have hn : N ≠ ⊥ := (nontrivial_iff_ne_bot N).mp inferInstance
  have hle : N ≤ K := by rintro x ⟨k, _, rfl⟩; exact k.property
  have hfull := h.rank_one_perfect_normal_moved ht N hle hn
  rw [s.space_eq]
  have heq : moved (ρ.comp K.subtype) F = subspaceCommutator ρ ⊤ N := by
    apply congrArg (Submodule.span (ZMod 2))
    ext v
    constructor
    · rintro ⟨k, hk, w, hw, rfl⟩
      exact ⟨k, mem_map_of_mem K.subtype hk, w, hw, rfl⟩
    · rintro ⟨g, ⟨k, hk, rfl⟩, w, hw, rfl⟩
      exact ⟨k, hk, w, hw, rfl⟩
  exact heq.trans hfull

/-- The full B.4 actor on the original B.5.1 quotient section. -/
theorem Hypotheses.normalClosure_section_generated
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    {L : Subgroup (normalClosure ({a} : Set G))}
    (s : MovedSection (ρ.comp (normalClosure ({a} : Set G)).subtype) L) :
    offenderSubgroup s.action = ⊤ := by
  let := h.finite_group
  let := h.finite_module
  exact normalClosure_subquotient_offenderSubgroup ρ a h.involution h.nonidentity
    ht.le s.space s.central

/-- The same original involution generates a best offender on the literal section. -/
theorem Hypotheses.normalClosure_section_original_best
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    {L : Subgroup (normalClosure ({a} : Set G))}
    (s : MovedSection (ρ.comp (normalClosure ({a} : Set G)).subtype) L) :
    IsBestOffender s.action (zpowers
      (⟨a, subset_normalClosure (Set.mem_singleton a)⟩ : normalClosure ({a} : Set G))) := by
  let := h.finite_group
  let := h.finite_module
  apply bestOffender_of_involution_displacement_le_one
  · exact Subtype.ext h.involution
  · exact fun he => h.nonidentity (congrArg Subtype.val he)
  · exact (subquotient_displacement_rank_le _ s.space s.central _).trans ht.le
end CFSG.Quasithin.ChapterG.Section06
