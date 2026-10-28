module
public import Theory.Mathieu.M24.ValueBoundParabolics.Construction
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.GroupTheory.CubicSylowExtension

/-!
# Cubic Sylow generation and lifts for the native Mathieu group

The checked native triple generates M₂₄ and has index three over its
marked Sylow. Sylow conjugacy transports the triple to any prescribed
Sylow. Every automorphism preserving that Sylow fixes each overgroup:
all automorphisms are inner and the Sylow is self-normalizing. The
literal core-quotient lift therefore supplies an escaping cubic overgroup
of a full ambient Sylow whenever its normalized component escapes.

Source: Aschbacher--Smith, E.4.3(2), pp.241--242, and the strict Mathieu
point enlargement in 12.5.11(2), p.821. The exterior-source application
retains the original component and Sylow, not just their isomorphism types.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M24ValueBoundParabolics
open M24LocalGeometry.SylowNormalizer

/-- All automorphisms preserving the specified M24 Sylow fix each of its overgroups. -/
theorem sylow_overgroup_invariant (S : Sylow 2 M24) (J : Subgroup M24)
    (hSJ : (S : Subgroup M24) ≤ J) (a : MulAut M24)
    (ha : (S : Subgroup M24).map a.toMonoidHom = S) : J.map a.toMonoidHom = J := by
  obtain ⟨g,rfl⟩ := M24OuterRestriction.conj_surjective a
  have hg : g ∈ normalizer (S : Set M24) := mem_normalizer_iff_map_conj_eq.mpr ha
  have hgS := sylow_normalizer_le candidate_card
    (candidate_automorphisms_isPGroup candidate_card) S hg
  exact mem_normalizer_iff_map_conj_eq.mp (J.le_normalizer (hSJ hgS))

/-- The native cubic parabolics generate for every prescribed Sylow subgroup. -/
theorem invariant_cubic_generation (S : Sylow 2 M24) (N : Subgroup M24)
    (hlocal : ∀ J : Subgroup M24, (S : Subgroup M24) ≤ J →
      (S : Subgroup M24).relIndex J = 3 →
      (∀ a : MulAut M24, (S : Subgroup M24).map a.toMonoidHom = S →
        J.map a.toMonoidHom = J) → J ≤ N) : N = ⊤ := by
  obtain ⟨P,hP,hcard,hgen⟩ := exists_native_triple
  have hs : Nat.card candidate = 2 ^ (Nat.card M24).factorization 2 := by
    rw [candidate_card,m24_order]
    decide +kernel
  let S0 : Sylow 2 M24 := Sylow.ofCard candidate hs
  have hS0 : (S0 : Subgroup M24) = candidate := Sylow.coe_ofCard candidate hs
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S0 S
  let e := MulAut.conj g
  have hS : candidate.map e.toMonoidHom = (S : Subgroup M24) := by
    have hh := congrArg Sylow.toSubgroup hg
    change (S0 : Subgroup M24).map e.toMonoidHom = S at hh
    rwa [hS0] at hh
  have hle (i : Fin 3) : (P i).map e.toMonoidHom ≤ N := by
    have hSP : (S : Subgroup M24) ≤ (P i).map e.toMonoidHom :=
      hS ▸ map_mono (hP i)
    apply hlocal _ hSP
    · rw [←hS,relIndex_map_map_of_injective _ _ e.injective]
      have hi := (candidate.subgroupOf (P i)).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe (hP i)).toEquiv,candidate_card,hcard i] at hi
      change candidate.relIndex (P i) * 1024 = 3072 at hi
      omega
    · exact sylow_overgroup_invariant S _ hSP
  apply top_unique
  rw [←map_top_of_surjective e.toMonoidHom e.surjective,←hgen,Subgroup.map_iSup]
  exact iSup_le hle

/-- The native M24 cubic parabolics lift through the actual two-core quotient
and the full ambient Sylow action, without an extra inner-action premise. -/
theorem exists_cubic_overgroup {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (K M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* M24) (hKM : ¬ K ≤ M) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧ H ≤ K ⊔ (T : Subgroup G) ∧
      (T : Subgroup G).relIndex H = 3 ∧ ¬ H ≤ M := by
  apply Subgroup.CubicSylowExtension.exists_cubic_overgroup T K M hTM hn eK
    ⊤ (fun _ _ => mem_top _) ?_ hKM
  intro S N _ hlocal
  apply invariant_cubic_generation S N
  intro J hSJ hi hinv
  exact hlocal J hSJ hi (fun a _ ha => hinv a ha)
end Sporadic.Mathieu.M24ValueBoundParabolics
