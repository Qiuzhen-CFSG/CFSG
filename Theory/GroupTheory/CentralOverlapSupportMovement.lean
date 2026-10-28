module
public import Theory.GroupTheory.IndependentSupportMovement
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.GroupTheory.IsPerfect

/-!
# Covering supports with a component-fixed intersection

Directness after removing fixed points only puts the intersection of two
covering supports in the component centralizer. For a perfect component this
suffices: a nontrivial involution displacement cannot itself be component-fixed,
by the three-subgroups lemma. Hence the two support contributions cannot cancel.
The fixed-point preimage identity also lifts fixedness through the original
central kernel, with no assertion that the two covers are disjoint modulo it.

Source application: Aschbacher--Smith, F.9.18(4iii), printed p.325, and the
covering-module vector argument in 14.6.22--24, printed pp.1038--1039.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A perfect actor has no nontrivial action with central displacement. -/
theorem centralizes_of_commutator_le_centralizer
    (K A : Subgroup G) [Group.IsPerfect K]
    (h : ⁅A,K⁆ ≤ centralizer (K : Set G)) : A ≤ centralizer (K : Set G) := by
  have h₁ : ⁅⁅A,K⁆,K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr h
  have h₂ : ⁅⁅K,A⁆,K⁆ = ⊥ := by rwa [commutator_comm K A]
  have h₃ := commutator_commutator_eq_bot_of_rotate h₂ h₁
  rw [K.commutator_eq_self] at h₃
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h₃)

/-- Fixedness modulo a central layer lifts across a perfect actor. -/
theorem commutatorPreimage_eq_inf_centralizer_of_perfect
    (K U Z : Subgroup G) [Group.IsPerfect K]
    (hUZ : U ≤ normalizer (Z : Set G))
    (hZK : Z ≤ centralizer (K : Set G)) :
    commutatorPreimage U K Z = U ⊓ centralizer (K : Set G) := by
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le U K Z)
      (centralizes_of_commutator_le_centralizer K _
        ((commutator_commutatorPreimage_le U K Z hUZ).trans hZK))
  · exact le_commutatorPreimage inf_le_left
      ((commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le)

/-- Disjoint images after removing fixed points give central intersection,
without asserting that the covering supports intersect only in Z. -/
theorem central_intersection_of_disjoint_images
    {Q : Type*} [Group Q] (K U W W' : Subgroup G)
    (hWU : W ≤ U) (q : U →* Q)
    (hker : q.ker ≤ (centralizer (K : Set G)).subgroupOf U)
    (hdis : Disjoint ((W.subgroupOf U).map q) ((W'.subgroupOf U).map q)) :
    W ⊓ W' ≤ centralizer (K : Set G) := by
  intro w hw
  let u : U := ⟨w,hWU hw.1⟩
  have hz : q u = 1 := (Subgroup.disjoint_def.mp hdis)
    (mem_map_of_mem q (show u ∈ W.subgroupOf U from hw.1))
    (mem_map_of_mem q (show u ∈ W'.subgroupOf U from hw.2))
  exact hker (show u ∈ q.ker from hz)

/-- Central overlap of two normalized supports is sufficient to prevent
cancellation under a perfect actor; their intersection need not lie in Z. -/
theorem product_not_centralized_of_central_intersection
    (K W W' : Subgroup G) [Group.IsPerfect K]
    (hKW : K ≤ normalizer (W : Set G)) (hKW' : K ≤ normalizer (W' : Set G))
    (hWW' : W ≤ normalizer (W' : Set G))
    (hdis : W ⊓ W' ≤ centralizer (K : Set G))
    (u v : G) (hu2 : u ^ 2 = 1) (hu : u ∈ W) (hv : v ∈ W')
    (hmove : ¬ K ≤ centralizer ({u} : Set G)) :
    ¬ K ≤ centralizer ({u*v} : Set G) := by
  have hnoncentral : ∃ k ∈ K, ⁅u,k⁆ ∉ centralizer (K : Set G) := by
    by_contra hn
    push Not at hn
    let A : Subgroup G := {
      carrier := {a | a = 1 ∨ a = u}
      one_mem' := Or.inl rfl
      mul_mem' := by rintro a b (rfl | rfl) (rfl | rfl) <;> simp_all [pow_two]
      inv_mem' := by
        rintro a (rfl | rfl)
        · simp
        · exact Or.inr (inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hu2)) }
    have hc : ⁅A,K⁆ ≤ centralizer (K : Set G) := by
      apply commutator_le.mpr
      rintro a (rfl | rfl) b hb
      · simp
      · exact hn b hb
    have hh := centralizes_of_commutator_le_centralizer K A hc
    apply hmove
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (hh (Or.inr rfl) k hk)
  exact product_not_centralized_of_disjoint_modulo K W W' (centralizer (K : Set G))
    hKW hKW' hWW' hdis u v hu hv hnoncentral
end Theory.GroupTheory
