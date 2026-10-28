module

public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Preparation
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility

/-!
# Faithful three-core action in the cubic branch of G.9.4

A commutator lying both in an off-three prime core and in the cubic Fitting
commutator is trivial. Thus faithfulness on F(G) transfers to O₃(G).
Its fixed space and displacement span are invariant under G, so ambient
irreducibility and faithfulness give zero fixed space and full moved space.
Counting three-group orbits then forces even binary dimension.

Source: Aschbacher--Smith, proof of G.9.4, printed p.355, PDF p.366.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

open Subgroup

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

/-- The cubic commutator hypothesis makes every other prime core central under A.
Faithfulness on their join, F(G), therefore transfers to the three-core. -/
theorem faithful_three_core (h : FittingHypothesis K ρ A m)
    (hc : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    A ⊓ centralizer (pCore 3 G : Set G) = ⊥ := by
  apply le_bot_iff.mp
  rw [← h.faithful_fitting]
  apply le_inf inf_le_left
  apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
  intro q
  let p := q.1.1
  let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors q.1.2⟩
  by_cases hp : p = 3
  · simpa only [p, hp] using
      (inf_le_right : A ⊓ centralizer (pCore 3 G : Set G) ≤ _)
  have hcomm : ⁅pCore p G, A⁆ = ⊥ := by
    apply le_bot_iff.mp
    have hd := IsPGroup.disjoint_of_ne p 3 hp (pCore p G) ⁅fittingSubgroup G, A⁆
      pCore_isPGroup hc
    rw [← hd.eq_bot]
    exact le_inf (commutator_le_left _ _)
      (commutator_mono (pCore_le_fitting G p) le_rfl)
  exact inf_le_left.trans (commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm A (pCore p G)).trans hcomm))

/-- A positive-rank actor faithful on the three-core forces that core to be nontrivial. -/
theorem three_core_ne_bot (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hf : A ⊓ centralizer (pCore 3 G : Set G) = ⊥) : pCore 3 G ≠ ⊥ := by
  intro hb
  have ha : A = ⊥ := by
    apply le_bot_iff.mp
    rw [← hf]
    refine le_inf le_rfl ?_
    intro x _ y hy
    have hy1 : y = 1 := by
      have hy' : y ∈ pCore 3 G := hy
      rwa [hb, mem_bot] at hy'
    simp only [hy1, one_mul, mul_one]
  exact (Nat.ne_of_gt hm) (h.toSetup.actor_eq_bot_iff.mp ha)

/-- Normality makes the fixed space a G-subrepresentation; ambient irreducibility
and faithfulness exclude a nonzero fixed vector. -/
theorem three_core_invariants_eq_bot (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hf : A ⊓ centralizer (pCore 3 G : Set G) = ⊥) :
    Representation.invariants (ρ.comp (pCore 3 G).subtype) = ⊥ := by
  let : Representation.IsIrreducible ρ := h.irreducible
  by_contra hn
  have hk := Representation.le_ker_of_normal_invariants_ne_bot ρ (pCore 3 G) hn
  rw [ρ.ker_eq_bot h.faithful] at hk
  exact three_core_ne_bot h hm hf (le_bot_iff.mp hk)

/-- The actual displacement span of the three-core is all of the irreducible module. -/
theorem three_core_moved_eq_top (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hf : A ⊓ centralizer (pCore 3 G : Set G) = ⊥) :
    NilpotentRigidity.movedSpace ρ (pCore 3 G) = ⊤ := by
  let : Representation.IsIrreducible ρ := h.irreducible
  let S : Subrepresentation ρ := ⟨NilpotentRigidity.movedSpace ρ (pCore 3 G),
    Representation.Coinvariants.le_comap_ker ρ (pCore 3 G)⟩
  have hs : S ≠ ⊥ := by
    intro hs
    apply three_core_ne_bot h hm hf
    apply le_bot_iff.mp
    intro x hx
    change x = 1
    apply h.faithful
    ext v
    have hv := Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp (pCore 3 G).subtype)
      ⟨x, hx⟩ v
    have hz : NilpotentRigidity.movedSpace ρ (pCore 3 G) = ⊥ :=
      congrArg Subrepresentation.toSubmodule hs
    change ρ x v - v ∈ NilpotentRigidity.movedSpace ρ (pCore 3 G) at hv
    rw [hz, Submodule.mem_bot, sub_eq_zero] at hv
    simpa only [map_one, Module.End.one_apply] using hv
  exact congrArg Subrepresentation.toSubmodule
    ((IsSimpleOrder.eq_bot_or_eq_top S).resolve_left hs)

/-- Three-group orbit counting gives even binary dimension once the common fixed
space is zero. The imported count uses the action v ↦ ρ(b)v and its literal invariants. -/
theorem even_degree_of_faithful_three_core (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hf : A ⊓ centralizer (pCore 3 G : Set G) = ⊥) :
    Even (Module.finrank (ZMod 2) V) := by
  apply even_iff_two_dvd.mpr
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_three] using
    Representation.BinaryOffender.orderOf_two_dvd_finrank_of_isPGroup
      (ρ.comp (pCore 3 G).subtype) Nat.prime_three (by decide)
      pCore_isPGroup (three_core_invariants_eq_bot h hm hf)

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
