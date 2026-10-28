module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Simultaneous correction by central commutators

For a subgroup K and a subgroup Z centralizing K, the two commutator
rows associated to t and v give a homomorphism K → Z × Z. Its kernel
is the centralizer of {t,v} in K. If the kernel has the complementary
order, this homomorphism is surjective. Consequently, any two changes
of t and v by elements of Z can be undone by a single conjugation in K.

This is the first isomorphism theorem applied to a central commutator
pairing, in a form that retains the literal ambient elements and subgroups.
The binary specialization is the counting argument in Parrott,
*A characterization of the Tits' simple group* (1972), pp.673–674.
-/

open Subgroup
open scoped commutatorElement
namespace Subgroup

private def centralCommutatorRow {G : Type*} [Group G]
    (K Z : Subgroup G) (hZ : Z ≤ centralizer (K : Set G))
    (t : G) (ht : ∀ j ∈ K, ⁅t, j⁆ ∈ Z) : K →* Z where
  toFun j := ⟨⁅t, (j : G)⁆, ht j j.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅t, (a : G) * (b : G)⁆ = ⁅t, (a : G)⁆ * ⁅t, (b : G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅t, (a : G)⁆ * ((a : G) * ⁅t, (b : G)⁆) * (a : G)⁻¹ := by group
      _ = ⁅t, (a : G)⁆ * ⁅t, (b : G)⁆ := by
        rw [hZ (ht b b.property) a a.property]
        group

/-- A full-sized image of the two central commutator rows realizes every pair. -/
public theorem exists_pair_commutator_of_centralizer_card
    {G : Type*} [Group G] [Finite G]
    (K Z : Subgroup G) (hZ : Z ≤ centralizer (K : Set G))
    (t v : G) (ht : ∀ j ∈ K, ⁅t, j⁆ ∈ Z) (hv : ∀ j ∈ K, ⁅v, j⁆ ∈ Z)
    (hcard : Nat.card K = Nat.card Z * Nat.card Z *
      Nat.card (K ⊓ centralizer ({t, v} : Set G) : Subgroup G))
    (a b : G) (ha : a ∈ Z) (hb : b ∈ Z) :
    ∃ j ∈ K, ⁅t, j⁆ = a ∧ ⁅v, j⁆ = b := by
  let f := (centralCommutatorRow K Z hZ t ht).prod
    (centralCommutatorRow K Z hZ v hv)
  have hker : f.ker.map K.subtype = K ⊓ centralizer ({t, v} : Set G) := by
    ext j
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : f x = 1 := hx
      have ht' : ⁅t, (x : G)⁆ = 1 := congrArg (fun p : Z × Z => (p.1 : G)) hx'
      have hv' : ⁅v, (x : G)⁆ = 1 := congrArg (fun p : Z × Z => (p.2 : G)) hx'
      refine ⟨x.property, ?_⟩
      intro y hy
      rcases hy with rfl | hy
      · exact commutatorElement_eq_one_iff_mul_comm.mp ht'
      · obtain rfl := Set.mem_singleton_iff.mp hy
        exact commutatorElement_eq_one_iff_mul_comm.mp hv'
    · intro hj
      refine ⟨⟨j, hj.1⟩, ?_, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply Prod.ext <;> apply Subtype.ext
      · exact commutatorElement_eq_one_iff_mul_comm.mpr (hj.2 t (by simp))
      · exact commutatorElement_eq_one_iff_mul_comm.mpr (hj.2 v (by simp))
  have hkcard : Nat.card f.ker =
      Nat.card (K ⊓ centralizer ({t, v} : Set G) : Subgroup G) := by
    rw [← hker, card_map_of_injective K.subtype_injective]
  have hc := f.ker.index_mul_card
  rw [index_ker] at hc
  have hrange : f.range = ⊤ := by
    apply eq_top_of_card_eq
    rw [Nat.card_prod]
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.ker))
    rw [hc, hkcard]
    exact hcard
  obtain ⟨j, hj⟩ := (MonoidHom.range_eq_top.mp hrange) (⟨a, ha⟩, ⟨b, hb⟩)
  exact ⟨j, j.property, congrArg (fun p : Z × Z => (p.1 : G)) hj,
    congrArg (fun p : Z × Z => (p.2 : G)) hj⟩

/-- A single element of K corrects both prescribed central displacements. -/
public theorem exists_pair_conjugation_of_centralizer_card
    {G : Type*} [Group G] [Finite G]
    (K Z : Subgroup G) (hZ : Z ≤ centralizer (K : Set G))
    (t v : G) (ht : ∀ j ∈ K, ⁅t, j⁆ ∈ Z) (hv : ∀ j ∈ K, ⁅v, j⁆ ∈ Z)
    (hcard : Nat.card K = Nat.card Z * Nat.card Z *
      Nat.card (K ⊓ centralizer ({t, v} : Set G) : Subgroup G))
    (t0 v0 : G) (ht0 : t0 * t⁻¹ ∈ Z) (hv0 : v0 * v⁻¹ ∈ Z) :
    ∃ j ∈ K, j * t0 * j⁻¹ = t ∧ j * v0 * j⁻¹ = v := by
  obtain ⟨j, hj, htj, hvj⟩ := exists_pair_commutator_of_centralizer_card
    K Z hZ t v ht hv hcard (t0 * t⁻¹) (v0 * v⁻¹) ht0 hv0
  have correct (x x0 : G) (hx0 : x0 * x⁻¹ ∈ Z)
      (hxj : ⁅x, j⁆ = x0 * x⁻¹) : j * x0 * j⁻¹ = x := by
    have hc := hZ hx0 j hj
    calc
      j * x0 * j⁻¹ = (j * (x0 * x⁻¹)) * x * j⁻¹ := by group
      _ = ((x0 * x⁻¹) * j) * x * j⁻¹ := by rw [hc]
      _ = x := by rw [← hxj, commutatorElement_def]; group
  exact ⟨j, hj, correct t t0 ht0 htj, correct v v0 hv0 hvj⟩

end Subgroup
