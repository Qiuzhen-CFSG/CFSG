module

public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds
public import Theory.Representation.BinaryCoprimeDegree.PerfectCentral
public import Theory.GroupTheory.PGroup.TransitivePlane
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic

/-!
# Binary degree bounds from transitive elementary planes

An elementary abelian subgroup of order p² has p+1 lines. Transitivity of its
actual normalizer on nonidentity elements makes all these lines one orbit.
The binary hyperplane theorem therefore gives degree at least
(p+1) ordₚ(2), which is at least 24 for prime p≥5.

For a faithful irreducible representation of a perfect central cover, split
according to whether p divides the central kernel. If it does, the Schur-field
and determinant bound gives p ordₚ(2). Otherwise the plane and its normalizer
lift through the coprime kernel. In either case the degree is at least 20.
The original binary representation is retained throughout.

This is a sufficient lower bound for Aschbacher--Smith K.2, printed p.453,
and the odd-prime rank-three branch of Guralnick--Malle, Classification of
2F-modules I, Proposition 4.2; the full projective bound is not asserted.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory

namespace Representation.BinaryCoprimeDegree

private noncomputable def planeSubspaceEquiv {E : Type*} [Group E]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p E] :
    Subgroup E ≃o Submodule (ZMod p) (Additive E) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule p)

private theorem plane_line_card_iff {E : Type*} [Group E] [Finite E]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p E] (H : Subgroup E) :
    Nat.card H = p ↔ Module.finrank (ZMod p) (planeSubspaceEquiv (p := p) H) = 1 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := planeSubspaceEquiv (p := p) H)
  change Nat.card H = _ at hc
  rw [Nat.card_zmod] at hc
  rw [hc]
  simpa only [pow_one] using
    (Nat.pow_right_injective (Fact.out : p.Prime).two_le).eq_iff
      (a := Module.finrank (ZMod p) (planeSubspaceEquiv (p := p) H)) (b := 1)

theorem elementary_plane_card_lines {E : Type*} [Group E] [Finite E]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2) :
    Nat.card {H : Subgroup E // Nat.card H = p} = p + 1 := by
  let e := (Equiv.subtypeEquiv (planeSubspaceEquiv (p := p)).toEquiv
    (plane_line_card_iff (E := E) (p := p))).trans
      (Projectivization.equivSubmodule (ZMod p) (Additive E)).symm
  have hc := Projectivization.card' (ZMod p) (Additive E)
  change Nat.card E = _ at hc
  rw [hE, Nat.card_zmod, ← Nat.card_congr e] at hc
  have hp := (Fact.out : p.Prime).two_le
  have hsub : p - 1 + 1 = p := by omega
  nlinarith

theorem transitive_plane_hyperplane_orbit_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) [IsElementaryAbelian p P] (hP : Nat.card P = p ^ 2)
    (htrans : ∀ x y : P, x ≠ 1 → y ≠ 1 →
      ∃ g : normalizer (P : Set G), P.normalizerMonoidHom g x = y)
    (H : Subgroup P) (hH : H.index = p) :
    Nat.card (normalizerHyperplaneOrbit P H) = p + 1 := by
  have hp := (Fact.out : p.Prime).two_le
  have hcH : Nat.card H = p := by
    have hc := H.card_mul_index
    rw [hP, hH] at hc
    nlinarith
  have he : normalizerHyperplaneOrbit P H = {K : Subgroup P | Nat.card K = p} := by
    ext K
    constructor
    · rintro ⟨g, rfl⟩
      exact (Subgroup.card_map_of_injective (P.normalizerMonoidHom g).injective).trans hcH
    · intro hcK
      let : IsCyclic H := isCyclic_of_prime_card hcH
      let : IsCyclic K := isCyclic_of_prime_card hcK
      obtain ⟨x, hx⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
      obtain ⟨y, hy⟩ := K.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
      have hxn : x ≠ 1 := by
        intro hx1
        rw [← hx, hx1] at hcH
        simp at hcH
        omega
      have hyn : y ≠ 1 := by
        intro hy1
        rw [← hy, hy1] at hcK
        simp at hcK
        omega
      obtain ⟨g, hg⟩ := htrans x y hxn hyn
      refine ⟨g, ?_⟩
      change H.map (P.normalizerMonoidHom g).toMonoidHom = K
      rw [← hx, MonoidHom.map_zpowers]
      change zpowers (P.normalizerMonoidHom g x) = K
      rw [hg, hy]
  rw [he]
  exact elementary_plane_card_lines hP

theorem transitive_plane_degree
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) (hf : Function.Injective rho)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Subgroup G) [IsElementaryAbelian p P] (hP : Nat.card P = p ^ 2)
    (htrans : ∀ x y : P, x ≠ 1 → y ≠ 1 →
      ∃ g : normalizer (P : Set G), P.normalizerMonoidHom g x = y) :
    (p + 1) * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  have hne : P ≠ ⊥ := by
    intro he
    rw [he] at hP
    simp at hP
    have hp := (Fact.out : p.Prime).two_le
    nlinarith
  exact (hyperplane_orbit_degree rho hf hp2 P hne (p + 1)
    (fun H hH => (transitive_plane_hyperplane_orbit_card P hP htrans H hH).ge)).1

private theorem three_le_binary_order {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    3 ≤ orderOf (2 : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hpos : 0 < orderOf (2 : ZMod p) :=
    (isUnit_iff_ne_zero.mpr htwo).isOfFinOrder.orderOf_pos
  by_contra! hsmall
  have hcases : orderOf (2 : ZMod p) = 1 ∨ orderOf (2 : ZMod p) = 2 := by omega
  have hpow := pow_orderOf_eq_one (2 : ZMod p)
  rcases hcases with he | he
  · rw [he, pow_one] at hpow
    have hz : (1 : ZMod p) = 0 := by linear_combination hpow
    exact one_ne_zero hz
  · rw [he] at hpow
    have hz : (3 : ZMod p) = 0 := by linear_combination hpow
    have hd := (ZMod.natCast_eq_zero_iff 3 p).mp hz
    have := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega

theorem twentyFour_le_plane_degree {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    24 ≤ (p + 1) * orderOf (2 : ZMod p) := by
  have hthree := three_le_binary_order hp hp5
  by_cases he : p = 5
  · subst p
    rw [Representation.BinaryPrimeDegree.orderOf_two_mod_five]
  · have hne : p ≠ 6 := by intro he; subst p; norm_num at hp
    have : 7 ≤ p := by omega
    nlinarith

theorem twenty_le_prime_times_binary_order {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    20 ≤ p * orderOf (2 : ZMod p) := by
  have hthree := three_le_binary_order hp hp5
  by_cases he : p = 5
  · subst p
    rw [Representation.BinaryPrimeDegree.orderOf_two_mod_five]
  · have hne : p ≠ 6 := by intro he; subst p; norm_num at hp
    have : 7 ≤ p := by omega
    nlinarith


/-- A transitive plane in a central quotient of a perfect group gives a
binary degree bound, including when p divides the central kernel. -/
theorem central_quotient_transitive_plane_degree
    {G H V : Type*} [Group G] [Finite G] [Group H]
    [Group.IsPerfect G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) [IsIrreducible rho]
    (hf : Function.Injective rho) (f : G →* H) (hsurj : Function.Surjective f)
    (hcentral : f.ker ≤ center G) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hplane : HasTransitiveElementaryPlane H p) :
    p * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  by_cases hd : p ∣ Nat.card f.ker
  · exact perfect_central_prime_degree rho hf Fact.out hp2
      (hd.trans (Subgroup.card_dvd_of_le hcentral))
  · obtain ⟨P, hP, hcard, htrans⟩ := hplane.of_central_coprime f hsurj hcentral
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hd)
    let : IsElementaryAbelian p P := hP
    exact (Nat.mul_le_mul_right (orderOf (2 : ZMod p)) (Nat.le_succ p)).trans
      (transitive_plane_degree rho hf hp2 P hcard htrans)

end Representation.BinaryCoprimeDegree
