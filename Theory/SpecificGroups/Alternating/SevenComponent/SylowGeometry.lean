module
public import GorensteinWalter.Classification
public import Theory.Representation.BinaryPermutation.SevenCubic
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The seven-point Sylow geometry used in C.1.29

A two-group containing the literal (4,2)-element fixes the last point:
its action on seven points has a fixed point, and that element fixes only
the last one. Its orbit through the first point has power-of-two cardinality
between four and seven, hence exactly four. It therefore preserves the first
four points and normalizes the cubic group on the complementary triple.
No enumeration of S₇ or assumed orbit table enters this proof.

Source: Aschbacher–Smith C.1.29, printed p.134.
-/
public section
open Subgroup MulAction
open BinaryPermutation.SevenCubic
namespace alternatingGroup.SevenComponent

/-- Every two-group containing the marked (4,2)-element fixes the last point. -/
theorem fixes_last_of_rho_mem (P : Subgroup (Equiv.Perm (Fin 7)))
    (hP : IsPGroup 2 P) (hr : GorensteinWalter.d8rho ∈ P) :
    ∀ g ∈ P, g 6 = 6 := by
  obtain ⟨a, ha⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Fin 7) (by simp)
  have hrfix := ha (⟨GorensteinWalter.d8rho, hr⟩ : P)
  have he : a = 6 :=
    (by decide : ∀ a : Fin 7, GorensteinWalter.d8rho a = a → a = 6) a hrfix
  subst a
  exact fun g hg => ha ⟨g, hg⟩

/-- The four-cycle forces the first orbit to have exactly four points. -/
theorem first_orbit_of_rho_mem (P : Subgroup (Equiv.Perm (Fin 7)))
    (hP : IsPGroup 2 P) (hr : GorensteinWalter.d8rho ∈ P) :
    orbit P (0 : Fin 7) = ({0, 1, 2, 3} : Set (Fin 7)) := by
  classical
  let O := orbit P (0 : Fin 7)
  have hs : ({0, 1, 2, 3} : Finset (Fin 7)) ⊆ O.toFinset := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · simpa only [Set.mem_toFinset] using mem_orbit_self (0 : Fin 7)
    · exact Set.mem_toFinset.mpr ⟨⟨GorensteinWalter.d8rho, hr⟩, (by decide : GorensteinWalter.d8rho 0 = 1)⟩
    · exact Set.mem_toFinset.mpr ⟨⟨GorensteinWalter.d8rho ^ 2, P.pow_mem hr 2⟩, (by decide : (GorensteinWalter.d8rho ^ 2) 0 = 2)⟩
    · exact Set.mem_toFinset.mpr ⟨⟨GorensteinWalter.d8rho ^ 3, P.pow_mem hr 3⟩, (by decide : (GorensteinWalter.d8rho ^ 3) 0 = 3)⟩
  have h4 : 4 ≤ Nat.card O := by
    simpa [O, Nat.card_eq_fintype_card, Set.toFinset_card] using Finset.card_le_card hs
  have h7 : Nat.card O ≤ 7 := by
    simpa using Nat.card_le_card_of_injective (f := fun x : O => (x : Fin 7)) Subtype.val_injective
  obtain ⟨n, hn⟩ := hP.card_orbit (0 : Fin 7)
  have hn2 : n ≤ 2 := by
    by_contra hh
    have hh' := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) (show 3 ≤ n by omega)
    change Nat.card O = 2 ^ n at hn
    omega
  have hc : Nat.card O = 4 := by
    change Nat.card O = 2 ^ n at hn
    interval_cases n <;> norm_num only [pow_zero, pow_one, show 2 ^ 2 = 4 from rfl] at hn <;> omega
  have he : ({0, 1, 2, 3} : Finset (Fin 7)) = O.toFinset :=
    Finset.eq_of_subset_of_card_le hs (by simpa [Nat.card_eq_fintype_card, Set.toFinset_card] using hc.le)
  simpa only [Set.coe_toFinset, Finset.coe_insert, Finset.coe_singleton] using
    congrArg (fun s : Finset (Fin 7) => (s : Set (Fin 7))) he.symm
/-- The same Sylow geometry normalizes the complementary cubic subgroup. -/
theorem normalizes_cubic_of_rho_mem (P : Subgroup (Equiv.Perm (Fin 7)))
    (hP : IsPGroup 2 P) (hr : GorensteinWalter.d8rho ∈ P) :
    P ≤ normalizer (C : Set (Equiv.Perm (Fin 7))) := by
  have ho := first_orbit_of_rho_mem P hP hr
  have hpres (g : P) (i : Fin 7) (hi : i ∈ ({0, 1, 2, 3} : Set (Fin 7))) :
      g.val i ∈ ({0, 1, 2, 3} : Set (Fin 7)) := by
    rw [← ho] at hi ⊢
    obtain ⟨a, rfl⟩ := hi
    exact ⟨g * a, rfl⟩
  intro g hg
  have h6 := fixes_last_of_rho_mem P hP hr g hg
  have h45 (i : Fin 7) (hi : i = 4 ∨ i = 5) : g i = 4 ∨ g i = 5 := by
    have hn : g i ∉ ({0, 1, 2, 3} : Set (Fin 7)) := by
      intro hh
      have hh' := hpres (⟨g, hg⟩ : P)⁻¹ (g i) hh
      have hb : i ∈ ({0, 1, 2, 3} : Set (Fin 7)) := by simpa using hh'
      rcases hi with rfl | rfl <;> norm_num [Fin.ext_iff] at hb
    have hn6 : g i ≠ 6 := by
      intro hh
      have hh' : i = 6 := g.injective (hh.trans h6.symm)
      rcases hi with rfl | rfl <;> norm_num [Fin.ext_iff] at hh'
    exact (by decide : ∀ a : Fin 7, a ∉ ({0, 1, 2, 3} : Set (Fin 7)) → a ≠ 6 →
      a = 4 ∨ a = 5) (g i) hn hn6
  have hswap (a b : Fin 7) : MulAut.conj g (Equiv.swap a b) = Equiv.swap (g a) (g b) := by
    change g * Equiv.swap a b * g⁻¹ = _
    rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]
  have hc : MulAut.conj g cycle = Equiv.swap (g 4) (g 5) * Equiv.swap (g 5) 6 := by
    rw [cycle, map_mul, hswap, hswap, h6]
  have hne : g 4 ≠ g 5 := g.injective.ne (by decide)
  have he : MulAut.conj g cycle = cycle ∨ MulAut.conj g cycle = cycle⁻¹ := by
    rcases h45 4 (Or.inl rfl) with h4 | h4 <;>
      rcases h45 5 (Or.inr rfl) with h5 | h5
    · exact False.elim (hne (h4.trans h5.symm))
    · exact Or.inl (by rw [hc, h4, h5]; rfl)
    · exact Or.inr (by rw [hc, h4, h5]; decide)
    · exact False.elim (hne (h4.trans h5.symm))
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change zpowers ((MulAut.conj g) cycle) = C
  rcases he with he | he <;> simp only [he, zpowers_inv]
end alternatingGroup.SevenComponent
