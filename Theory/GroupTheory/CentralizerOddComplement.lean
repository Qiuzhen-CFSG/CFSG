module

public import Theory.GroupTheory.FullAutomizerNormalizerControl
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Transfer

/-!
# An odd complement from a centralizer-normalizer intersection

Suppose E is an abelian two-subgroup, Y has odd order, and
C_G(Y) ∩ N_G(E) = YE. The relative normalizer index promotes E to a
Sylow subgroup of C_G(Y). Its normalizer centralizes E, so Burnside
transfer supplies a normal odd complement. The complement is returned
with its literal ambient inclusion and normalization by C_G(Y).

Source application: Aschbacher–Smith, J.2.10, printed p.438 (PDF p.449).
The intersection includes Y; the printed equality omitting Y is erroneous.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The corrected local intersection supplies a normal odd complement in the actual centralizer. -/
theorem exists_odd_complement_of_centralizer_intersection
    (Y E : Subgroup G) [IsMulCommutative E]
    (hE : IsPGroup 2 E) (hY : Odd (Nat.card Y))
    (hinter : centralizer (Y : Set G) ⊓ normalizer (E : Set G) = Y ⊔ E) :
    ∃ P : Subgroup G, Odd (Nat.card P) ∧
      centralizer (Y : Set G) ≤ normalizer (P : Set G) ∧
      centralizer (Y : Set G) = P ⊔ E := by
  let C := centralizer (Y : Set G)
  have hMC : Y ⊔ E ≤ C := hinter ▸ inf_le_left
  have hEC : E ≤ C := le_sup_right.trans hMC
  let D := E.subgroupOf C
  have hD : IsPGroup 2 D := hE.comap_subtype
  have hN : normalizer (D : Set C) = (Y ⊔ E).subgroupOf C := by
    rw [← subgroupOf_normalizer_eq hEC]
    ext x
    change (x : G) ∈ normalizer (E : Set G) ↔ (x : G) ∈ Y ⊔ E
    exact ⟨fun hx => hinter ▸ (show (x : G) ∈ C ⊓ normalizer (E : Set G) from
      ⟨x.property, hx⟩), fun hx => (show (x : G) ∈ C ⊓ normalizer (E : Set G) from
      hinter.symm ▸ hx).2⟩
  have hd : Disjoint Y E := by
    obtain ⟨n, hn⟩ := hE.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hY.coprime_two_right.pow_right n
  have hcard : Nat.card (Y ⊔ E : Subgroup G) = Nat.card Y * Nat.card E :=
    card_sup_eq_mul_of_normalizes_of_disjoint Y E
      (hEC.trans (centralizer_le_normalizer _)) hd
  have hindex : D.relIndex (normalizer (D : Set C)) = Nat.card Y := by
    have hc := (D.subgroupOf (normalizer (D : Set C))).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv, hN,
      Nat.card_congr (subgroupOfEquivOfLe hMC).toEquiv, hcard] at hc
    rw [hN]
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := E)) hc
  have hnot : ¬ 2 ∣ D.relIndex (normalizer (D : Set C)) := by
    rw [hindex]
    exact hY.not_two_dvd_nat
  obtain ⟨S, hS⟩ := exists_sylow_of_local_index D (normalizer (D : Set C)) hD hnot le_rfl
  have hNC : normalizer (S : Set C) ≤ centralizer (S : Set C) := by
    change normalizer ((S : Subgroup C) : Set C) ≤ centralizer ((S : Subgroup C) : Set C)
    rw [hS, hN]
    intro x hx y hy
    apply Subtype.ext
    exact (sup_le (le_centralizer_iff.mp hEC) (le_centralizer E) hx) y hy
  let P := (MonoidHom.transferSylow S hNC).ker
  have hcomp := MonoidHom.ker_transferSylow_isComplement' S hNC
  refine ⟨P.map C.subtype, ?_, ?_, ?_⟩
  · rw [card_map_of_injective C.subtype_injective]
    exact Nat.not_even_iff_odd.mp (fun he =>
      MonoidHom.not_dvd_card_ker_transferSylow S hNC (even_iff_two_dvd.mp he))
  · simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using P.le_normalizer_map C.subtype
  · have hh := congrArg (Subgroup.map C.subtype) hcomp.sup_eq_top
    rw [map_sup] at hh
    change P.map C.subtype ⊔ (S : Subgroup C).map C.subtype = (⊤ : Subgroup C).map C.subtype at hh
    rw [hS, map_subgroupOf_eq_of_le hEC, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh.symm
end Subgroup
