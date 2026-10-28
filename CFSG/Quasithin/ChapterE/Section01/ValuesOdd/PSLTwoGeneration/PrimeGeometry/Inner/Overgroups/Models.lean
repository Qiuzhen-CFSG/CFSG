module

public import GorensteinWalter.DihedralCore
public import GorensteinWalter.KleinFourExceptionTransport
public import GorensteinWalter.DihedralReflectionCentralizerCard
public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic

/-!
# The concrete small models in the prime-field overgroup calculation

A four-group in an even dihedral group contains a reflection, whose centralizer
has order at most four. In S₄ the cycle-type formula bounds an involution's
centralizer by eight. The actual inclusions A₄ → S₄ and A₅ → S₅ give the same
bound; in the latter case parity excludes transpositions. Injective maps from
the literal relative centralizer transfer these bounds to ambient subgroups.

Two noncommuting three-cycles in S₄ also exclude an embedding in any dihedral
group, where all elements of order three are rotations and commute.

Source: the elementary model calculations used in the prime-field case of
Aschbacher--Smith E.1.14(6), printed p.214, with E0 from E.1.2, printed p.210.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups

private theorem involution_cycleType {n : ℕ} (hn : n ≤ 5)
    (z : Equiv.Perm (Fin n)) (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    z.cycleType = {2} ∨ z.cycleType = {2, 2} := by
  have ho : orderOf z = 2 := orderOf_eq_prime_iff.mpr ⟨hz2, hz⟩
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hk
  have hb := z.sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hb
  have hk2 : k = 0 ∨ k = 1 := by omega
  rcases hk2 with rfl | rfl
  · left; simpa using hk
  · right; simpa using hk

/-- Every nonidentity involution in the actual S₄ model has centralizer of
order at most eight. -/
theorem symmetric_four_involution_centralizer (z : Equiv.Perm (Fin 4))
    (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    Nat.card (centralizer ({z} : Set (Equiv.Perm (Fin 4)))) ≤ 8 := by
  rcases involution_cycleType (by decide) z hz hz2 with h | h <;>
    rw [Equiv.Perm.nat_card_centralizer, h] <;> norm_num

private theorem centralizer_card_le_of_injective {K L : Type*} [Group K] [Group L]
    [Finite L] (f : K →* L) (hf : Function.Injective f) (z : K) :
    Nat.card (centralizer ({z} : Set K)) ≤
      Nat.card (centralizer ({f z} : Set L)) := by
  let g : centralizer ({z} : Set K) → centralizer ({f z} : Set L) := fun x =>
    ⟨f x, mem_centralizer_singleton_iff.mpr (by
      simpa using congrArg f (mem_centralizer_singleton_iff.mp x.property))⟩
  exact Nat.card_le_card_of_injective g (fun x y h =>
    Subtype.ext (hf (congrArg Subtype.val h)))

/-- The A₄ bound uses its actual inclusion into S₄. -/
theorem alternating_four_involution_centralizer (z : alternatingGroup (Fin 4))
    (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    Nat.card (centralizer ({z} : Set (alternatingGroup (Fin 4)))) ≤ 8 := by
  apply (centralizer_card_le_of_injective (alternatingGroup (Fin 4)).subtype
    Subtype.val_injective z).trans
  apply symmetric_four_involution_centralizer
  · exact fun h => hz (Subtype.ext h)
  · exact congrArg Subtype.val hz2

/-- The A₅ bound uses double transpositions in its actual five-point action. -/
theorem alternating_five_involution_centralizer (z : alternatingGroup (Fin 5))
    (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    Nat.card (centralizer ({z} : Set (alternatingGroup (Fin 5)))) ≤ 8 := by
  apply (centralizer_card_le_of_injective (alternatingGroup (Fin 5)).subtype
    Subtype.val_injective z).trans
  change Nat.card (centralizer ({(z : Equiv.Perm (Fin 5))} : Set (Equiv.Perm (Fin 5)))) ≤ 8
  have hne : (z : Equiv.Perm (Fin 5)) ≠ 1 := fun h => hz (Subtype.ext h)
  have hpow : (z : Equiv.Perm (Fin 5)) ^ 2 = 1 := congrArg Subtype.val hz2
  rcases involution_cycleType (n := 5) (by decide) z hne hpow with h | h
  · have hs := z.property
    change Equiv.Perm.sign (z : Equiv.Perm (Fin 5)) = 1 at hs
    rw [Equiv.Perm.sign_of_cycleType, h] at hs
    norm_num at hs
  · rw [Equiv.Perm.nat_card_centralizer, h]
    norm_num

/-- Relative centralizers inject into the centralizer of the literal image
of the element under an injective homomorphism from the overgroup. -/
theorem relative_centralizer_card_le {G K : Type*} [Group G] [Group K] [Finite K]
    (M : Subgroup G) (f : M →* K) (hf : Function.Injective f) (z : M) :
    Nat.card ((centralizer ({(z : G)} : Set G)).subgroupOf M) ≤
      Nat.card (centralizer ({f z} : Set K)) := by
  have heq : (centralizer ({(z : G)} : Set G)).subgroupOf M =
      centralizer ({z} : Set M) := by
    ext x
    simp only [mem_subgroupOf, mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [heq]
  exact centralizer_card_le_of_injective f hf z

/-- Any four-group in an even dihedral group contains a reflection, giving
an element with relative centralizer of order at most four. -/
theorem dihedral_actor_centralizer {G : Type*} [Group G] [Finite G]
    (A M : Subgroup G) (hA : IsKleinFour A) (hAM : A ≤ M)
    {k : ℕ} (hk : 0 < k) (eM : M ≃* DihedralGroup (2 * k)) :
    ∃ z : G, z ∈ A ∧ z ≠ 1 ∧
      Nat.card ((centralizer ({z} : Set G)).subgroupOf M) ≤ 4 := by
  classical
  let : NeZero k := ⟨by omega⟩
  let R : Subgroup (DihedralGroup (2 * k)) := zpowers (DihedralGroup.r 1)
  let AM := A.subgroupOf M
  let AD := AM.map eM.toMonoidHom
  have hAD : IsKleinFour AD := isKleinFour_map_mulEquiv_cross AM
    (isKleinFour_subgroupOf hAM hA) eM
  have hnle : ¬ AD ≤ R := fun h =>
    no_kleinFour_subgroup_of_isCyclic R AD hAD h (inferInstance : IsCyclic R)
  obtain ⟨x, hx, hxR⟩ := Set.not_subset.mp hnle
  obtain ⟨a, ha, hax⟩ := mem_map.mp hx
  rcases hxform : x with i | i
  · exact (hxR (hxform ▸ r_mem_zpowers_r_one i)).elim
  · refine ⟨a, ha, ?_, ?_⟩
    · intro ha1
      have ham : a = 1 := Subtype.ext ha1
      have he : DihedralGroup.sr i = 1 := by rw [← hxform, ← hax, ham, map_one]
      cases he
    · have h := relative_centralizer_card_le M eM.toMonoidHom eM.injective a
      rw [hax, hxform] at h
      exact h.trans (card_centralizer_reflection_dihedral_even_le_four i)

/-- S₄ does not embed into any dihedral group: its two indicated elements
of order three do not commute, whereas all odd-order dihedral elements are rotations. -/
theorem not_injective_symmetric_four_dihedral {n : ℕ}
    (f : Equiv.Perm (Fin 4) →* DihedralGroup n) : ¬ Function.Injective f := by
  intro hf
  let a : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
  let b : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3
  have ha : a ^ 3 = 1 := by decide
  have hb : b ^ 3 = 1 := by decide
  have hnc : a * b ≠ b * a := by decide
  have rotation (x : Equiv.Perm (Fin 4)) (hx : x ^ 3 = 1) :
      ∃ i : ZMod n, f x = DihedralGroup.r i := by
    cases hfx : f x with
    | r i => exact ⟨i, rfl⟩
    | sr i =>
      have hh : DihedralGroup.sr i ^ 3 = (1 : DihedralGroup n) := by
        rw [← hfx, ← map_pow, hx, map_one]
      have hbad : DihedralGroup.sr i = (1 : DihedralGroup n) := by
        simpa [pow_succ, pow_two] using hh
      cases hbad
  obtain ⟨i, hi⟩ := rotation a ha
  obtain ⟨j, hj⟩ := rotation b hb
  apply hnc
  apply hf
  simp [hi, hj, add_comm]

/-- In particular, an actual S₄ subgroup cannot be contained in a dihedral overgroup. -/
theorem symmetric_four_not_le_dihedral {G : Type*} [Group G]
    (H M : Subgroup G) {n : ℕ}
    (eH : H ≃* Equiv.Perm (Fin 4)) (eM : M ≃* DihedralGroup n) : ¬ H ≤ M := by
  intro hHM
  let f := eM.toMonoidHom.comp ((Subgroup.inclusion hHM).comp eH.symm.toMonoidHom)
  exact not_injective_symmetric_four_dihedral f
    (eM.injective.comp ((Subgroup.inclusion_injective hHM).comp eH.symm.injective))
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups
