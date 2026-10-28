module

public import GorensteinWalter.DihedralCore
public import Mathlib.GroupTheory.IndexNormal
public import GorensteinWalter.KleinFourMapInjective
import Mathlib.Tactic

/-!
# The two four-groups of the order-eight overlap

The two parity classes of reflections give the two Klein four subgroups
of D₈. The normal subgroup classification proves exhaustiveness, since
every four-group has index two. The concrete subgroup and exponent checks
use only the eight-element model. An injective map transports the entire
pair, including exhaustiveness, into any supplied ambient subgroup.

Source: the dihedral Sylow calculation underlying Aschbacher--Smith
E.1.14(6), printed p.214, and its citation of Asc82a 4.10.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers
private def V (j : ZMod 2) : Subgroup (DihedralGroup 4) where
  carrier := {x | x = .r 0 ∨ x = .r 2 ∨
    x = .sr j.val ∨ x = .sr (j.val + 2)}
  one_mem' := Or.inl rfl
  mul_mem' := by revert j; decide
  inv_mem' := by revert j; decide
private instance (j : ZMod 2) : DecidablePred (· ∈ V j) :=
  fun x => inferInstanceAs (Decidable (x = .r 0 ∨ x = .r 2 ∨
    x = .sr j.val ∨ x = .sr (j.val + 2)))
private theorem cardV (j : ZMod 2) : Nat.card (V j) = 4 := by
  rw [Nat.card_eq_fintype_card]
  revert j
  decide
private instance (j : ZMod 2) : Nontrivial (V j) :=
  Finite.one_lt_card_iff_nontrivial.mp (by rw [cardV]; decide)
private theorem kleinV (j : ZMod 2) : IsKleinFour (V j) := by
  refine ⟨cardV j, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  have hp : ∀ j : ZMod 2, ∀ x : V j, x ^ 2 = 1 := by decide
  intro x hx
  exact ((Nat.prime_two.dvd_iff_eq (by simpa using hx)).mp
    (orderOf_dvd_of_pow_eq_one (hp j x))).symm
private theorem Vneq : V 0 ≠ V 1 := by
  intro h
  have : DihedralGroup.sr 0 ∈ V 1 := h ▸ (by decide : DihedralGroup.sr 0 ∈ V 0)
  exact (by decide : DihedralGroup.sr 0 ∉ V 1) this
private theorem indexTwo_eqV (j : ZMod 4) :
    dihedralIndexTwoSubgroup 2 j = V (j.val : ZMod 2) := by
  ext x
  rw [mem_dihedralIndexTwoSubgroup_iff (by decide)]
  constructor
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact (show ∀ k : ZMod 4, ∀ j : ZMod 2, DihedralGroup.r (2 * k) ∈ V j by decide)
        (k : ZMod 4) (j.val : ZMod 2)
    · exact (show ∀ j k : ZMod 4, DihedralGroup.sr (j + 2 * k) ∈ V (j.val : ZMod 2)
        by decide) j (k : ZMod 4)
  · have hf : ∀ (j : ZMod 4) (x : DihedralGroup 4), x ∈ V (j.val : ZMod 2) →
        (∃ k : Fin 4, x = .r (2 * (k.val : ZMod 4))) ∨
        (∃ k : Fin 4, x = .sr (j + 2 * (k.val : ZMod 4))) := by decide
    intro hx
    rcases hf j x hx with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨(k.val : ℤ), by simpa using hk⟩
    · exact Or.inr ⟨(k.val : ℤ), by simpa using hk⟩
private theorem eight_cases (C : Subgroup (DihedralGroup 4)) [IsKleinFour C] :
    C = V 0 ∨ C = V 1 := by
  have hi : C.index = 2 := by
    have h := C.index_mul_card
    rw [IsKleinFour.card_four, DihedralGroup.nat_card] at h
    omega
  rcases normal_noncyclic_subgroup_dihedral_two_pow (m := 2) (by decide) C
    (normal_of_index_eq_two hi) IsKleinFour.not_isCyclic with ht | ⟨j, rfl⟩
  · have hc := IsKleinFour.card_four (G := C)
    rw [ht, Nat.card_congr (topEquiv (G := DihedralGroup 4)).toEquiv,
      DihedralGroup.nat_card] at hc
    omega
  · rw [indexTwo_eqV]
    have hj : (j.val : ZMod 2) = 0 ∨ (j.val : ZMod 2) = 1 := (show ∀ j : ZMod 2, j = 0 ∨ j = 1 by decide) _
    exact hj.imp (fun h => by rw [h]) (fun h => by rw [h])

theorem dihedral_four_four_groups {G : Type*} [Group G] (D : Subgroup G)
    (eD : D ≃* DihedralGroup 4) :
    ∃ A B : Subgroup G, A ≤ D ∧ B ≤ D ∧ IsKleinFour A ∧ IsKleinFour B ∧ A ≠ B ∧
      ∀ C : Subgroup G, C ≤ D → IsKleinFour C → C = A ∨ C = B := by
  let j := D.subtype.comp eD.symm.toMonoidHom
  have hj : Function.Injective j := D.subtype_injective.comp eD.symm.injective
  have hjrange : j.range = D := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (eD.symm y).property
    · intro hx
      exact ⟨eD ⟨x, hx⟩, by simp [j]⟩
  refine ⟨(V 0).map j, (V 1).map j, ?_, ?_,
    isKleinFour_map_of_injective _ (kleinV 0) j hj,
    isKleinFour_map_of_injective _ (kleinV 1) j hj, ?_, ?_⟩
  · rw [← hjrange]; exact map_le_range _ _
  · rw [← hjrange]; exact map_le_range _ _
  · exact fun h => Vneq ((map_injective hj) h)
  · intro C hCD hC
    have hCj : (C.comap j).map j = C := map_comap_eq_self (hjrange ▸ hCD)
    let eC : C.comap j ≃* C :=
      (equivMapOfInjective _ j hj).trans (MulEquiv.subgroupCongr hCj)
    let : IsKleinFour (C.comap j) :=
      ⟨(Nat.card_congr eC.toEquiv).trans hC.card_four,
        (Monoid.exponent_eq_of_mulEquiv eC).trans hC.exponent_two⟩
    rcases eight_cases (C.comap j) with h | h
    · exact Or.inl (hCj.symm.trans (congrArg (fun H => H.map j) h))
    · exact Or.inr (hCj.symm.trans (congrArg (fun H => H.map j) h))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers
