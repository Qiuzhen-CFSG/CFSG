module

public import Theory.SpecificGroups.PSL2.SmallPrimeFourGroup.NormalizerEscape.Counting
public import Theory.SpecificGroups.PSL2.SmallPrimeFourGroup.NormalizerEscape.ModelFacts
public import Theory.SpecificGroups.PSL2.SmallPrimeFourGroup.NormalizerEscape.Dihedral
public import Theory.SpecificGroups.PSL2.SmallPrimeFourGroup.DihedralPairs
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Tactic

/-!
# Four-group normalizer escape in small prime PSL₂

The centralizer of the marked inner involution has more than eight elements.
Inside the low dihedral normalizer at most four elements centralize that mark,
so at most one four-group through it lies there. Every automorphism four-group
is self-centralizing, and at most eight elements of its normalizer fix the
mark. A centralizing inner element therefore moves the four-group outside
the low dihedral normalizer. All transports use the literal conjugation map.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript pp.8--9, used by Aschbacher--Smith K.2, printed p.453.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2.SmallPrimeFourGroup

/-- A four-group through a marked inner involution escapes the normalizer
of the low maximal dihedral subgroup by an inner conjugator fixing the mark. -/
theorem normalizer_escape (F : Type) [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (hF : Nat.card F = p)
    (a b : PSL(2, F)) (ha2 : a ^ 2 = 1) (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1)
    (hmax : IsCoatom (closure ({a, b} : Set PSL(2, F))))
    (hcard : Nat.card (closure ({a, b} : Set PSL(2, F))) = lowOrder p)
    (A : Subgroup (MulAut PSL(2, F))) (hA : IsElementaryAbelian 2 A)
    (hcardA : Nat.card A = 4) (hbA : MulAut.conj b ∈ A) :
    ∃ x : PSL(2, F), x * b * x⁻¹ = b ∧
      ¬ A.map (MulAut.conj (MulAut.conj x)).toMonoidHom ≤
        normalizer ((closure ({a, b} : Set PSL(2, F))).map
          (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)) : Set (MulAut PSL(2, F))) := by
  have ho : Odd p := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hplarge : 3 < p := by rcases hp with rfl | rfl | rfl | rfl <;> omega
  let : IsSimpleGroup PSL(2, F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsElementaryAbelian 2 A := hA
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour A := ⟨hcardA, IsElementaryAbelian.exponent_eq_prime⟩
  let j : PSL(2, F) →* MulAut PSL(2, F) := MulAut.conj
  have hj : Function.Injective j :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot (psl2_center_eq_bot F)
  have hi : j.range.index = 2 := prime_card_inner_index F ho hplarge hF
  let C := (centralizer ({b} : Set PSL(2, F))).map j
  have hC : C ≤ centralizer ({j b} : Set (MulAut PSL(2, F))) := by
    rintro c ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg j (mem_centralizer_singleton_iff.mp hx)
  have hlarge : 8 < Nat.card C := by
    rw [card_map_of_injective hj]
    exact involution_centralizer_gt_eight F hp hF b hb1 hb2
  have hbaut : j b ≠ 1 := by
    intro h
    apply hb1
    apply hj
    simpa only [map_one] using h
  have hDlarge : 4 < Nat.card (closure ({a, b} : Set PSL(2, F))) := by
    rw [hcard]
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder]
  have hDmod : Nat.card (closure ({a, b} : Set PSL(2, F))) % 4 = 2 := by
    rw [hcard]
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [lowOrder]
  have hsmall := pair_normalizer_centralizer_card_le_four
    j hj hi a b ha2 hb1 hb2 hmax hDlarge hDmod
  obtain ⟨c, hc, hescape⟩ := exists_conjugate_not_le_of_small_centralizer
    A C (normalizer ((closure ({a, b} : Set PSL(2, F))).map j : Set (MulAut PSL(2, F))))
    (j b) hbA hbaut hC hlarge hsmall
    (automorphism_four_centralizer F ho hplarge hF A inferInstance)
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hc
  refine ⟨x, ?_, hescape⟩
  rw [mem_centralizer_singleton_iff.mp hx]
  simp

end Theory.PSL2.SmallPrimeFourGroup
