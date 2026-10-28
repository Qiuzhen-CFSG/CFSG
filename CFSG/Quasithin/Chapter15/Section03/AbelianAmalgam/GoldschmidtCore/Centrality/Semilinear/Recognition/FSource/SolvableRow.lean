module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Nilpotent

/-!
# Solvability and Sylow commutativity in F.6.18(2)

The two actual models in the solvable row are S₃ × S₃ and an extension
of an order-27 extraspecial group by E₄. The first has order 36 and the
second order 108, so their Sylow two-subgroups have order four. Solvability
follows from the symmetric-three factors or the normal three-group and
abelian quotient. No splitting of the extraspecial extension is assumed.

The original paired-point application in 13.2.12 uses exactly these two
properties, via its literal O₃′ quotient. Source: Aschbacher--Smith,
F.6.18(2), printed p.309, and 13.2.12, printed p.882.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
variable {D : Type*} [Group D] [Finite D]

/-- Both models in F.6.18(2) are solvable and have abelian Sylow two-subgroups. -/
theorem solvable_row_sylow_abelian (S : Sylow 2 D)
    (hmodel : Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup D, ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty ((D ⧸ N) ≃* E4)) :
    Group.IsSolvable D ∧ IsMulCommutative S := by
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Group.isSolvable_of_isSolvable_injective
        (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    refine ⟨Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective, ?_⟩
    apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
    rw [S.card_eq_multiplicity, Nat.card_congr e.toEquiv, Nat.card_prod,
      Nat.card_perm, Nat.card_fin]
    decide +kernel
  · obtain ⟨N,hn,_,hc,_,⟨e⟩⟩ := hmodel
    let := hn
    let : Group.IsNilpotent N := (IsPGroup.of_card (p := 3) (n := 3) hc).isNilpotent
    let : Group.IsSolvable (D ⧸ N) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    refine ⟨(Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,inferInstance⟩, ?_⟩
    have hD : Nat.card D = 108 := by
      rw [card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr e.toEquiv, hc]
      norm_num [E4,C,Nat.card_prod]
    apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
    rw [S.card_eq_multiplicity,hD]
    decide +kernel
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
