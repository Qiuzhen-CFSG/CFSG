module
public import Theory.GroupTheory.SylowFrattiniBounds
public import Theory.Frattini.PGroup
public import Theory.SpecificGroups.SymplecticSix.OrderRank
public import Theory.SpecificGroups.SymplecticSix.EvenProjective
public import Theory.SpecificGroups.SymplecticSix.FieldTransport

/-!
# A seven-generator Frattini bound for the binary symplectic six-space

A displayed symplectic matrix has order eight, certified by three small
squaring identities. In a Sylow two-subgroup containing it, its square
has order four and lies in the Frattini subgroup. The certified ambient
order bounds that Sylow subgroup by512, so the Frattini quotient has at
most128 elements. Sylow conjugacy and the literal field and central-quotient
comparisons give the bound for every binary projective model.

The matrix is the standard block construction [[A,AS],[0,A^(-transpose)]],
with A the upper unitriangular three-block and S supported at its last
diagonal entry. Source application: Aschbacher--Smith 4.4.10, printed p.621.
No Sylow enumeration or full automorphism classification is required.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticSix.BinarySylowFrattini
private def coordinate : Fin 3 ⊕ Fin 3 → Fin 6 :=
  Sum.elim (fun i => ⟨i, by omega⟩) (fun i => ⟨i + 3, by omega⟩)
private def eightMatrix : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fun i j => (![![1,1,0,0,0,0], ![0,1,1,0,0,1], ![0,0,1,0,0,1],
    ![0,0,0,1,0,0], ![0,0,0,1,1,0], ![0,0,0,1,1,1]] :
      Fin 6 → Fin 6 → ZMod 2) (coordinate i) (coordinate j)
private theorem eightMatrix_mem : eightMatrix ∈ Matrix.symplecticGroup (Fin 3) (ZMod 2) := by
  change eightMatrix * Matrix.J _ _ * eightMatrix.transpose = Matrix.J _ _
  decide +kernel
private def eightElement : Sp (ZMod 2) := ⟨eightMatrix, eightMatrix_mem⟩
private def squareMatrix : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fun i j => (![![1,0,1,0,0,1], ![0,1,0,1,1,1], ![0,0,1,1,1,0], ![0,0,0,1,0,0], ![0,0,0,0,1,0], ![0,0,0,1,0,1]] : Fin 6 → Fin 6 → ZMod 2) (coordinate i) (coordinate j)
private def fourthMatrix : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fun i j => (![![1,0,0,0,1,0], ![0,1,0,1,0,0], ![0,0,1,0,0,0], ![0,0,0,1,0,0], ![0,0,0,0,1,0], ![0,0,0,0,0,1]] : Fin 6 → Fin 6 → ZMod 2) (coordinate i) (coordinate j)
private theorem matrix_square : eightMatrix ^ 2 = squareMatrix := by decide +kernel
private theorem matrix_fourth : eightMatrix ^ 4 = fourthMatrix := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, matrix_square]
  decide +kernel
private theorem eightElement_order : orderOf eightElement = 8 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 2)
  · intro h
    have hh := congrArg (fun x : Sp (ZMod 2) => x.val) h
    change eightMatrix ^ 4 = 1 at hh
    rw [matrix_fourth] at hh
    exact (by decide +kernel : fourthMatrix ≠ 1) hh
  · apply Subtype.ext
    change eightMatrix ^ 8 = 1
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, matrix_fourth]
    decide +kernel

/-- Every Sylow two-subgroup of the binary symplectic matrix group has
a Frattini quotient of order at most128. -/
theorem frattini_card_le (P : Sylow 2 (Sp (ZMod 2))) :
    Nat.card (P ⧸ frattini P) ≤ 128 := by
  have hcyc : IsPGroup 2 (zpowers eightElement) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_zpowers, eightElement_order]
    norm_num)
  obtain ⟨Q,hQ⟩ := hcyc.exists_le_sylow
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv Q)]
  let z : Q := ⟨eightElement, hQ (mem_zpowers _)⟩
  have hz : orderOf z = 8 := by
    rw [← orderOf_injective (Q : Subgroup (Sp (ZMod 2))).subtype Subtype.val_injective z]
    exact eightElement_order
  let : Fact (IsPGroup 2 Q) := ⟨Q.isPGroup'⟩
  have hsq : zpowers (z ^ 2) ≤ frattini Q :=
    zpowers_le.mpr (pth_power_mem_frattini_of_isPGroup (p := 2) z)
  have hfour : 4 ≤ Nat.card (frattini Q) := by
    have hc : Nat.card (zpowers (z ^ 2)) = 4 := by
      rw [Nat.card_zpowers, orderOf_pow, hz]
      norm_num
    exact hc ▸ card_le_of_le hsq
  have hcard : Nat.card Q ≤ 512 := by
    obtain ⟨k,hk⟩ := Q.isPGroup'.exists_card_eq
    have hd := (Q : Subgroup (Sp (ZMod 2))).card_subgroup_dvd_card
    rw [hk, card_sp_of_card_two (by simp)] at hd
    have hk9 : k ≤ 9 := by
      by_contra! h
      have hd' : 2 ^ 10 ∣ 1451520 := (pow_dvd_pow 2 (by omega : 10 ≤ k)).trans hd
      norm_num at hd'
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk9
  have hprod := card_eq_card_quotient_mul_card_subgroup (frattini Q)
  nlinarith

/-- The same bound under the actual binary projective model equivalence. -/
theorem frattini_card_le_of_equiv {A F : Type*} [Group A] [Finite A] [Field F] [Finite F]
    (hF : Nat.card F = 2) (e : A ≃* PSp F) (P : Sylow 2 A) :
    Nat.card (P ⧸ frattini P) ≤ 128 := by
  let a : A ≃* Sp (ZMod 2) :=
    (e.trans (pspFieldEquivZModTwo F hF)).trans EvenProjective.equiv.symm
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : P ≃* Q := a.subgroupMap (P : Subgroup A)
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr b]
  exact frattini_card_le Q

end Theory.SpecificGroups.SymplecticSix.BinarySylowFrattini
