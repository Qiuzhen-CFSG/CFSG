module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FixedActionImage
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanCyclic
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OctagonRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.OctagonDegrees
public import Theory.ElementaryAbelian.Injective

/-!
# Linear octagon degrees detected by the actual Cartan actions

The Feit--Higman square condition makes the two binary root degrees have
opposite parity. The reflection on a perpendicular elementary root of odd
degree centralizes it: its cyclic Cartan image is a Singer group, whose
involutory normalizer cannot move a root of odd dimension. The fixed Cartan
factor therefore surjects onto that root image. Its identification with the
panel kernel and faithfulness of the other panel force a divisibility of
field-unit orders, and hence of the binary degrees.

These are the initial reductions in Fong--Seitz I (6G), printed p.49.
LinearPairDegrees in CFSG supplies the elementary structure and root orders
from the actual two natural panel markings. This module does not assert the
subsequent centralizer or terminal exclusion arguments of (6G).
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure (rootAt rootAt_torus_normalizes)
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

private theorem degree_dvd {a b : ℕ} (h : 2^a-1 ∣ 2^b-1) : a ∣ b := by
  have he := Nat.mod_eq_zero_of_dvd h
  rw [Nat.pow_sub_one_mod_pow_sub_one] at he
  have hh : 2^(b % a) ≤ 2^0 := by omega
  have hz := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  exact Nat.dvd_of_mod_eq_zero (by omega)

private theorem square_exponent_even {n : ℕ} (h : IsSquare (2^n)) : Even n := by
  obtain ⟨k,hk⟩ := h
  have hp := Nat.BinaryTorusParity.two_pow_mod_three n
  have hs := congrArg (fun x : ℕ => x % 3) hk
  rw [Nat.mul_mod] at hs
  have hn : n % 2 = 0 := by
    by_contra hn
    rw [if_neg hn] at hp
    rw [hp] at hs
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with hk3 | hk3 | hk3 <;> norm_num [hk3] at hs
  exact Nat.even_iff.mpr hn

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The actual octagonal root orders have opposite binary-degree parity. -/
theorem linear_pair_degree_parity (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) {a b : ℕ}
    (hi : Nat.card (simpleRoot Q split i) = 2^a)
    (hj : Nat.card (simpleRoot Q split j) = 2^b) :
    (Odd a ∧ Even b) ∨ (Even a ∧ Odd b) := by
  have hs := octagon_twice_root_product_isSquare_of_ne Q split hm i j hij
  rw [hi,hj] at hs
  have he : 2 * 2^a * 2^b = 2^(1+a+b) := by
    rw [pow_add,pow_add,pow_one]
  rw [he] at hs
  have hp := Nat.even_iff.mp (square_exponent_even hs)
  rcases Nat.even_or_odd a with ha | ha
  · right
    exact ⟨ha,Nat.odd_iff.mpr (by have hh := Nat.even_iff.mp ha; omega)⟩
  · left
    exact ⟨ha,Nat.even_iff.mpr (by have hh := Nat.odd_iff.mp ha; omega)⟩

/-- An odd-dimensional linear root is centralized by the actual perpendicular reflection. -/
theorem linear_perpendicular_centralizes (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (a : ℕ) (ha : Odd a)
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup a)
    (T : Sylow 2 (PSL2BinaryMatrixGroup a))
    (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set _))
    (hE : IsElementaryAbelian 2 (simpleRoot Q split i))
    (hcard : Nat.card (simpleRoot Q split i) = 2^a)
    (s : RootReflection Q split i) :
    ((involutoryRootReflection Q split i s).val : X ⧸ Q.D) ∈
      centralizer (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  let w := Q.simple j*Q.simple i*Q.simple j
  let r := involutoryRootReflection Q split i s
  let e := RootAction.conjugateEquiv (simpleRoot Q split i) (representative w)
  let := hE
  let : IsElementaryAbelian 2 (rootAt Q split i w) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  let : IsCyclic (RootAction.action (Q.tits.B ⊓ Q.tits.N)
      (rootAt Q split i w) (rootAt_torus_normalizes Q split i w)).range :=
    (rootActionImageEquiv Q split i w).isCyclic.mpr
      (linear_cartanImage_cyclic Q split i a ha.pos μ T hB s)
  apply RootAction.normalizing_involution_centralizes (Q.tits.B ⊓ Q.tits.N)
    (rootAt Q split i w) (rootAt_torus_normalizes Q split i w) ha
  · change Nat.card (rootAction Q split i w).range = _
    rw [Nat.card_congr (rootActionImageEquiv Q split i w).toEquiv]
    exact linear_cartanImage_card Q split i a ha.pos μ T hB s
  · exact (Nat.card_congr e.toEquiv).trans hcard
  · exact perpendicular_root_normalizes Q split hm i j hij r.val r.class_eq
  · exact torus_normalizes r.val
  · exact involutoryRootReflection_sq Q split i s

/-- The odd endpoint degree divides the other degree through the literal Cartan panel maps. -/
theorem linear_pair_odd_degree_dvd (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (a b : ℕ) (ha : Odd a) (hb : 0 < b)
    (μi : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup a)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup a))
    (hBi : (quotientBorel Q i).map μi.toMonoidHom = normalizer (Ti : Set _))
    (μj : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup b)
    (Tj : Sylow 2 (PSL2BinaryMatrixGroup b))
    (hBj : (quotientBorel Q j).map μj.toMonoidHom = normalizer (Tj : Set _))
    (hE : IsElementaryAbelian 2 (simpleRoot Q split i))
    (hcard : Nat.card (simpleRoot Q split i) = 2^a)
    (s : ∀ k, RootReflection Q split k) (hcore : Q.tits.B.normalCore = ⊥) : a ∣ b := by
  have hc := linear_perpendicular_centralizes Q split hm i j hij a ha μi Ti hBi hE hcard (s i)
  have hd := rootAction_card_dvd_fixed Q split i i (Q.simple j*Q.simple i*Q.simple j)
    (involutoryRootReflection Q split i (s i)) hc
  rw [linear_reflectionFixed_eq_kernel Q split i a μi Ti hBi (s i)] at hd
  have hdiv := hd.trans (panelKernel_card_dvd_other Q split i j hij s hcore)
  rw [linear_cartanImage_card Q split i a ha.pos μi Ti hBi (s i),
    linear_cartanImage_card Q split j b hb μj Tj hBj (s j)] at hdiv
  exact degree_dvd hdiv

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
