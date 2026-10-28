module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourCartanOrders
public import Mathlib.Data.Nat.GCD.Basic

/-!
# Commuting quadrangle roots force divisibility of the field degrees

If a simple root commutes with its crossed root of the same type, its
whole rank-one actor centralizes that crossed root. The reflection-fixed
part of the Cartan therefore maps onto the root's Cartan action. For a
linear panel this fixed subgroup is the panel kernel. The opposite
panel is faithful on that kernel, because the whole Borel has trivial
normal core. Consequently the first Cartan image order divides the second.

Full linear panel markings identify these orders with 2^m-1 and 2^n-1.
The elementary Mersenne remainder identity then gives m dividing n.
This uses the actual two panel maps and the full Borel on the same quotient;
it does not assume a relation between the field orders. The source
UnequalOrderRecognition adapter combines this divisibility with the
unequal-radical bound to obtain the exact quadratic ratio, including m=1.

Source: Fong--Seitz I (6A)(b), II (8.1)--(8.2); DGS, Groups and
Graphs (1985), (11.6)--(11.7), pp.173--175.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The commuting-root clause forces divisibility between the actual Cartan image orders. -/
theorem commuting_cartan_image_dvd_other (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hc : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = ⊥)
    (hcore : Q.tits.B.normalCore = ⊥)
    (hfix : reflectionFixed Q split i = (cartanPanelMap Q i).ker) :
    Nat.card (cartanPanelMap Q i).range ∣ Nat.card (cartanPanelMap Q j).range := by
  have hcentral := rankOne_centralizes_cross_root Q split hm i j hij hc
  have hd := rootAction_card_dvd_fixed Q split i i (Q.simple j)
    (actorReflection Q split i) (hcentral (actorReflection Q split i).mem_rankOne)
  rw [hfix] at hd
  exact hd.trans (panelKernel_card_dvd_other Q split i j hij (actorReflection Q split) hcore)

private theorem binary_degree_dvd {m n : ℕ} (h : 2^m-1 ∣ 2^n-1) : m ∣ n := by
  have he := Nat.mod_eq_zero_of_dvd h
  rw [Nat.pow_sub_one_mod_pow_sub_one] at he
  have hh : 2^(n % m) ≤ 2^0 := by omega
  have hz := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  exact Nat.dvd_of_mod_eq_zero (by omega)

/-- Full linear panels and the commuting crossed roots force divisibility of their binary degrees. -/
theorem linear_commuting_field_degree_dvd (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) (m n : ℕ) (hmpos : 0 < m) (hnpos : 0 < n)
    (μi : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup m)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup m))
    (hBi : (quotientBorel Q i).map μi.toMonoidHom = normalizer (Ti : Set _))
    (μj : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (Tj : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hBj : (quotientBorel Q j).map μj.toMonoidHom = normalizer (Tj : Set _))
    (hc : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = ⊥)
    (hcore : Q.tits.B.normalCore = ⊥) : m ∣ n := by
  have hd := commuting_cartan_image_dvd_other Q split hm i j hij hc hcore
    (linear_reflectionFixed_eq_kernel Q split i m μi Ti hBi (actorReflection Q split i))
  rw [linear_cartanImage_card Q split i m hmpos μi Ti hBi (actorReflection Q split i),
    linear_cartanImage_card Q split j n hnpos μj Tj hBj (actorReflection Q split j)] at hd
  exact binary_degree_dvd hd

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
