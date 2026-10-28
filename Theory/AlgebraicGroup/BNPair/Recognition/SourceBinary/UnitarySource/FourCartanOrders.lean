module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.RootCommutators
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FixedActionImage
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RankOneOrders
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.CoreAction

/-!
# The exact U4 source Cartan orders

The commuting-root clause of Fong--Seitz I (6A)(b) extends from the simple
root to its full root-generated actor: the same reflection preserves the
crossed root. Consequently that reflection centralizes the crossed root,
so its fixed Cartan factor maps onto the small faithful panel torus.
The small panel kernel therefore has order divisible by q-1. Together
with the small panel image this gives (q-1)^2 dividing |H|. The large
panel contributes q^2-1, and the trivial joint kernel bounds |H| by
(q^2-1)(q-1). Since q is even, gcd(q-1,q+1)=1, so equality follows.
Both literal Cartan kernels then have their exact source orders.

The natural faithful-panel markings supply their orders and reflection
inversion; no order, scalar-coordinate or tensor-realization assumption
remains in four_linear_cartan_cards. The earlier markings and commuting
clause remain inputs here. CartanOrderApplication supplies that clause
from the original elementary radical, and applies these orders to the
coefficient fields on the actual quotient. Both orientations, q=2 and
q=4 are retained. This is not full unitary source recognition.

Source: Fong--Seitz II (8.1)--(8.2), p.197, and the first paragraph of the
characteristic-two argument on p.201; I (6A)(b), pp.37--38.
-/

public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem rankOne_centralizes_cross_root (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hc : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = ⊥) :
    rankOne Q split i ≤ centralizer (rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) := by
  let s := actorReflection Q split i
  have hn : (s.val : X ⧸ Q.D) ∈ normalizer
      (rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) := by
    have he := cross_root_reflection_fixed Q split hm i j hij s.val s.class_eq
    apply mem_normalizer_iff.mpr
    intro x
    exact (SetLike.ext_iff.mp he x).symm
  have hU := commutator_eq_bot_iff_le_centralizer.mp hc
  rw [rankOne_eq Q split i s.val s.class_eq]
  apply sup_le hU
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  have hy' := (mem_normalizer_iff.mp hn y).mp hy
  change (s.val : X ⧸ Q.D)*x*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i at hx
  have he := mem_centralizer_iff.mp (hU hx) _ hy'
  apply (MulAut.conj (s.val : X ⧸ Q.D)).injective
  simpa only [map_mul, MulAut.conj_apply] using he

theorem coreCartan_card_eq_kernel (i : Fin 2) :
    Nat.card (coreCartan Q i) = Nat.card (cartanPanelMap Q i).ker := by
  rw [cartanPanelMap_kernel]
  exact (Nat.card_congr (subgroupOfEquivOfLe
    (show coreCartan Q i ≤ Q.tits.B ⊓ Q.tits.N from inf_le_left)).toEquiv).symm.trans
      (Nat.card_congr (MulEquiv.subgroupCongr (by
        ext x
        exact ⟨fun hx => hx.2, fun hx => ⟨x.property,hx⟩⟩)).toEquiv)

private theorem four_order_arithmetic {q h : ℕ} (hq : 1 < q) (he : Even q)
    (hupper : h ∣ (q^2-1)*(q-1)) (hsquare : (q-1)^2 ∣ h)
    (hlarge : q^2-1 ∣ h) : h = (q^2-1)*(q-1) := by
  have hf : q^2-1 = (q-1)*(q+1) := by
    have hs := Nat.sub_add_cancel (show 1 ≤ q from by omega)
    have ht := Nat.sub_add_cancel (show 1 ≤ q^2 from by nlinarith)
    nlinarith
  have hcop : Nat.Coprime (q-1) (q+1) := by
    rw [show q+1 = 2+(q-1) by omega, Nat.coprime_add_self_right]
    exact (Nat.Even.sub_odd (by omega) he odd_one).coprime_two_right
  have hd : q+1 ∣ h := (show q+1 ∣ q^2-1 from by rw [hf]; exact dvd_mul_left _ _).trans hlarge
  have hlo := (hcop.pow_left 2).mul_dvd_of_dvd_of_dvd hsquare hd
  have heq : (q-1)^2*(q+1) = (q^2-1)*(q-1) := by rw [hf]; ring
  exact Nat.dvd_antisymm hupper (heq ▸ hlo)

/-- The small commuting-root clause and the two faithful panel orders force
both Cartan-kernel orders. No coordinates or scalar-action equation are assumed. -/
theorem four_cartan_cards (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) {q : ℕ} (hq : 1 < q) (he : Even q)
    (hc : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = ⊥)
    (hcore : Q.tits.B.normalCore = ⊥)
    (hi : Nat.card (cartanPanelMap Q i).range = q-1)
    (hj : Nat.card (cartanPanelMap Q j).range = q^2-1)
    (hfix : reflectionFixed Q split i = (cartanPanelMap Q i).ker) :
    Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = (q^2-1)*(q-1) ∧
      Nat.card (coreCartan Q i) = q^2-1 ∧
      Nat.card (coreCartan Q j) = q-1 := by
  have hcentral := rankOne_centralizes_cross_root Q split hm i j hij hc
  have hd := rootAction_card_dvd_fixed Q split i i (Q.simple j)
    (actorReflection Q split i) (hcentral (actorReflection Q split i).mem_rankOne)
  rw [hfix,hi] at hd
  have hcounti := (cartanPanelMap Q i).ker.card_mul_index
  rw [index_ker,hi] at hcounti
  have hcountj := (cartanPanelMap Q j).ker.card_mul_index
  rw [index_ker,hj] at hcountj
  have hupper := cartan_card_dvd_product_images Q split (actorReflection Q split) hcore
  have hprod : Nat.card (cartanPanelMap Q 0).range * Nat.card (cartanPanelMap Q 1).range =
      (q^2-1)*(q-1) := by
    have hii : i = 0 ∨ i = 1 := by omega
    have hjj : j = 0 ∨ j = 1 := by omega
    rcases hii with rfl | rfl <;> rcases hjj with rfl | rfl
    · exact (hij rfl).elim
    · rw [hi,hj,Nat.mul_comm]
    · rw [hi,hj]
    · exact (hij rfl).elim
  rw [hprod] at hupper
  have hsquare : (q-1)^2 ∣ Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) := by
    rw [←hcounti,pow_two]
    exact Nat.mul_dvd_mul_right hd (q-1)
  have hlarge : q^2-1 ∣ Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) := by
    rw [←hcountj]
    exact dvd_mul_left _ _
  have hH := four_order_arithmetic hq he hupper hsquare hlarge
  refine ⟨hH,?_,?_⟩
  · rw [coreCartan_card_eq_kernel]
    apply Nat.eq_of_mul_eq_mul_right (show 0 < q-1 from by omega)
    exact hcounti.trans hH
  · rw [coreCartan_card_eq_kernel]
    apply Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt (one_lt_pow₀ hq (by decide : (2:ℕ) ≠ 0)))
    exact hcountj.trans (hH.trans (Nat.mul_comm _ _))

open BenderSuzuki.MatrixGroups
/-- Natural markings of the two faithful panels supply every image-order
and inversion premise of the U4 Cartan calculation, including q=2. -/
theorem four_linear_cartan_cards (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) (n : ℕ) (hn : 0 < n)
    (μi : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup n)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hBi : (quotientBorel Q i).map μi.toMonoidHom = normalizer (Ti : Set _))
    (μj : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup (2*n))
    (Tj : Sylow 2 (PSL2BinaryMatrixGroup (2*n)))
    (hBj : (quotientBorel Q j).map μj.toMonoidHom = normalizer (Tj : Set _))
    (hc : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = ⊥)
    (hcore : Q.tits.B.normalCore = ⊥) :
    Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = ((2^n)^2-1)*(2^n-1) ∧
      Nat.card (coreCartan Q i) = (2^n)^2-1 ∧
      Nat.card (coreCartan Q j) = 2^n-1 := by
  apply four_cartan_cards Q split hm i j hij (one_lt_pow₀ (by decide) hn.ne')
    (even_two.pow_of_ne_zero hn.ne') hc hcore
  · exact linear_cartanImage_card Q split i n hn μi Ti hBi (actorReflection Q split i)
  · have hh := linear_cartanImage_card Q split j (2*n) (by omega) μj Tj hBj (actorReflection Q split j)
    simpa only [pow_mul,Nat.mul_comm 2 n] using hh
  · exact linear_reflectionFixed_eq_kernel Q split i n μi Ti hBi (actorReflection Q split i)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
