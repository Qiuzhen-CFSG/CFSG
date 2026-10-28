module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryWeights
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiConstituentKernels
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.LinearPairCartan
public import Theory.GroupAction.AbelianIrreducibleOrder

/-!
# Cartan divisibility for an odd linear degree opposite a unitary root

The full Cartan acts irreducibly on the unitary Frattini quotient of order
2^(2b). Abelianness and faithful coprime Frattini action make its root-action
image have order dividing 2^(2b)-1. If the opposite linear degree is odd,
the perpendicular reflection centralizes that linear root. The fixed
Cartan factor then maps onto its Singer image, and joint panel faithfulness
embeds it into the unitary image. Thus 2^a-1 divides 2^(2b)-1.

Source: Fong--Seitz I (6F), pp.45--46. The original-factor application is
LinearUnitaryParity in CFSG; the reverse degree divisibility is separate.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The full unitary panel Cartan image divides the quadratic field-unit order. -/
theorem unitary_cartan_image_card_dvd {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x : F, J.conj x = x^(2^n))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Nat.card (cartanPanelMap Q j).range ∣ 2^(2*n)-1 := by
  let := split.abelian
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨e⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hcard hf
  obtain ⟨hirr,_⟩ := unitary_rootAt_cartan_frattini_irreducible Q split J₀ hn hcard hf rfl
    j (μj.trans e) hKj 1
  let τ := rootAtCartanFrattiniRepresentation Q split j 1
  let ρ := rootAtCartanFrattiniAction Q split j 1
  let : τ.IsIrreducible := hirr
  have hd := Theory.GroupAction.abelian_irreducible_image_card_dvd ρ τ (by intros; rfl)
  rw [unitary_rootAt_frattini_card Q split J₀ hn hcard hf rfl j (μj.trans e) hKj 1] at hd
  have hker : ρ.ker = (rootAction Q split j 1).ker := by
    rw [←rootAtCartanFrattiniRepresentation_kernel Q split j 1]
    ext h
    constructor
    · intro hh
      change τ h = 1
      ext a
      change Additive.ofMul (ρ h a.toMul) = a
      rw [show ρ h = 1 from hh]
      rfl
    · intro hh
      change ρ h = 1
      ext a
      exact congrArg Additive.toMul (DFunLike.congr_fun hh (Additive.ofMul a))
  let he := (QuotientGroup.quotientKerEquivRange ρ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivRange (rootAction Q split j 1)))
  rw [Nat.card_congr he.toEquiv,Nat.card_congr (rootActionImageEquiv Q split j 1).toEquiv] at hd
  exact hd

/-- Odd linear degree gives the literal perpendicular-root divisibility. -/
theorem linear_unitary_odd_cartan_dvd {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {a b : ℕ} (hb : 2 ≤ b) (hcard : Nat.card F = (2^b)^2)
    (hconj : ∀ x : F, J.conj x = x^(2^b))
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) (ha : Odd a)
    (μi : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup a)
    (Ti : Sylow 2 (PSL2BinaryMatrixGroup a))
    (hBi : (quotientBorel Q i).map μi.toMonoidHom = normalizer (Ti : Set _))
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hE : IsElementaryAbelian 2 (simpleRoot Q split i))
    (hroot : Nat.card (simpleRoot Q split i) = 2^a)
    (s : ∀ k, HexagonStructure.RootReflection Q split k) (hcore : Q.tits.B.normalCore = ⊥) :
    2^a-1 ∣ 2^(2*b)-1 := by
  have hc := linear_perpendicular_centralizes Q split hm i j hij a ha μi Ti hBi hE hroot (s i)
  have hd := rootAction_card_dvd_fixed Q split i i (Q.simple j*Q.simple i*Q.simple j)
    (involutoryRootReflection Q split i (s i)) hc
  rw [linear_reflectionFixed_eq_kernel Q split i a μi Ti hBi (s i)] at hd
  have hdiv := hd.trans (panelKernel_card_dvd_other Q split i j hij s hcore)
  rw [linear_cartanImage_card Q split i a ha.pos μi Ti hBi (s i)] at hdiv
  exact hdiv.trans (unitary_cartan_image_card_dvd Q split J hb hcard hconj j hKj μj)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
