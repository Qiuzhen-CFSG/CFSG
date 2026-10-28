module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.EffectiveRadical
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.CoreAction
public import Theory.Representation.Suzuki.BinaryDegree
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# The Suzuki lower bound on the actual radical Frattini section

The full endpoint action on V/Φ(V), for V = U ∩ U^s, has kernel V.
Since V lies in the panel kernel, the order of the naturally marked Suzuki
panel quotient divides the order of this actual action image. A primitive
prime of binary order 4(2m+1) then forces dimension at least 4(2m+1).
At m=0 the prime five gives the same bound. The representation is on the
literal source section; no natural-module identification or simplicity of
the unknown source group is assumed.

This supplies the first effective-module size estimate used on printed p.52
in Fong--Seitz I (1973), proof of (6H). It uses the stronger original
F.1.1 local-characteristic-two hypothesis, discharged in OriginalEffectiveRadical.
The octagon order formula also bounds Φ(V), retaining the other root order
independently. It does not establish effectivity on the derived radical, the centralizer bounds
(6.1), or the subsequent nonzero mixed-commutator equality. The two rank-one
fields remain independent.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

/-- The image of the whole endpoint acts on this very Frattini section. -/
def endpointImageRepresentation : Representation (ZMod 2)
    (endpointFrattiniAction Q split i hV).range (UnitarySource.CoreSpace Q split i) where
  toFun g := g.val.toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

theorem endpointImageRepresentation_injective :
    Function.Injective (endpointImageRepresentation Q split i hV) := by
  intro g h he
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  exact Additive.ofMul.injective (congrArg
    (fun f : Module.End (ZMod 2) (UnitarySource.CoreSpace Q split i) =>
      f (Additive.ofMul x)) he)

variable (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤
  pCore 2 (Endpoint Q i))
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)

include hV hc μ in
theorem suzuki_card_dvd_endpoint_image :
    Nat.card (SuzukiMatrixGroup m) ∣ Nat.card (endpointFrattiniAction Q split i hV).range := by
  have hle : (endpointFrattiniAction Q split i hV).ker ≤ panelKernel Q i := by
    rw [endpointFrattiniAction_ker Q split i hV hc]
    intro g hg
    have hk : g ∈ (localKernel Q i).subgroupOf (Endpoint Q i) := hV hg
    rw [localKernel_subgroupOf] at hk
    exact hk
  rw [← Nat.card_congr μ.toEquiv]
  change (panelKernel Q i).index ∣ _
  rw [← index_ker]
  exact index_dvd_of_le hle

include hV hc μ in
/-- The first degree bound of (6H), on the actual radical Frattini quotient.
The order-five argument covers m=0 without simplicity. -/
theorem suzuki_radical_frattini_finrank_ge :
    4*(2*m+1) ≤ Module.finrank (ZMod 2) (UnitarySource.CoreSpace Q split i) := by
  let ρ := endpointImageRepresentation Q split i hV
  have hf := endpointImageRepresentation_injective Q split i hV
  have hd := suzuki_card_dvd_endpoint_image Q split i hV hc m μ
  by_cases hm : m = 0
  · subst m
    have h5 : 5 ∣ Nat.card (endpointFrattiniAction Q split i hV).range := by
      apply dvd_trans (show 5 ∣ Nat.card (SuzukiMatrixGroup 0) from by rw [suzukiZero_card]; decide) hd
    have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hf
      (by decide : Nat.Prime 5) (by decide : 5 ≠ 2) h5
    simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five, Nat.mul_zero,
      Nat.zero_add, Nat.mul_one] using hh
  · obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul_odd
      (n := 2*m+1) ⟨m,rfl⟩ (by omega)
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      rw [show (2 : ZMod 2) = 0 by decide, orderOf_zero] at ho
      omega
    have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hf hp hp2
      ((Representation.Suzuki.prime_dvd_card_of_orderOf_two (by omega) hp ho).trans hd)
    rwa [ho] at hh

include hV hc μ in
theorem suzuki_radical_frattini_card_ge :
    (2^(2*m+1))^4 ≤ Nat.card
      ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) := by
  have hd := suzuki_radical_frattini_finrank_ge Q split i hV hc m μ
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := UnitarySource.CoreSpace Q split i)
  rw [Nat.card_zmod] at he
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hd
  rw [← he] at hh
  simpa only [pow_mul, Nat.mul_comm 4 (2*m+1),
    Nat.card_congr (Additive.toMul : UnitarySource.CoreSpace Q split i ≃ _)] using hh

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource


@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i j : Fin 2)

private theorem octagon_remainder_card (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    Nat.card (simpleRemainder Q split i) =
      Nat.card (simpleRoot Q split i)^3 * Nat.card (simpleRoot Q split j)^4 := by
  have hu := unipotent_card_even Q split 4 hm
  have he : Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1) =
      Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j) := by
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | rfl | exact Nat.mul_comm _ _
  rw [he, unipotent_card_simple Q split i] at hu
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := simpleRoot Q split i))
  calc
    Nat.card (simpleRoot Q split i) * Nat.card (simpleRemainder Q split i) =
        (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))^4 := hu
    _ = Nat.card (simpleRoot Q split i) *
        (Nat.card (simpleRoot Q split i)^3 * Nat.card (simpleRoot Q split j)^4) := by ring

variable (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include μ hB in
theorem suzuki_octagon_radical_card (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    Nat.card (simpleRemainder Q split i) =
      (2^(2*m+1))^6 * Nat.card (simpleRoot Q split j)^4 := by
  rw [octagon_remainder_card Q split i j hm hij,
    Nat.card_congr (suzukiRootEquiv Q split i m μ hB).toEquiv, matrixRoot_card,
    ← pow_mul]

variable (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))

include hV hc μ hB in
/-- The q^4 effective quotient bounds the actual Frattini subgroup before field synchronization. -/
theorem suzuki_radical_frattini_card_le (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    Nat.card (frattini (simpleRemainder Q split i)) ≤
      (2^(2*m+1))^2 * Nat.card (simpleRoot Q split j)^4 := by
  let R := simpleRemainder Q split i
  have hl := suzuki_radical_frattini_card_ge Q split i hV hc m μ
  have he := (frattini R).card_mul_index
  change Nat.card (frattini R) * Nat.card (R ⧸ frattini R) = Nat.card R at he
  have hm' : Nat.card (frattini R) * (2^(2*m+1))^4 ≤
      ((2^(2*m+1))^2 * Nat.card (simpleRoot Q split j)^4) * (2^(2*m+1))^4 := by
    calc
      _ ≤ Nat.card (frattini R) * Nat.card (R ⧸ frattini R) := Nat.mul_le_mul_left _ hl
      _ = Nat.card R := he
      _ = _ := by rw [suzuki_octagon_radical_card Q split i j m μ hB hm hij]; ring
  exact Nat.le_of_mul_le_mul_right hm' (by positivity)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
