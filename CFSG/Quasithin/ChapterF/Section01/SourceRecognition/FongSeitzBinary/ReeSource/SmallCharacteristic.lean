module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SmallCharacteristic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.MixedBounds

/-!
# Centralization of the small characteristic source subgroups

The natural panel markings supply (6.3), so the actual second Frattini
subgroup is centralized by the positive-parameter Suzuki actor, or by the
binary quintic mover. The same holds for the embedded Frattini subgroup of
[V,V]. Both field orders remain independent and the precise size inequality
is explicit. OriginalSmallCharacteristic transports the result through both
original endpoint markings and the literal quotient map.

Source: Fong--Seitz I (1973), pp.52--53, the effective-section restriction
in the proof of (6H)(b). The positive near-commutator equality, pairing,
odd degree and the remaining structural clauses still require proof.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include ν hC in
private theorem linear_root_card : Nat.card (simpleRoot Q split j) = Nat.card F := by
  rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)]

include ν hC in
/-- Both small characteristic subgroups centralize the whole positive Suzuki actor. -/
theorem source_positive_small_characteristic_centralizes
    (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card F)^4 < (2^(2*m+1))^6) :
    let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
    (secondFrattiniRadicalSection Q split i hV).numerator ≤
        centralizer (rankOne Q split i : Set (X ⧸ Q.D)) ∧
      (frattini (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))).map
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)).subtype ≤
        centralizer (rankOne Q split i : Set (X ⧸ Q.D)) := by
  dsimp only
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  have hfix := positive_secondFrattini_centralizes Q split i hV m μ hB hmpos hc hm j hij
    (source_six_three Q split i j m μ hB ν T hC hm hij).2
    (by rwa [linear_root_card Q split j ν T hC])
  exact ⟨hfix,(derived_frattini_le_secondFrattini Q split i hV).trans hfix⟩

include ν hC in
/-- In Sz(2), the literal quintic mover centralizes both small characteristic subgroups. -/
theorem source_binary_small_characteristic_centralizes
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j) (hsize : (Nat.card F)^4 < 64) :
    let hV := marked_suzuki_remainder_le_kernel Q split i 0 μ hB
    let C := centralizer ({(frattiniMover Q split i 0 μ hB : X ⧸ Q.D)} : Set (X ⧸ Q.D))
    (secondFrattiniRadicalSection Q split i hV).numerator ≤ C ∧
      (frattini (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))).map
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)).subtype ≤ C := by
  dsimp only
  let hV := marked_suzuki_remainder_le_kernel Q split i 0 μ hB
  have hfix := binary_secondFrattini_centralizes Q split i hV μ hB hc hm j hij
    (source_six_three Q split i j 0 μ hB ν T hC hm hij).2
    (by rwa [linear_root_card Q split j ν T hC])
  exact ⟨hfix,(derived_frattini_le_secondFrattini Q split i hV).trans hfix⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

