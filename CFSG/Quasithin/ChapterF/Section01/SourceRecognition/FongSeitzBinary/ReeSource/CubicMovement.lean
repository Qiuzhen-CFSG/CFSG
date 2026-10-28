module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CubicMovement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.MixedBounds

/-!
# Source cubic commutator movement from the natural panel markings

The marked linear and Suzuki panels supply (6.3) and the actual two root
orders. The positive Suzuki cubic-movement theorem therefore applies to
both the radical and its derived subgroup. In particular the third
commutator of the radical with the simple Suzuki root is not contained
in the derived radical. This is the source movement used on printed p.53
to exclude a trivial perpendicular contribution under the near-zero
assumption.

The independent-field size comparison remains explicit. No odd linear
degree, field equality, perpendicular support, or (6H) conclusion is
assumed. OriginalCubicMovement transports the actual witnesses to both
original endpoints and the literal quotient Q.q.

Source: Fong--Seitz I (1973), pp.52--53, proof of (6H)(b).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
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
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include ν hC μ hB in
/-- The literal marked root has cubic movement on V/Phi(V), with (6.3) discharged. -/
theorem source_positive_radical_cubic_movement (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j) (hsize : Nat.card F ≤ 2^(2*m+1)) :
    let u := (suzukiParameter Q split i m μ hB 1 0 : X ⧸ Q.D)
    ∃ v : simpleRemainder Q split i, ⁅u,⁅u,⁅u,(v : X ⧸ Q.D)⁆⁆⁆ ∉
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype := by
  apply positive_radical_cubic_movement Q split i m μ hB
    (marked_suzuki_remainder_le_kernel Q split i m μ hB) hc hm j hij hmpos
    (source_six_three Q split i j m μ hB ν T hC hm hij).2
  rwa [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)]

include ν hC μ hB in
/-- Cubic movement also survives in the actual derived radical modulo its Frattini subgroup. -/
theorem source_positive_derived_cubic_movement (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j) (hsize : Nat.card F ≤ 2^(2*m+1)) :
    let D : Subgroup (X ⧸ Q.D) := ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆
    let u := (suzukiParameter Q split i m μ hB 1 0 : X ⧸ Q.D)
    ∃ v : D, ⁅u,⁅u,⁅u,(v : X ⧸ Q.D)⁆⁆⁆ ∉ (frattini D).map D.subtype := by
  apply positive_derived_cubic_movement Q split i m μ hB
    (marked_suzuki_remainder_le_kernel Q split i m μ hB) hc hm j hij hmpos
  rwa [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)]

include ν hC μ hB in
/-- The p.53 triple commutator survives even modulo the derived radical. -/
theorem source_positive_third_commutator_not_le_derived (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j) (hsize : Nat.card F ≤ 2^(2*m+1)) :
    ¬ ⁅simpleRoot Q split i,⁅simpleRoot Q split i,⁅simpleRoot Q split i,
      simpleRemainder Q split i⁆⁆⁆ ≤ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ := by
  obtain ⟨v,hv⟩ := source_positive_radical_cubic_movement Q split i j ν T hC m μ hB
    hmpos hc hm hij hsize
  intro h
  apply hv
  let V := simpleRemainder Q split i
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hD : ⁅V,V⁆ ≤ (frattini V).map V.subtype := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  apply hD
  apply h
  exact commutator_mem_commutator (suzukiParameter Q split i m μ hB 1 0).property
    (commutator_mem_commutator (suzukiParameter Q split i m μ hB 1 0).property
      (commutator_mem_commutator (suzukiParameter Q split i m μ hB 1 0).property v.property))

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
