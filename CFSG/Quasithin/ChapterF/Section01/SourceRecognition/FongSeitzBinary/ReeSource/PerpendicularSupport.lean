module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.InvariantRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PerpendicularObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositiveSixFourFactor

/-!
# Perpendicular root intersections with the actual derived radical

Cartan invariance makes any root intersection containing an order-four
element the entire Suzuki root. For positive parameters, each root Omega
is already in the derived radical. Thus every shifted root contained in
the radical meets its derived subgroup in either precisely Omega or the
whole root. In particular this applies to the perpendicular root on the
same octagonal quotient.

The proper-intersection branch gives the precise Omega support used in
Fong--Seitz I (1973), p.53. The source argument excluding the whole-root
branch is still required; no perpendicular noncontainment is inferred
from the previously proved cubic movement alone. OriginalPerpendicularSupport
transports the actual intersection through both endpoint orientations and Q.q.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i j : Fin 2)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include μ hB in
private theorem derived_cartan_normalizes :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer
      ((⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) : Set _) := by
  intro h hh
  have hv := remainder_parabolic_normalizes Q split i
    (marked_suzuki_remainder_le_kernel Q split i m μ hB)
    (Q.tits.B_le_standardParabolic _ hh.1)
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp hv]

include μ hB in
/-- A root in the actual radical has Omega intersection unless it is wholly derived. -/
theorem source_positive_derived_root_intersection (hmpos : 0 < m) (w : Weyl Q)
    (hA : rootAt Q split i w ≤ simpleRemainder Q split i)
    (hnot : ¬ rootAt Q split i w ≤ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆) :
    (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) ⊓
      rootAt Q split i w = omegaOneAmbient (rootAt Q split i w) := by
  apply le_antisymm
  · exact suzuki_rootAt_intersection_le_omega_of_not_le Q split i m μ hB w _
      (derived_cartan_normalizes Q split i m μ hB) hnot
  · exact le_inf (source_positive_omega_le_derived Q split i m μ hB hmpos w hA)
      (omegaOneAmbient_le _)

include μ hB in
/-- The perpendicular intersection has exactly two possible values. The whole-root
alternative is retained, pending the preceding p.53 source module argument. -/
theorem source_positive_perpendicular_derived_dichotomy
    (hmpos : 0 < m) (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    let D : Subgroup (X ⧸ Q.D) := ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆
    let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
    D ⊓ E = omegaOneAmbient E ∨ D ⊓ E = E := by
  dsimp only
  by_cases he : rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆
  · exact Or.inr (inf_eq_right.mpr he)
  · exact Or.inl (source_positive_derived_root_intersection Q split i m μ hB hmpos _
      (octagon_three_roots_le_remainder Q split hm i j hij).2.2 he)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
