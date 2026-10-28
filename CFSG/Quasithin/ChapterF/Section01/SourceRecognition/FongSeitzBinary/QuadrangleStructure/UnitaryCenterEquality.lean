module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.CenterIrreducibility
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitarySpecialRadical

/-!
# The original U5 center commutator and special radical

DGS (11.8)(f) supplies specialness of the original beta radical; the
original linear Sylow quotient makes the opposite root elementary.
The same endpoint/core marking transports these inputs to the literal
complementary section. The faithful unitary local marking now supplies
the inverse-norm action, turning the previously proved nonzero inclusion
into the exact crossed-root center equality of Fong--Seitz I (6A)(c).
That commutator is also the beta radical's full derived, Frattini and
center layer, as actual embedded subgroups of the same finite quotient.

The theorem works for either orientation and any genuine amalgam mark,
including the independent geometric completion. Its original quotient
specialization keeps the original endpoint squares and full overlap.
The faithful local marking is the earlier section 5 catalogue transport;
it is not an identification of the full actor with PSU3. The full SU3
actor, the other exact mixed commutator and the remaining U5 section
actions still require their structural proofs. No later Hermitian
realization is assumed here.

Source: DGS (11.5), (11.8), pp.172--176;
Fong--Seitz I (3G), (5C), (6A)(c), pp.14--16,26,37.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- The actual original special radical gives the full center-side mixed commutator. -/
theorem marked_unitary_center_commutator
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (center (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype := by
  obtain ⟨hd,hf,hz,_,_⟩ := marked_unitary_special_radical Q e h split hm i j hij
    hVi hVj hQi hderived hfrattini
  let := marked_simpleRoot_elementary_of_original_quotient Q e h split i hVi hQi
  have hc := Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.unitary_cross_root_commutator_eq_center
    Q split J hn hcard hfixed hJ hm i j hij hVi hVj μ
    (commutator_self_eq_bot_iff.mpr inferInstance) (hz.trans hd.symm).le
  exact ⟨hc,hc.trans hd.symm,hc.trans hf.symm,hc.trans hz.symm⟩

include h in
omit Q e split in
/-- The exact center equality on the original SourceQuotient, with either endpoint orientation. -/
theorem original_unitary_center_commutator
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q₀ = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (μ : localGroup Q₀ split₀ j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ =
        (center (rootAt Q₀ split₀ j (Q₀.simple i))).map (rootAt Q₀ split₀ j (Q₀.simple i)).subtype ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ =
        ⁅simpleRemainder Q₀ split₀ j,simpleRemainder Q₀ split₀ j⁆ ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ =
        (frattini (simpleRemainder Q₀ split₀ j)).map (simpleRemainder Q₀ split₀ j).subtype ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ =
        (center (simpleRemainder Q₀ split₀ j)).map (simpleRemainder Q₀ split₀ j).subtype :=
  marked_unitary_center_commutator Q₀ (originalMarkedIso Q₀) h split₀ J hn hcard hfixed hJ
    hm i j hij hVi hVj μ hQi hderived hfrattini

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
