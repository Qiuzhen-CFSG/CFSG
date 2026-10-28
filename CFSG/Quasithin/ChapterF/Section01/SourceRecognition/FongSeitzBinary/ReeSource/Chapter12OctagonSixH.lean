module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Chapter12SixH
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OctagonSixH

/-!
# Chapter 12 `(6H)` data from the octagonal source

The selected Chapter 12 branch already supplies the full local-pair,
`KnownSimple`, `Preparation`, endpoint and Borel hypotheses.  The octagon
theorem discharges the remaining odd-degree premise, so the existing
intrinsic and endpoint consumers can be applied without adding it as an
independent input.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.ReeSource
open ChapterF.Source.FongSeitzBinary.ReeSection10

variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
variable
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (preparation : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : RootCoordinates.rotationOrder Q = 8) (m : ℕ)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam)
    (μ₀ : (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⧸
      originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 0) ≃*
        BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup n)
    (T₀ : Sylow 2 (BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup n))
    (hB₀ : (originalFaithfulBorel (L := ![L,R]) (S := Global.sourceS L H) 0).map
      μ₀.toMonoidHom = normalizer (T₀ : Set _))
    (μ₁ : (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1 ⧸
      originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hB₁ : (originalFaithfulBorel (L := ![L,R]) (S := Global.sourceS L H) 1).map
      μ₁.toMonoidHom = normalizer (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m : Set _))

/-- Construct the selected Chapter 12 `(6H)` data using octagon oddness. -/
def rankOneReeSixHData_of_octagon : ReeSixHData Q split n m := by
  let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
  exact originalSourceReeSixHData_of_octagon Q e hf split hm n
    (Nat.zero_lt_of_lt hn) m μ₀ T₀ hB₀ μ₁ hB₁

include D h hmany hn hpsl hH preparation Q split hm e μ₀ T₀ hB₀ μ₁ hB₁ in
/-- The intrinsic center and Frattini identities for the octagon constructor. -/
theorem rankOne_ree_intrinsic_structure_of_octagon :
    let U := Global.sourceS L H
    let J := ChapterF.Source.parabolic ![L,R] U 1
    let K := pCore 2 J
    (center U).map U.subtype = (center K).map (J.subtype.comp K.subtype) ∧
      ⁅frattini K,(⊤ : Subgroup K)⁆ = center K ∧
      frattini K = _root_.commutator K ∧
      (IsElementaryAbelian 2 (frattini K) ∧ Nat.card (frattini K) = (2^(2*m+1))^5) ∧
      (IsElementaryAbelian 2 (center K) ∧ Nat.card (center K) = 2^(2*m+1)) := by
  let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
  let c := D.rankOneReeSixHData_of_octagon h hmany hn hpsl hH preparation
    Q split hm m e μ₀ T₀ hB₀ μ₁ hB₁
  exact ⟨original_source_sylow_center_eq_radical_center Q e split n c.linear_degree_odd m
      c.linear c.linearSylow c.linearBorel c.suzuki c.suzukiBorel hf hm,
    original_source_radical_third_eq_center Q e split n c.linear_degree_odd m
      c.linear c.linearSylow c.linearBorel c.suzuki c.suzukiBorel hf hm,
    original_source_radical_frattini_eq_commutator Q e split n c.linear_degree_odd m
      c.linear c.linearSylow c.linearBorel c.suzuki c.suzukiBorel hf hm,
    original_source_radical_frattini_data Q e split n c.linear_degree_odd m
      c.linear c.linearSylow c.linearBorel c.suzuki c.suzukiBorel hf hm,
    original_source_radical_center_data Q e split n c.linear_degree_odd m
      c.linear c.linearSylow c.linearBorel c.suzuki c.suzukiBorel hf hm⟩

local instance chapter12OctagonSourceBasisBinaryAlgebra :
    Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

include D h hmany hn hpsl hH preparation Q split hm e μ₀ T₀ hB₀ μ₁ hB₁ in
/-- Both endpoint inclusion squares for the octagon-selected Chapter 12 pair. -/
theorem rankOne_ree_source_basis_endpoints_of_octagon (j : Fin 2) :
    let c := D.rankOneReeSixHData_of_octagon h hmany hn hpsl hH preparation
      Q split hm m e μ₀ T₀ hB₀ μ₁ hB₁
    ∀ i : Fin 2, ∃ hi : ((originalV1BasisPoint Q e split c j).val.val : G) ∈
        ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i,
      MarkedLocal.endpointMap Q e i ⟨(originalV1BasisPoint Q e split c j).val.val,hi⟩ =
        (V1BasisPoint Q split c j : X ⧸ Q.D) ∧
      originalV1BasisCoordinates Q e split c
        (Additive.ofMul (QuotientGroup.mk (originalV1BasisPoint Q e split c j))) =
        ![![0,1],![1,0]] j := by
  let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
  exact originalV1BasisPoint_endpoints Q e split
    (D.rankOneReeSixHData_of_octagon h hmany hn hpsl hH preparation
      Q split hm m e μ₀ T₀ hB₀ μ₁ hB₁) hf j

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
