module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalStructure
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SourceSection10Basis
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# Genuine (6H) and original core structure in the selected Chapter 12 branch

For the actual selected factor and Preparation, the proved local-pair
reduction supplies Hypothesis F.1.1. The source constructor then produces
ReeSixHData from the naturally marked panels, with every center, derived
product and commutator field discharged. The intrinsic original center and
Frattini identities apply to that same pair, and the independent Section 10
basis retains both original endpoint squares. No (6H) bundle, center bound,
module identification or presentation equations are assumed.

The original full KnownSimple/Hypothesis1221 and Preparation hypotheses are
retained. Family pairing and odd degree remain the earlier inputs; the
remaining Section 10 equations and full marked comparison are separate.
Source: Fong--Seitz I (6H), pp.51--56; II (10.6), pp.222--223;
Aschbacher--Smith, Chapter 12, Section 2.
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
    (hnOdd : Odd n)
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

/-- Construct every (6H) field for the actual selected source pair. -/
def rankOneReeSixHData : ReeSixHData Q split n m :=
  originalSourceReeSixHData Q e
    (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
    split hm n hnOdd m μ₀ T₀ hB₀ μ₁ hB₁

include D h hmany hn hpsl hH preparation Q split hm e hnOdd μ₀ T₀ hB₀ μ₁ hB₁ in
/-- The complete intrinsic derived and center identities on the original second two-core. -/
theorem rankOne_ree_intrinsic_structure :
    let U := Global.sourceS L H
    let J := ChapterF.Source.parabolic ![L,R] U 1
    let K := pCore 2 J
    (center U).map U.subtype = (center K).map (J.subtype.comp K.subtype) ∧
      ⁅frattini K,(⊤ : Subgroup K)⁆ = center K ∧
      frattini K = _root_.commutator K ∧
      (IsElementaryAbelian 2 (frattini K) ∧ Nat.card (frattini K) = (2^(2*m+1))^5) ∧
      (IsElementaryAbelian 2 (center K) ∧ Nat.card (center K) = 2^(2*m+1)) := by
  let hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1
  let c := D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e hnOdd μ₀ T₀ hB₀ μ₁ hB₁
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

local instance chapter12SourceBasisBinaryAlgebra :
    Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

/-- Both endpoint inclusion squares for the actual selected pair's printed Section 10 basis. -/
theorem rankOne_ree_source_basis_endpoints (j : Fin 2) :
    let c := D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e hnOdd μ₀ T₀ hB₀ μ₁ hB₁
    ∀ i : Fin 2, ∃ hi : ((originalV1BasisPoint Q e split c j).val.val : G) ∈
        ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i,
      MarkedLocal.endpointMap Q e i ⟨(originalV1BasisPoint Q e split c j).val.val,hi⟩ =
        (V1BasisPoint Q split c j : X ⧸ Q.D) ∧
      originalV1BasisCoordinates Q e split c
        (Additive.ofMul (QuotientGroup.mk (originalV1BasisPoint Q e split c j))) =
        ![![0,1],![1,0]] j :=
  originalV1BasisPoint_endpoints Q e split
    (D.rankOneReeSixHData h hmany hn hpsl hH preparation Q split hm m e hnOdd μ₀ T₀ hB₀ μ₁ hB₁)
    (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH preparation).1 j

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
