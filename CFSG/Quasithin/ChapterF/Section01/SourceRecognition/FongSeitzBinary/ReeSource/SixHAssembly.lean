module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10Centers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10Near
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10Perpendicular

/-!
# Constructing the source (6H) input for Section 10

All literal relations (10.2)--(10.3), including the ordered derived
product and both full centers, are supplied by the source proofs at every
N-conjugate. Together with the proved common field and Cartan clauses,
they construct ReeSixHData on the same quotient. No relation or center
certificate remains an input. Natural panel markings and odd linear
degree are still the preceding family-selection premises; that earlier arithmetic restriction
remains with the independent polygon-square work.

Source: Fong--Seitz I (1973), (6H), pp.51--56;
II (1974), the input to Section 10, pp.221--222.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

include ν hC μ hB hn in
/-- All literal source relations, with no remaining commutator or center premise. -/
theorem sourceSixHRelations
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    SixHRelations Q split where
  ten_two_i := source_ten_two_i Q split n hn m ν T hC μ hB hc hm hcore
  ten_two_ii_left w := (source_ten_two_ii Q split n hn m ν T hC μ hB hc hm hcore w).1
  ten_two_ii_right w := (source_ten_two_ii Q split n hn m ν T hC μ hB hc hm hcore w).2
  ten_two_iii_left w := (source_ten_two_iii Q split n hn m ν T hC μ hB hc hm hcore w).1
  ten_two_iii_right w := (source_ten_two_iii Q split n hn m ν T hC μ hB hc hm hcore w).2
  ten_two_iv_left := source_ten_two_iv_left Q split n hn m ν T hC μ hB hc hm hcore
  ten_two_iv_right := source_ten_two_iv_right Q split n hn m ν T hC μ hB hc hm hcore
  ten_two_v w := (source_ten_two_v_eq Q split n hn m ν T hC μ hB hc hm hcore w).le
  ten_three_frattini := source_ten_three_frattini Q split n hn m ν T hC μ hB hc hm hcore
  ten_three_product := source_ten_three_product Q split n hn m ν T hC μ hB hc hm hcore
  ten_three_frattini_square := source_ten_three_frattini_square Q split n hn m ν T hC μ hB hc hm hcore
  ten_three_center := source_ten_three_center_commutator Q split n hn m ν T hC μ hB hc hm hcore
  ten_three_center_remainder := source_ten_three_center_remainder Q split n hn m ν T hC μ hB hc hm hcore
  ten_three_center_unipotent := source_ten_three_center_unipotent Q split n hn m ν T hC μ hB hc hm hcore

/-- The genuine Section 10 input constructed from naturally marked source panels. -/
def sourceReeSixHData
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ReeSixHData Q split n m where
  rotation_eight := hm
  linear_degree_odd := hn
  linear := ν
  linearSylow := T
  linearBorel := hC
  suzuki := μ
  suzukiBorel := hB
  reflections := UnitarySource.actorReflection Q split
  common_field := ree_common_field_exponent Q split hm n hn m ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  hcore := hcore
  cartan_card := ree_cartan_card Q split hm n hn m ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  independent_root_centralizer := sixH_joint_simpleRoot_centralizer_eq_bot Q split
    (UnitarySource.actorReflection Q split) hcore
  panel_kernel_centralizer := sixH_panelKernel_centralizes_rankOne Q split
  relations := sourceSixHRelations Q split n hn m ν T hC μ hB hm hcore hc

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
