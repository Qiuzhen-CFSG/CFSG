module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.SuzukiExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SmallSuzuki
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OriginalActorQuotient

/-!
# Original quadrangle factors opposite a linear endpoint

The original quotient markings construct the actual SL2 and Suzuki
root actors, their canonical root isomorphisms and both kernel
containments. The two quadrangle degree estimates exclude every Suzuki
parameter, including zero. For D10 the actual full root actor is Sz(2),
so the same proof excludes that constructor as well.

Exhausting F.1.1 now leaves an actual original PSL2, PSU3 or SU3 quotient
at the opposite endpoint. These are model identifications, not numeric
row tags; scalar centers, binary fields and both orientations remain.
The literal source-quotient and Chapter 12 applications use the same
full amalgam marking. The linear and mixed unitary recognition consumers
retain the final comparison obligations.

Source: Fong--Seitz I (6A), p.37; AS F.1.1--3; DGS (11.6)--(11.8).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h split in
private theorem linear_actor {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nonempty (rankOne Q split i ≃* SL(2,F)) := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hV := linear_remainder_le_kernel Q e h split i T hT μ
  obtain ⟨f,hf,hk,_⟩ := linear_actor_quotient_of_factor Q e h split i μ
  let : ((S ⊔ L i).subgroupOf (parabolic L S i)).Normal :=
    marked_sylow_factor_normal Q e h split i
  obtain ⟨a,_⟩ := marked_linear_rankOne Q e h split i
    (UnitarySource.actorReflection Q split i) hV _ (subgroupOf_mono _ le_sup_left) f hf hk
  exact ⟨hV,⟨a⟩⟩

include e h split in
/-- No original Suzuki quotient occurs opposite a linear quadrangle factor,
including the nonperfect parameter zero. -/
theorem original_linear_suzuki_excluded
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m) : False := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  obtain ⟨hVi,⟨ξ⟩⟩ := linear_actor Q e h split i μi
  exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.no_linear_suzuki_quadrangle
    Q split hm i j hij hVi (suzuki_remainder_le_kernel_all Q e h split j T hT μj)
    (parabolic_core_selfCentralizing Q e h j) ξ m
    (suzukiAllRankOneEquiv Q e h split j T hT μj)
    (HexagonStructure.originalSuzukiAllRootEquiv Q e h split j T hT μj)

include e h split in
/-- The D10 constructor is excluded using its full order-twenty root actor. -/
theorem original_linear_dihedral_excluded
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5) : False := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  obtain ⟨hVi,⟨ξ⟩⟩ := linear_actor Q e h split i μi
  exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.no_linear_suzuki_quadrangle
    Q split hm i j hij hVi (dihedral_remainder_le_kernel Q e h split j T hT μj)
    (parabolic_core_selfCentralizing Q e h j) ξ 0
    (dihedralSuzukiRankOneEquiv Q e h split j T hT μj)
    (HexagonStructure.originalDihedralRootEquiv Q e h split j T hT μj)

include e h split in
/-- The full opposite catalogue reduces to original linear or unitary factors. -/
theorem original_quadrangle_opposite_linear_or_unitary
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    ∃ n : ℕ, 0 < n ∧
      (ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) ∨
       ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n) ∨
       IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n)) := by
  cases h.quotient j with
  | linear n hn hmodel => exact ⟨n,hn,Or.inl hmodel⟩
  | suzuki m hmodel => exact (original_linear_suzuki_excluded Q e h split hm i j hij μi hmodel.some).elim
  | projective_unitary n hn hmodel => exact ⟨n,hn,Or.inr (Or.inl hmodel)⟩
  | special_unitary n hn hmodel => exact ⟨n,hn,Or.inr (Or.inr hmodel)⟩
  | dihedral hmodel => exact (original_linear_dihedral_excluded Q e h split hm i j hij μi hmodel.some).elim

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
