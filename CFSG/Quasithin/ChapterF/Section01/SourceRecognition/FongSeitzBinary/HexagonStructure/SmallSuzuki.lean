module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSuzuki
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.MixedSuzuki
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.DihedralLocal

/-!
# All mixed linear--Suzuki rows on the original marked quotient

The small Suzuki argument supplies the missing m=0 case of the mixed
linear--Suzuki exclusion. The actual all-parameter Suzuki cover identifies
the root actor and its root Sylow, with (2B) discharged. For the original
dihedral D₁₀ constructor, its actual cover is Sz(2), and the canonical root
has order four; its faithful local image supplies the correct root
isomorphism. Neither original factor is assumed perfect.

The proof constructs Z(O₃(H)) on the same quotient. Its centralizer in
the original Sylow radical is the literal two-root product, with words
s_i and s_i s_j. The Theory proof moves this section by a constructed
order-five reflection--root product and contradicts its Frattini bounds.
Both original/geometric markings and the literal Q.q application are
provided. Separately, the existing regular Suzuki two-layer bound
excludes the original small Suzuki and dihedral opposite endpoints.

Source: Fong--Seitz I (5H), printed pp.29--30, and (6C), pp.39--41;
DGS (6.1), pp.118--119, for the original dihedral constructor. The earlier
(1J) square profile remains explicit where used. These exclusions leave
two regular Suzuki endpoints, two small endpoints, the remaining unitary
rows and the exhaustive structural dichotomy with the same assembly owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

/-- The actual dihedral endpoint's canonical root, through its faithful
local image and specified Sylow, is the small Suzuki root. -/
def originalDihedralRootEquiv (j : Fin 2) [Finite (L j)]
    (T : Sylow 2 (L j)) (hT : (T : Subgroup (L j)).map (L j).subtype = S ⊓ L j)
    (μ : ((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5) :
    simpleRoot Q split j ≃* SuzukiRootSubgroup 0 := by
  let a := dihedralSuzukiLocalEquiv Q e h split j T hT μ
  let R := (GTwoSource.localSylow Q split j).mapSurjective (f := a.toMonoidHom) a.surjective
  let b : GTwoSource.localSylow Q split j ≃* R :=
    (GTwoSource.localSylow Q split j : Subgroup _).equivMapOfInjective a.toMonoidHom a.injective
  exact (GTwoSource.simpleRootLocalSylowEquiv Q split j
    (dihedral_remainder_le_kernel Q e h split j T hT μ)).trans
    (b.trans ((R.equiv (ReeSource.matrixRootSylow 0)).trans
      (MulEquiv.subgroupCongr (ReeSource.matrixRootSylow_carrier 0))))

private def originalLinearLocalEquiv
    {F : Type*} [Field F] [Finite F] [CharP F 2] (i : Fin 2)
    [Finite (L i)] (T : Sylow 2 (L i))
    (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    localGroup Q split i ≃* PSL(2,F) := by
  have hK := linear_remainder_le_kernel Q e h split i T hT μ
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
    rw [simpleRoot_card_linear Q e h split i T hT μ]
    exact ((Nat.card_congr (linearSylowEquiv i T μ).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i T μ)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center PSL(2,F) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact μ.injective (hh.trans μ.map_one.symm)
  exact (regularFactorLocalEquiv Q e h split i T hT hK hc hz).trans μ

include e h in
/-- Original/geometric linear--Suzuki exclusion for every parameter,
including Sz(2), with neither original factor assumed perfect. -/
theorem original_mixed_linear_suzuki_all_exclusion
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact no_mixed_suzuki_all_of_square_profile Q split hhex i j hij
    (linear_remainder_le_kernel Q e h split i Ti hTi μi)
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj)
    (originalLinearLocalEquiv Q e h split i Ti hTi μi)
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj) hsquare

include e h in
/-- The original D₁₀ constructor is also excluded opposite a linear
endpoint; its genuine source actor and order-four root are used. -/
theorem original_mixed_linear_dihedral_exclusion
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact no_mixed_smallSuzuki_of_square_profile Q split hhex i j hij
    (linear_remainder_le_kernel Q e h split i Ti hTi μi)
    (dihedral_remainder_le_kernel Q e h split j Tj hTj μj)
    (originalLinearLocalEquiv Q e h split i Ti hTi μi)
    (dihedralSuzukiRankOneEquiv Q e h split j Tj hTj μj)
    (originalDihedralRootEquiv Q e h split j Tj hTj μj) hsquare

include e h split in
/-- A regular Suzuki endpoint cannot face either original order-four
alternative. This discharges the mixed small/regular Suzuki rows. -/
theorem original_regular_suzuki_small_exclusion
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    {m : ℕ} (hm : 0 < m) (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m) : False := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hc : Nat.card (simpleRoot Q split i) = 4 := by
    rcases hi with ⟨⟨μi⟩⟩ | ⟨⟨μi⟩⟩
    · rw [Nat.card_congr (originalSuzukiAllRootEquiv Q e h split i Ti hTi μi).toEquiv,
        ReeSource.matrixRoot_card]
      norm_num
    · exact dihedral_simpleRoot_card Q e h split i Ti hTi μi
  exact no_regular_suzuki_opposite_four Q split hhex i j hij
    (suzuki_remainder_le_kernel_all Q e h split j Tj hTj μj) hm
    (suzukiAllRankOneEquiv Q e h split j Tj hTj μj)
    (originalSuzukiAllRootEquiv Q e h split j Tj hTj μj) hc

include e h in
/-- The small Suzuki/dihedral three-core centralizer identity on the
literal original Sylow image, before applying the contradictory bounds. -/
theorem original_smallSuzuki_centralizer_product
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) :
    (((sylowMap Q e h).range ⊓
        rightConjugate (sylowMap Q e h).range
          ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)) ⊓
      centralizer (threeCartan Q : Set (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (rightConjugate (simpleRoot Q split j)
        ((UnitarySource.actorReflection Q split i).val : X ⧸ Q.D) : Set (X ⧸ Q.D)) *
      (rightConjugate (simpleRoot Q split j)
        (((UnitarySource.actorReflection Q split i).val : X ⧸ Q.D)*
          (UnitarySource.actorReflection Q split j).val) : Set (X ⧸ Q.D)) := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  obtain ⟨μj,νj⟩ : Nonempty (rankOne Q split j ≃* SuzukiMatrixGroup 0) ∧
      Nonempty (simpleRoot Q split j ≃* SuzukiRootSubgroup 0) := by
    rcases hj with ⟨⟨a⟩⟩ | ⟨⟨a⟩⟩
    · exact ⟨⟨suzukiAllRankOneEquiv Q e h split j Tj hTj a⟩,
        ⟨originalSuzukiAllRootEquiv Q e h split j Tj hTj a⟩⟩
    · exact ⟨⟨dihedralSuzukiRankOneEquiv Q e h split j Tj hTj a⟩,
        ⟨originalDihedralRootEquiv Q e h split j Tj hTj a⟩⟩
  let a := originalLinearLocalEquiv Q e h split i Ti hTi μi
  have hKi := linear_remainder_le_kernel Q e h split i Ti hTi μi
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  have hh := radical_centralizer_product Q split hhex i j hij (threeCartan Q)
    (threeCartan_le_cartan Q)
    (linear_threeCartan_nontrivial_fixedFree Q split i hKi a si
      (linear_cubic_of_suzuki_square_profile Q split i j hKi a νj.some hsquare)).2
    (threeCartan_centralizes_smallSuzuki_roots Q split j μj.some)
  rw [marked_radical_eq h Q e split j sj.val sj.class_eq] at hh
  rw [rootAt_eq Q split j (Q.simple i) si.val si.class_eq,
    rootAt_eq Q split j (Q.simple i*Q.simple j) (si.val*sj.val)
      (by rw [map_mul,si.class_eq,sj.class_eq])] at hh
  exact hh

/-- The exact Q.q centralizer, retaining the source-S image and both
right-conjugation words. -/
theorem quotient_smallSuzuki_centralizer_product
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) :
    ((((S.subgroupOf (generated L S)).map Q.q) ⊓
        rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
          ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)) ⊓
      centralizer (threeCartan Q : Set ((generated L S) ⧸ Q.D)) : Set ((generated L S) ⧸ Q.D)) =
      (rightConjugate (simpleRoot Q split j)
        ((UnitarySource.actorReflection Q split i).val : (generated L S) ⧸ Q.D) : Set _) *
      (rightConjugate (simpleRoot Q split j)
        (((UnitarySource.actorReflection Q split i).val : (generated L S) ⧸ Q.D)*
          (UnitarySource.actorReflection Q split j).val) : Set _) := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := original_smallSuzuki_centralizer_product Q (originalMarkedIso Q)
    h split hhex i j hij μi hj hsquare
  rw [sylow_range Q (originalMarkedIso Q) h split] at hh
  exact hh

/-- All Suzuki parameters are excluded opposite a linear original factor
on the literal quotient map, with the earlier square profile retained. -/
theorem quotient_mixed_linear_suzuki_all_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_mixed_linear_suzuki_all_exclusion Q (originalMarkedIso Q) h split
    hhex i j hij μi μj hsquare

/-- The original dihedral quotient is handled through its actual Sz(2)
cover, without changing the original model or imposing perfectness. -/
theorem quotient_mixed_linear_dihedral_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_mixed_linear_dihedral_exclusion Q (originalMarkedIso Q) h split
    hhex i j hij μi μj hsquare

/-- The regular/small Suzuki exclusion on the original quotient map. -/
theorem quotient_regular_suzuki_small_exclusion
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    {m : ℕ} (hm : 0 < m) (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m) : False :=
  original_regular_suzuki_small_exclusion Q (originalMarkedIso Q) h split
    hhex i j hij hi hm μj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
