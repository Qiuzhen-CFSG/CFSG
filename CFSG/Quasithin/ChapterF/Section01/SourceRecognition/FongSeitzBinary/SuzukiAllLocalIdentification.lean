module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiAllRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularFactorCover

/-!
# All Suzuki local groups and original covers

Substitute the proved (2B) containment and exact original quotient-Sylow
count into RegularFactorCover. The canonical root group and whole original
cover become the actual Suzuki matrix group, including Sz(2), without
assuming the original factor perfect. Centerlessness kills the central
panel kernel and identifies the same local permutation image.

The original cover agrees both with the supplied Suzuki marking on every
original factor representative and with the root comparison on every root
representative. The root/local square is the actual original panel action.
SuzukiAllApplications supplies the literal Chapter 12 applications.

Source: Fong--Seitz I (2B), (5B)--(5C), pp.7--9,25--26;
AS F.1.1--3, pp.259--260. These are local comparisons; the full Borel,
both marked endpoint squares and split quotient remain earlier inputs,
and seven-row rank-two selection remains a separate source obligation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)]
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  {m : ℕ} (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)

omit [Finite (L i)] in
include μ in
private theorem suzuki_all_factor_center : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
  have hz : center (SuzukiMatrixGroup m) = ⊥ := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact suzukiZero_center_eq_bot
    · let : IsSimpleGroup (SuzukiMatrixGroup m) :=
        (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
      rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with hz | hz
      · exact hz
      · exfalso
        apply BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
        exact Group.isSolvable_of_comm (fun x y => by
          have hx : x ∈ center (SuzukiMatrixGroup m) := hz ▸ mem_top x
          exact (mem_center_iff.mp hx y).symm)
  apply eq_bot_iff.mpr
  intro z hz'
  have hm := MulEquivClass.apply_mem_center μ hz'
  change μ z ∈ center (SuzukiMatrixGroup m) at hm
  rw [hz,mem_bot] at hm
  exact μ.injective (hm.trans μ.map_one.symm)

/-- The full canonical Suzuki root group at every parameter, including zero. -/
def suzukiAllRankOneEquiv : rankOne Q split i ≃* SuzukiMatrixGroup m :=
  (regularFactorRootEquiv Q e h split i T hT
    (suzuki_remainder_le_kernel_all Q e h split i T hT μ)
    (suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT μ)).trans μ

/-- The SAME faithful local permutation group is the original Suzuki model. -/
def suzukiAllLocalEquiv : localGroup Q split i ≃* SuzukiMatrixGroup m :=
  (regularFactorLocalEquiv Q e h split i T hT
    (suzuki_remainder_le_kernel_all Q e h split i T hT μ)
    (suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT μ)
    (suzuki_all_factor_center i μ)).trans μ

theorem suzukiAllRankOneEquiv_projection (r : rankOne Q split i) :
    suzukiAllRankOneEquiv Q e h split i T hT μ r =
      suzukiAllLocalEquiv Q e h split i T hT μ (RootLocalCover.projection Q split i r) := by
  apply congrArg μ
  exact regularFactorRootEquiv_projection Q e h split i T hT _ _
    (suzuki_all_factor_center i μ) r

/-- The root comparison on the original marked endpoint. -/
def originalSuzukiAllRankOneEquiv : originalRankOne Q e split i ≃* SuzukiMatrixGroup m :=
  (regularOriginalFactorRootEquiv Q e h split i T hT
    (suzuki_remainder_le_kernel_all Q e h split i T hT μ)
    (suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT μ)).trans μ

theorem originalSuzukiAllRankOneEquiv_projection (r : originalRankOne Q e split i) :
    originalSuzukiAllRankOneEquiv Q e h split i T hT μ r =
      suzukiAllLocalEquiv Q e h split i T hT μ (originalRootProjection Q e split i r) := by
  apply congrArg μ
  exact regularOriginalFactorRootEquiv_projection Q e h split i T hT _ _
    (suzuki_all_factor_center i μ) r

include h hT μ in
/-- The full original panel kernel is trivial inside the canonical root group. -/
theorem suzuki_all_original_root_kernel_trivial :
    (originalPanelKernel (L := L) (S := S) i).subgroupOf (originalRankOne Q e split i) = ⊥ :=
  regular_original_root_kernel_eq_bot Q e h split i T hT
    (suzuki_remainder_le_kernel_all Q e h split i T hT μ)
    (suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT μ)
    (suzuki_all_factor_center i μ)

/-- The full original cover is the actual Suzuki group, with no perfectness premise. -/
def originalSuzukiAllCoverEquiv :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃* SuzukiMatrixGroup m := by
  let := originalRadicalInClosure_normal Q e h split i
  exact (regularOriginalFactorCoverEquiv Q e h split i T hT
    (suzuki_remainder_le_kernel_all Q e h split i T hT μ)
    (suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT μ)).trans μ

@[simp] theorem originalSuzukiAllCoverEquiv_mk_factor (a : L i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalSuzukiAllCoverEquiv Q e h split i T hT μ
      (QuotientGroup.mk' (originalRadicalInClosure Q e split i)
        (originalFactorIntoClosure Q e h split i a)) = μ (QuotientGroup.mk' (pCore 2 (L i)) a) := by
  let := originalRadicalInClosure_normal Q e h split i
  change μ (regularOriginalFactorCoverEquiv Q e h split i T hT _ _ _) = _
  rw [regularOriginalFactorCoverEquiv_mk_factor]

@[simp] theorem originalSuzukiAllCoverEquiv_mk_root (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalSuzukiAllCoverEquiv Q e h split i T hT μ
      (QuotientGroup.mk' (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r)) =
      originalSuzukiAllRankOneEquiv Q e h split i T hT μ r := by
  let := originalRadicalInClosure_normal Q e h split i
  change μ (regularOriginalFactorCoverEquiv Q e h split i T hT _ _ _) = _
  rw [regularOriginalFactorCoverEquiv_mk_root]
  rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
