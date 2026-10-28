module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.CommonFieldRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularFactorCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SylowGeneratedReduction

/-!
# The G₂ source row from the original linear quotients

Both original factors are marked as PSL₂ over the same finite field. Their
actual Sylows supply the root orders, linear panel regularity, and faithful
local PSL₂ actions. The regular cover theorem applies without perfectness:
the original quotient is centerless and its whole Sylow is accounted for.
The original F.1.1 generation theorem supplies normal generation. These
facts discharge the local-model, kernel and generation premises of the
accepted common-field G₂ recognition theorem.

The result keeps the actual quotient, full Borel, both endpoint squares and
original Sylow image. Fields of orders two and four are included; the binary
target is the full G₂(2). The independently constructed marked split quotient,
rotation order six, original common-field marks and root reflections remain
earlier source inputs. This selected row does not assert exhaustiveness.

Source: Fong--Seitz I (2B), (5C), (6E)(a), and II (9.1)--(9.21);
DGS, Groups and Graphs (1985), Theorem D, printed p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.G2Source
open FongSeitzBinary

variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

/-- The faithful local action comes from the original linear quotient, also
when the original factor is nonperfect. -/
def linearLocalEquiv (i : Fin 2)
    (μ : (L i ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    localGroup Q split i ≃* PSL(2,F) := by
  let := h.finite_local i
  let T := (h.sylow i).choose
  have hT := (h.sylow i).choose_spec
  have hK := MarkedLocal.linear_remainder_le_kernel Q e h split i T hT μ
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
    rw [MarkedLocal.simpleRoot_card_linear Q e h split i T hT μ]
    exact ((Nat.card_congr (MarkedLocal.linearSylowEquiv i T μ).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (MarkedLocal.linearModelSylow i T μ)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center (L i ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center PSL(2,F) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot, mem_bot] at hh
    exact μ.injective (hh.trans μ.map_one.symm)
  exact (MarkedLocal.regularFactorLocalEquiv Q e h split i T hT hK hc hz).trans μ

include e h in
private theorem linearContainment (i : Fin 2)
    (μ : (L i ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  exact MarkedLocal.linear_remainder_le_kernel Q e h split i T hT μ

variable (hm : rotationOrder Q = 6)
  (μ : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i)

/-- Construct all G₂ relations and their orientation from original quotient
marks. No local-action marking, kernel bound or normal-generation callback
is supplied by the caller. -/
def linearData : Σ i : Fin 2, RootData Q split F i :=
  ⟨_, GTwoSource.CommonFieldSource.rootData Q split hm
    (fun i => linearContainment Q e h split i (μ i))
    (fun i => linearLocalEquiv Q e h split i (μ i)) n
    (MarkedLocal.unipotentClosure_eq_top_of_source Q e h split)⟩

/-- The constructed equivalence of the actual finite quotient with full G₂. -/
def linearModelEquiv : (X ⧸ Q.D) ≃* Atlas.G2.Model F :=
  G2Presentation.quotientEquiv Q split (linearData Q e h split hm μ n).2

/-- Both endpoint squares use the same quotient equivalence and whole overlap. -/
def linearComparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F (linearData Q e h split hm μ n).1) :=
  G2Presentation.comparison Q e split (linearData Q e h split hm μ n).2

theorem linearComparison_left (x : parabolic L S 0) :
    ((linearComparison Q e h split hm μ n).left x : Atlas.G2.Model F) =
      linearModelEquiv Q e h split hm μ n (MarkedLocal.endpointMap Q e 0 x) := by
  exact G2Presentation.comparison_left_apply Q e split (linearData Q e h split hm μ n).2 x

theorem linearComparison_right (x : parabolic L S 1) :
    ((linearComparison Q e h split hm μ n).right x : Atlas.G2.Model F) =
      linearModelEquiv Q e h split hm μ n (MarkedLocal.endpointMap Q e 1 x) := by
  exact G2Presentation.comparison_right_apply Q e split (linearData Q e h split hm μ n).2 x

/-- The full common Borel is marked, including its odd part. -/
theorem linearComparison_borel (b : commonBorel L S) :
    ((linearComparison Q e h split hm μ n).middle
      ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm) b) : Atlas.G2.Model F) =
      linearModelEquiv Q e h split hm μ n (MarkedLocal.borelMap Q e h b) := by
  exact G2Presentation.comparison_commonBorel_apply Q e h split
    (linearData Q e h split hm μ n).2 b

/-- The original Sylow has exactly the positive-subgroup image. -/
theorem linearComparison_sylow :
    (MarkedLocal.sylowMap Q e h).range.map
      (linearModelEquiv Q e h split hm μ n).toMonoidHom = Atlas.G2.unipotent :=
  G2Presentation.source_sylow_image Q e h split (linearData Q e h split hm μ n).2

/-- The same map identifies the entire Borel and both oriented parabolics. -/
theorem linearModelEquiv_images :
    Q.tits.B.map (linearModelEquiv Q e h split hm μ n).toMonoidHom = Atlas.G2.borel ∧
    (Q.tits.standardParabolic {Q.simple (linearData Q e h split hm μ n).1}).map
      (linearModelEquiv Q e h split hm μ n).toMonoidHom =
        Atlas.G2.LieParabolicSetup.parabolic₁ ∧
    (Q.tits.standardParabolic {Q.simple (1 - (linearData Q e h split hm μ n).1)}).map
      (linearModelEquiv Q e h split hm μ n).toMonoidHom =
        Atlas.G2.LieParabolicSetup.parabolic₂ :=
  (G2Presentation.subgroup_images Q split (linearData Q e h split hm μ n).2).2

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.G2Source
