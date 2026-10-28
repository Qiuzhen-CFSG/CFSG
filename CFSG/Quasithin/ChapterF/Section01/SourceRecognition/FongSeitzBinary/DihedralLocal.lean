module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.FactorClosureAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocal
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Valence
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.DihedralPanelModel
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms

/-!
# The truncated Suzuki source endpoint becomes Sz(2)

An actual D₁₀ original quotient gives a panel of degree five and a root
of order four. Its quotient-automorphism two-subgroups have order at most
four, forcing the entire simple remainder into the full panel kernel.
The original quotient embeds in the whole cover; the canonical root also
embeds there. Their orders ten and four, together with the automorphism
bound twenty, force the cover's order to be twenty. Its two-core is
trivial, so the checked five-point recognition identifies it with Sz(2).
Centerlessness then identifies the same faithful local permutation image.

No factor perfectness is assumed and no equality of root order four with
the original quotient Sylow order two is imposed. DihedralApplications
retains the original D₁₀ as an actual index-two subgroup and preserves the
original factor, root and cover representative equations.
Source: DGS (6.1) and its remark, pp.118--119; Fong--Seitz I
(2B), (5B)--(5C), pp.7--9,25--26; AS F.1.1--3, pp.259--260.
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

variable [Finite (L i)]
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  (μ : ((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5)

include e h hT μ in
/-- The original dihedral panel has degree five and canonical root order four. -/
theorem dihedral_simpleRoot_card : Nat.card (simpleRoot Q split i) = 4 := by
  have he := Nat.card_congr ((localBorelPanel Q e h i).symm.trans
    (localBorelModelCosetEquiv (L i) S T hT μ))
  have hi := singleton_parabolic_root_index Q split i
  change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at hi
  have hm := dihedral_sylow_normalizer_index (MulEquiv.refl (DihedralGroup 5))
    ((quotientSylow T).mapSurjective (f := μ.toMonoidHom) μ.surjective)
  change Nat.card (DihedralGroup 5 ⧸ _) = 5 at hm
  have he' : 1 + Nat.card (simpleRoot Q split i) = 5 := hi.symm.trans (he.trans hm)
  omega

include e h hT μ in
/-- The truncated Suzuki endpoint satisfies (2B), without a Sylow-count equality. -/
theorem dihedral_remainder_le_kernel : simpleRemainder Q split i ≤ localKernel Q i := by
  apply remainder_le_kernel_of_factor_action_bound Q e h split i
  · apply eq_bot_iff.mpr
    intro z hz
    have he := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center (DihedralGroup 5) at he
    rw [DihedralGroup.five_center_eq_bot,mem_bot] at he
    exact μ.injective (he.trans μ.map_one.symm)
  · intro V hV
    let f := (MulAut.congr μ).toMonoidHom
    have hc := card_map_of_injective (K := V) (f := f) (MulAut.congr μ).injective
    rw [dihedral_simpleRoot_card Q e h split i T hT μ, ← hc]
    exact DihedralGroup.five_aut_two_subgroup_bound _ (hV.map f)

include e h hT μ in
/-- The original endpoint pullback of the remainder is its two-core. -/
theorem dihedral_remainder_comap :
    (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i) :=
  remainder_comap_of_containment Q e split i (dihedral_remainder_le_kernel Q e h split i T hT μ)
omit [Finite (L i)] in
include μ in
private theorem dihedral_factor_center : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  have he := MulEquivClass.apply_mem_center μ hz
  change μ z ∈ center (DihedralGroup 5) at he
  rw [DihedralGroup.five_center_eq_bot,mem_bot] at he
  exact μ.injective (he.trans μ.map_one.symm)

include e h hT μ in
/-- The original order-ten factor and order-four root force a cover of order twenty. -/
theorem dihedral_localCover_card : Nat.card (LocalCover.CoverGroup Q split i) = 20 := by
  have hbound : Nat.card (LocalCover.CoverGroup Q split i) ≤ 20 := by
    have hh := localCover_card_le_factor_aut Q e h split i (dihedral_factor_center i μ)
    rw [Nat.card_congr (MulAut.congr μ).toEquiv] at hh
    exact hh.trans DihedralGroup.card_mulAut_five_le_twenty
  have hten : 10 ∣ Nat.card (LocalCover.CoverGroup Q split i) := by
    have hh := (factorQuotientCoverMap Q e h split i).range.card_subgroup_dvd_card
    have he := Nat.card_congr (MonoidHom.ofInjective
      (factorQuotientCoverMap_injective Q e h split i)).toEquiv
    rw [←he,Nat.card_congr μ.toEquiv,DihedralGroup.nat_card] at hh
    exact hh
  have hfour : 4 ∣ Nat.card (LocalCover.CoverGroup Q split i) := by
    let f := (RootLocalCover.coverMap Q split i).comp
      (inclusion (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left))
    have hf : Function.Injective f := (RootLocalCover.coverMap_injective Q split i).comp
      (inclusion_injective _)
    have hh := f.range.card_subgroup_dvd_card
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      dihedral_simpleRoot_card Q e h split i T hT μ] at hh
    exact hh
  have hp := Nat.card_pos (α := LocalCover.CoverGroup Q split i)
  omega

/-- The whole local cover of a dihedral source factor is the actual Sz(2) model. -/
noncomputable def dihedralSuzukiCoverEquiv :
    LocalCover.CoverGroup Q split i ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 := by
  apply Classical.choice
  apply Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.equiv_suzuki_of_card_twenty
    (dihedral_localCover_card Q e h split i T hT μ)
  have he := pCore_map_iso 2 (LocalCover.coreQuotientEquiv Q split i).symm
  rw [pCore_quotient_pCore_eq_bot, Subgroup.map_bot] at he
  exact he.symm

/-- The canonical two-root group is Sz(2), with (2B) discharged. -/
noncomputable def dihedralSuzukiRankOneEquiv :
    rankOne Q split i ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  (RootLocalCover.coverEquiv Q split i (dihedral_remainder_le_kernel Q e h split i T hT μ)).trans
    (dihedralSuzukiCoverEquiv Q e h split i T hT μ)

/-- The root comparison uses the literal whole-cover quotient representative. -/
@[simp] theorem dihedralSuzukiRankOneEquiv_apply (r : rankOne Q split i) :
    dihedralSuzukiRankOneEquiv Q e h split i T hT μ r =
      dihedralSuzukiCoverEquiv Q e h split i T hT μ
        (QuotientGroup.mk' (LocalCover.radicalInClosure Q split i)
          (inclusion (rankOne_le_localClosure Q split i) r)) := by
  rw [dihedralSuzukiRankOneEquiv, MulEquiv.trans_apply, RootLocalCover.coverEquiv_apply]

include e h hT μ in
/-- The central panel kernel vanishes in the centerless Suzuki cover. -/
theorem dihedral_cover_projection_injective : Function.Injective (LocalCover.projection Q split i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  let c := dihedralSuzukiCoverEquiv Q e h split i T hT μ
  have he := MulEquivClass.apply_mem_center c (LocalCover.projection_ker_central Q split i hx)
  change c x ∈ center (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) at he
  rw [BenderSuzuki.MatrixGroups.suzukiZero_center_eq_bot,mem_bot] at he
  exact c.injective (he.trans c.map_one.symm)

/-- The SAME faithful local permutation image is Sz(2). -/
noncomputable def dihedralSuzukiLocalEquiv :
    localGroup Q split i ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  (MulEquiv.ofBijective (LocalCover.projection Q split i)
    ⟨dihedral_cover_projection_injective Q e h split i T hT μ,
      LocalCover.projection_surjective Q split i⟩).symm.trans
    (dihedralSuzukiCoverEquiv Q e h split i T hT μ)

/-- The root and local comparisons commute with the literal panel action. -/
theorem dihedralSuzukiRankOneEquiv_projection (r : rankOne Q split i) :
    dihedralSuzukiRankOneEquiv Q e h split i T hT μ r =
      dihedralSuzukiLocalEquiv Q e h split i T hT μ (RootLocalCover.projection Q split i r) := by
  let hV := dihedral_remainder_le_kernel Q e h split i T hT μ
  have he : RootLocalCover.projection Q split i r =
      LocalCover.projection Q split i (RootLocalCover.coverEquiv Q split i hV r) := by
    apply Subtype.ext
    rw [RootLocalCover.projection_apply,RootLocalCover.coverEquiv_apply,LocalCover.projection_mk]
  rw [he]
  let a := MulEquiv.ofBijective (LocalCover.projection Q split i)
    ⟨dihedral_cover_projection_injective Q e h split i T hT μ,
      LocalCover.projection_surjective Q split i⟩
  change dihedralSuzukiCoverEquiv Q e h split i T hT μ (RootLocalCover.coverEquiv Q split i hV r) =
    dihedralSuzukiCoverEquiv Q e h split i T hT μ (a.symm (a (RootLocalCover.coverEquiv Q split i hV r)))
  rw [MulEquiv.symm_apply_apply]
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
