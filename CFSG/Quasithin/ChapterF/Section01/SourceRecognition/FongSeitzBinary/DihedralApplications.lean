module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.DihedralLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularCatalogue

/-!
# Original dihedral markings and the remaining binary unitary cases

Transport the Sz(2) local recognition through the original endpoint map.
The original D₁₀ quotient embeds with index two; its factor representatives
and the canonical root representatives agree with the same whole-cover
comparison. The root/local square is the original panel action, whose
kernel on the canonical root group is trivial. Scalar covers in the other
catalogue branches are unchanged.

The literal Chapter 12 application supplies both endpoint (2B)
containments and all these comparison squares. The exhaustive local
regularity sieve now leaves only actual PSU3(2) or SU3(2) quotients.
Their type VI issue, the remaining minimal-configuration reduction and
exhaustive seven-row marked rank-two assembly remain unproved here.
Earlier marked quotient and split data retain their genuine source
producers; these are local comparisons, not ambient recognition.
Source: DGS (6.1), pp.118--119, and Theorem D, p.224;
Fong--Seitz I (2B), (5B)--(5C); AS F.1.1--3 and 12.2.2.
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
  (μ : ((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5)

/-- Embed the supplied D₁₀ marking in the recognized larger Suzuki cover. -/
noncomputable def dihedralFactorEmbedding :
    DihedralGroup 5 →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  ((dihedralSuzukiCoverEquiv Q e h split i T hT μ).toMonoidHom.comp
    (factorQuotientCoverMap Q e h split i)).comp μ.symm.toMonoidHom

/-- The original dihedral quotient is faithfully retained. -/
theorem dihedralFactorEmbedding_injective : Function.Injective (dihedralFactorEmbedding Q e h split i T hT μ) :=
  (dihedralSuzukiCoverEquiv Q e h split i T hT μ).injective.comp
    ((factorQuotientCoverMap_injective Q e h split i).comp μ.symm.injective)

/-- The original dihedral factor has index two in its Suzuki enlargement. -/
theorem dihedralFactorEmbedding_index : (dihedralFactorEmbedding Q e h split i T hT μ).range.index = 2 := by
  have he := Nat.card_congr (MonoidHom.ofInjective
    (dihedralFactorEmbedding_injective Q e h split i T hT μ)).toEquiv
  have hc := (dihedralFactorEmbedding Q e h split i T hT μ).range.card_mul_index
  rw [←he,DihedralGroup.nat_card,BenderSuzuki.MatrixGroups.suzukiZero_card] at hc
  omega

/-- Transport the whole cover through the original marked endpoint. -/
noncomputable def originalDihedralSuzukiCoverEquiv :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 := by
  let := originalRadicalInClosure_normal Q e h split i
  exact (originalCoverEquiv Q e h split i).trans (dihedralSuzukiCoverEquiv Q e h split i T hT μ)

/-- Identify the original canonical root group with Sz(2). -/
noncomputable def originalDihedralSuzukiRankOneEquiv :
    originalRankOne Q e split i ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  (originalRankOneEquiv Q e split i).trans (dihedralSuzukiRankOneEquiv Q e h split i T hT μ)

@[simp] theorem originalDihedralSuzukiCoverEquiv_mk_factor (l : L i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalDihedralSuzukiCoverEquiv Q e h split i T hT μ
      (QuotientGroup.mk' _ (originalFactorIntoClosure Q e h split i l)) =
      dihedralFactorEmbedding Q e h split i T hT μ (μ (QuotientGroup.mk' (pCore 2 (L i)) l)) := by
  let := originalRadicalInClosure_normal Q e h split i
  change dihedralSuzukiCoverEquiv Q e h split i T hT μ
    (originalCoverEquiv Q e h split i (QuotientGroup.mk' _ _)) =
      dihedralSuzukiCoverEquiv Q e h split i T hT μ
        (factorQuotientCoverMap Q e h split i (μ.symm (μ (QuotientGroup.mk' _ l))))
  rw [MulEquiv.symm_apply_apply,originalCoverEquiv_mk,factorQuotientCoverMap_mk]
  apply congrArg
  apply congrArg (QuotientGroup.mk' (LocalCover.radicalInClosure Q split i))
  apply Subtype.ext
  rw [originalLocalClosureEquiv_apply,factorIntoClosure_coe]
  change endpointMap Q e i _ = endpointMap Q e i _
  apply congrArg (endpointMap Q e i)
  apply Subtype.ext
  exact originalFactorIntoClosure_coe Q e h split i l

@[simp] theorem originalDihedralSuzukiCoverEquiv_mk_root (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalDihedralSuzukiCoverEquiv Q e h split i T hT μ
      (QuotientGroup.mk' _ (inclusion (originalRankOne_le_localClosure Q e split i) r)) =
      originalDihedralSuzukiRankOneEquiv Q e h split i T hT μ r := by
  let := originalRadicalInClosure_normal Q e h split i
  change dihedralSuzukiCoverEquiv Q e h split i T hT μ
    (originalCoverEquiv Q e h split i (QuotientGroup.mk' _ _)) =
      dihedralSuzukiRankOneEquiv Q e h split i T hT μ (originalRankOneEquiv Q e split i r)
  rw [originalCoverEquiv_mk,dihedralSuzukiRankOneEquiv_apply]
  apply congrArg
  apply congrArg (QuotientGroup.mk' (LocalCover.radicalInClosure Q split i))
  apply Subtype.ext
  simp only [originalLocalClosureEquiv_apply, Subgroup.coe_inclusion, originalRankOneEquiv_apply]

/-- The original root comparison agrees with the SAME panel image. -/
theorem originalDihedralSuzukiRankOneEquiv_projection (r : originalRankOne Q e split i) :
    originalDihedralSuzukiRankOneEquiv Q e h split i T hT μ r =
      dihedralSuzukiLocalEquiv Q e h split i T hT μ (originalRootProjection Q e split i r) := by
  have he : originalRootProjection Q e split i r =
      RootLocalCover.projection Q split i (originalRankOneEquiv Q e split i r) := by
    apply Subtype.ext
    rw [originalRootProjection_apply,RootLocalCover.projection_apply]
  rw [he,← dihedralSuzukiRankOneEquiv_projection Q e h split i T hT μ]
  rfl

include h hT μ in
/-- The full original panel kernel meets the canonical root group trivially. -/
theorem dihedral_original_root_kernel_eq_bot :
    (originalPanelKernel (L := L) (S := S) i).subgroupOf (originalRankOne Q e split i) = ⊥ := by
  rw [← originalRootProjection_ker Q e h split i]
  apply (MonoidHom.ker_eq_bot_iff _).mpr
  intro r s hrs
  apply (originalDihedralSuzukiRankOneEquiv Q e h split i T hT μ).injective
  rw [originalDihedralSuzukiRankOneEquiv_projection Q e h split i T hT μ,
    originalDihedralSuzukiRankOneEquiv_projection Q e h split i T hT μ,hrs]

include e h hT in
/-- Only the two genuine binary unitary quotients remain in the (2B) sieve. -/
theorem remainder_le_kernel_or_small_unitary :
    (simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i)) ∨
    ClassicalGroup.IsPSU ((L i) ⧸ pCore 2 (L i)) 3 2 ∨
    IsSU ((L i) ⧸ pCore 2 (L i)) 3 2 := by
  rcases regularity_or_small_unitary_or_dihedral Q e h split i T hT with hreg | hs
  · exact Or.inl ⟨hreg.1,remainder_comap_of_containment Q e split i hreg.1⟩
  · rcases hs with hpsu | hs
    · exact Or.inr (Or.inl hpsu)
    · rcases hs with hsu | hd
      · exact Or.inr (Or.inr hsu)
      · obtain ⟨ν⟩ := hd
        exact Or.inl ⟨dihedral_remainder_le_kernel Q e h split i T hT ν,
          dihedral_remainder_comap Q e h split i T hT ν⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- Apply the complete regularity sieve to both literal Chapter 12 endpoints. -/
theorem rankOne_global_regularity_or_small_unitary
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    (∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i)) ∨
      ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 2 ∨ IsSU (R ⧸ pCore 2 R) 3 2 := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  rcases MarkedLocal.remainder_le_kernel_or_small_unitary Q e hf split 1 T₁ hT₁ with h1 | hs
  · refine Or.inl ?_
    intro i
    fin_cases i
    · have h0 := MarkedLocal.linear_remainder_le_kernel_of_model Q e hf split 0 hpsl
      exact ⟨h0,MarkedLocal.remainder_comap_of_containment Q e split 0 h0⟩
    · exact h1
  · exact Or.inr hs

/-- The literal Chapter 12 dihedral branch, including both containments and all representative squares. -/
theorem rankOne_global_dihedral_local_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (μ : (R ⧸ pCore 2 R) ≃* DihedralGroup 5) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    letI := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0,
      ∃ b : localGroup Q split 1 ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0,
        ∃ c : (MarkedLocal.originalLocalClosure Q e split 1 ⧸ MarkedLocal.originalRadicalInClosure Q e split 1) ≃*
            BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0,
          ∃ f : DihedralGroup 5 →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0,
            Function.Injective f ∧ f.range.index = 2 ∧
            (∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 1 r)) ∧
            (∀ r, c (QuotientGroup.mk' _ (inclusion
              (MarkedLocal.originalRankOne_le_localClosure Q e split 1) r)) = a r) ∧
            (∀ l : R, c (QuotientGroup.mk' _
              (MarkedLocal.originalFactorIntoClosure Q e hf split 1 l)) =
                f (μ (QuotientGroup.mk' (pCore 2 R) l))) ∧
            (∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  let := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  refine ⟨MarkedLocal.originalDihedralSuzukiRankOneEquiv Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.dihedralSuzukiLocalEquiv Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.originalDihedralSuzukiCoverEquiv Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.dihedralFactorEmbedding Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.dihedralFactorEmbedding_injective Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.dihedralFactorEmbedding_index Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.originalDihedralSuzukiRankOneEquiv_projection Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.originalDihedralSuzukiCoverEquiv_mk_root Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.originalDihedralSuzukiCoverEquiv_mk_factor Q e hf split 1 T₁ hT₁ μ,?_⟩
  intro i
  fin_cases i
  · exact MarkedLocal.linear_remainder_le_kernel_of_model Q e hf split 0 hpsl
  · exact MarkedLocal.dihedral_remainder_le_kernel Q e hf split 1 T₁ hT₁ μ
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
