module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.NaturalConstituents

/-!
# Ratio preservation through faithful constituents

Maximizing offender weight and then minimizing inside its equal-weight class
preserves every action ratio at most one. A single minimal offender therefore
bounds the actual action on every faithful irreducible component constituent.
The full earlier B.4.2 theorem then gives the quarter lower bound on every
noncentral chief image, without assuming irreducibility on the component.

Source: Aschbacher--Smith B.5.1, pp.100–101, (+) and the comparison of q_i.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem actionRatio_le_of_weight {A D : Subgroup G} (hA : IsOffender ρ A)
    (hD : IsElementaryTwo D) (hrank : rank D ≤ rank A) (hw : weight ρ A ≤ weight ρ D) :
    actionRatio ρ D ≤ actionRatio ρ A := by
  have ha := fixedCodim_add_finrank ρ A
  have hd := fixedCodim_add_finrank ρ D
  unfold weight at hw
  have hc : fixedCodim ρ D + rank A ≤ rank D + fixedCodim ρ A := by omega
  have hpa : (0 : ℝ) < rank A := by exact_mod_cast hA.1.rank_pos
  have hpd : (0 : ℝ) < rank D := by exact_mod_cast hD.rank_pos
  have hca : (fixedCodim ρ A : ℝ) ≤ rank A := by exact_mod_cast hA.2
  have hrd : (rank D : ℝ) ≤ rank A := by exact_mod_cast hrank
  have hcd : (fixedCodim ρ D : ℝ) + rank A ≤ rank D + fixedCodim ρ A := by exact_mod_cast hc
  have hnat (H : Subgroup G) (hp : 0 < rank H) : actionRatio ρ H ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by exact_mod_cast Nat.ne_of_gt hp)
  apply (ENNReal.toReal_le_toReal (hnat D hD.rank_pos) (hnat A hA.1.rank_pos)).mp
  simp only [actionRatio, ENNReal.toReal_div, ENNReal.toReal_natCast]
  apply (div_le_div_iff₀ hpd hpa).mpr
  have hmul := mul_le_mul_of_nonneg_right hcd hpa.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hrd)]

theorem exists_minimal_ratio {r : ℝ≥0∞} (hr : r ≤ 1) (hq : quadraticRatio ρ ≤ r) :
    ∃ B, IsMinimalBestOffender ρ B ∧ actionRatio ρ B ≤ r := by
  have hrt : r ≠ ⊤ := ne_top_of_le_ne_top (by simp) hr
  obtain ⟨A, hA, _, hAr⟩ := (quadraticRatio_le_iff ρ hrt).mp hq
  have hoff : IsOffender ρ A := ⟨hA, (actionRatio_le_one_iff ρ hA).mp (hAr.trans hr)⟩
  obtain ⟨B, hBA, hB, hweight⟩ := exists_bestOffender_ge_weight ρ hoff
  obtain ⟨D, hD, hDB⟩ := hB.exists_minimal ρ
  have hw : weight ρ A ≤ weight ρ D := hweight.trans_eq hDB.2.symm
  have hd : rank D ≤ rank A := Nat.log_mono_right (Subgroup.card_le_of_le (hDB.1.trans hBA))
  exact ⟨D, hD, (actionRatio_le_of_weight ρ hoff hD.1.1 hd hw).trans hAr⟩

omit [Finite G] in
theorem subrepresentation_ratio_le_actionRatio (W : Subrepresentation ρ)
    {B : Subgroup G} (hb : IsElementaryTwo B) (hq : IsQuadratic ρ B) :
    quadraticRatio W.toRepresentation ≤ actionRatio ρ B := by
  apply (iInf_le_of_le B (iInf_le_of_le ⟨hb, quadratic_subrepresentation ρ W hq⟩ le_rfl)).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast fixedCodim_subrepresentation_le ρ W B

/-- The common offender bounds the ratio on every actual stable constituent. -/
theorem constituent_ratio_le {C B : Subgroup G} (hB : IsMinimalBestOffender ρ B)
    (W : Subrepresentation (ρ.comp C.subtype))
    (hs : C ⊔ B ≤ subspaceStabilizer ρ W.toSubmodule) :
    quadraticRatio (invariantSubspace ρ (C ⊔ B) W.toSubmodule hs).toRepresentation ≤
      actionRatio ρ B := by
  let H := C ⊔ B
  let J := invariantSubspace ρ H W.toSubmodule hs
  have hb := (hB.1.subgroupOf ρ (show B ≤ H from le_sup_right)).1
  have hq : IsQuadratic (ρ.comp H.subtype) (B.subgroupOf H) := by
    intro a ha b hb v
    exact hB.isQuadratic ρ a.val ha b.val hb v
  have hh := subrepresentation_ratio_le_actionRatio (ρ.comp H.subtype) J hb hq
  simpa only [actionRatio, fixedCodim_subgroupOf ρ (show B ≤ H from le_sup_right),
    rank_subgroupOf (show B ≤ H from le_sup_right)] using hh

/-- The earlier irreducible theorem applies simultaneously to all faithful
constituents at the original action's ratio bound. -/
theorem bounded_constituent_classification
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) {r : ℝ≥0∞} (hr : r ≤ 1) (hq : quadraticRatio ρ ≤ r) :
    ∃ B, IsMinimalBestOffender ρ B ∧
      ∀ (W : Subrepresentation (ρ.comp C.subtype)), IsIrreducible W.toRepresentation →
        Function.Injective W.toRepresentation →
        ∃ hstable : C ⊔ B ≤ subspaceStabilizer ρ W.toSubmodule,
          let δ := (invariantSubspace ρ (C ⊔ B) W.toSubmodule hstable).toRepresentation
          SourceInduction.ProjectiveLine.IrreducibleActionCase δ
            (generalizedFitting ↥(C ⊔ B)) (offenderSubgroup δ) ∧ quadraticRatio δ ≤ r := by
  obtain ⟨B, hB, hb⟩ := exists_minimal_ratio ρ hr hq
  refine ⟨B, hB, fun W hi hf => ?_⟩
  obtain ⟨hs, hc⟩ := constituent_classification ρ hK earlier C hC hfit hcore hfaith hB W hi hf
  exact ⟨hs, hc, (constituent_ratio_le ρ hB W hs).trans hb⟩

omit [FiniteDimensional (ZMod 2) V] [Finite G] in
theorem FaithfulConstituentDecomposition.exists_constituent [Nontrivial V]
    {C : Subgroup G} (h : FaithfulConstituentDecomposition ρ C) :
    ∃ W : Subrepresentation (ρ.comp C.subtype),
      IsIrreducible W.toRepresentation ∧ Function.Injective W.toRepresentation := by
  obtain ⟨n, W, hd, hW⟩ := h
  have hnonempty : Nonempty (Fin n) := by
    by_contra! he
    let := he
    have hz := hd.submodule_iSup_eq_top
    simp only [iSup_of_empty] at hz
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    let a := (Representation.asModuleEquiv (ρ.comp C.subtype)).symm v
    have ha : a ∈ (⊥ : Submodule (MonoidAlgebra (ZMod 2) C)
      (Representation.asModule (ρ.comp C.subtype))) := hz.symm ▸ Submodule.mem_top
    have he : a = 0 := ha
    apply hv
    have heq := congrArg (Representation.asModuleEquiv (ρ.comp C.subtype)) he
    simpa only [a, LinearEquiv.apply_symm_apply, map_zero] using heq
  obtain ⟨i⟩ := hnonempty
  exact ⟨W i, hW i⟩

/-- The quarter lower bound passes from the earlier irreducible catalogue
to the entire faithful chief action, without assuming component irreducibility. -/
theorem quarter_le_ratio_of_constituents [Nontrivial V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hdec : FaithfulConstituentDecomposition ρ C)
    (hq : quadraticRatio ρ ≤ 1) : 1 / 4 ≤ quadraticRatio ρ := by
  obtain ⟨B, _, hb⟩ := bounded_constituent_classification ρ hK earlier C hC
    hfit hcore hfaith hq le_rfl
  obtain ⟨W, hi, hf⟩ := hdec.exists_constituent ρ
  obtain ⟨hs, hc, hr⟩ := hb W hi hf
  exact (hc.quarter_le_ratio _).trans hr

/-- Actual chief-image application, retaining its kernel quotient and the
three genuine earlier inputs A.2.1, A.3.6 and B.4.2. -/
theorem ChiefImage.quarter_le_ratio
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hL : IsSQTK K L) (hi : IsIrreducible ρ)
    (hn : subspaceCommutator ρ ⊤ L ≠ ⊥) (hq : IsPGroup 2 (G ⧸ L))
    (hr : quadraticRatio (imageRepresentation ρ) ≤ 1) :
    1 / 4 ≤ quadraticRatio (imageRepresentation ρ) := by
  let C := ChiefImage.component ρ L
  let : C.Normal := ChiefImage.component_normal ρ L
  let : IsQuasisimple C := ChiefImage.component_quasisimple ρ L hn
  let := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hratio : quadraticRatio (KernelQuotient.action ρ) = quadraticRatio (imageRepresentation ρ) :=
    NaturalExtensions.FourSpaceOffenders.reindex_ratio (imageRepresentation ρ) (KernelQuotient.equiv ρ)
  rw [← hratio] at hr ⊢
  exact quarter_le_ratio_of_constituents (KernelQuotient.action ρ) hK earlier C
    (ChiefImage.component_sqtk ρ hsemisimple L hL hn)
    (ChiefImage.fitting_eq_component ρ L hi hn hq) (ChiefImage.twoCore_eq_bot ρ hi)
    (KernelQuotient.faithful ρ) (ChiefImage.faithful_constituents ρ hsemisimple h36 L hL hi hn) hr

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
