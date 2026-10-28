module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification.Adequate

/-!
# The larger-field source reduction with adequate B.5.6

The perfect source actor supplies the same quasisimple component through
the corrected adequate classification. The existing concrete normalizer
argument then collapses its actual conjugate family and retains the full
SL₂, even-degree and marked Borel conclusions on the original quotients.
No outer module data or legacy triple-six offender clause is needed.

Source: Aschbacher–Smith, proof of 15.3.49 after (k), p.1144,
with B.5.6, p.105 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
open BorelInner BorelInner.ModelSelection ModelGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

omit d in
private theorem four_models_transport_adequate {D E : Type*} [Group D] [Group E]
    {F : Type} [Field F] (e : D ≃* E) (hm : FourModels D F) : FourModels E F := by
  rcases hm with h | h | h | h
  · exact Or.inl (h.map (e.symm.trans ·))
  · exact Or.inr (Or.inl (h.map (e.symm.trans ·)))
  · exact Or.inr (Or.inr (Or.inl (h.map (e.symm.trans ·))))
  · exact Or.inr (Or.inr (Or.inr (h.map (e.symm.trans ·))))

/-- Apply the full FF classification to obtain quasisimplicity, then collapse
all actual T-conjugate components by their concrete model normalizers. Borel
containment lifts through the star quotient because its kernel lies in T₀. -/
theorem source_four_models_reduction_of_adequate
    (hclass : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} κ) (hYL : Y0 ≤ localSpan L T)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hm : FourModels (starImage H L) F) :
    starImage H L = starImage H (localSpan L T) ∧
      Nonempty (starImage H (localSpan L T) ≃* SL(2,F)) ∧
      Y0 ≤ localSpan L T ⊓
        normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) := by
  classical
  have hq : IsQuasisimple (starImage H L) :=
    (component_quotient_quasisimple_iff d).mp
      (Classification.sourceSetup_component_quotient_quasisimple_of_adequate d hclass)
  have hmem : starImage H L ∈ conjugateFactors H L T := by
    apply mem_conjugateFactors.mpr
    refine ⟨1, ?_⟩
    have he : (MulAut.conj ((1 : T) : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [he, map_id]
  let C0 : ↥(conjugateFactors H L T) := ⟨starImage H L, hmem⟩
  let : Nonempty ↥(conjugateFactors H L T) := ⟨C0⟩
  have hmodels (C : ↥(conjugateFactors H L T)) : FourModels (LieBorels.factor C) F :=
    four_models_transport_adequate (LieBorels.factorEquiv d C) hm
  have hC := source_cubic_control d hYL
  obtain ⟨ht, he⟩ := collapse_of_four_models LieBorels.factor
    (LieBorels.factor_commute d hq) (LieBorels.factor_sup d) n hF hn hmodels _ hC
  have heq : starImage H L = starImage H (localSpan L T) :=
    le_antisymm (map_mono (comap_mono (le_conjugateSpanBy L T)))
      (subgroupOf_eq_top.mp (ht C0))
  have hd (C : ↥(conjugateFactors H L T)) :
      ∃ r : ℕ, NormalizerData (LieBorels.factor C) n r := by
    rcases hmodels C with h | h | h | h
    · exact ⟨1, (linearTwo_normalizerData F n hF hn).of_equiv h.some⟩
    · exact ⟨2, (linearThree_normalizerData F n hF hn).of_equiv h.some⟩
    · exact ⟨2, (symplectic_normalizerData hF hn).of_equiv h.some⟩
    · exact ⟨2, (g2_normalizerData hF hn).of_equiv h.some⟩
  choose r hr using hd
  have hSN : (LieBorels.closureSylow d : Subgroup (starImage H (localSpan L T))) ≤
      normalizer ((starImage H Y0).subgroupOf (starImage H (localSpan L T)) :
        Set (starImage H (localSpan L T))) := by
    rw [LieBorels.closureSylow_coe]
    exact (comap_mono (star_normalizes H _ Y0
      (inf_le_left.trans d.sylow_normalizes))).trans
        ((starImage H Y0).le_normalizer_comap (starImage H (localSpan L T)).subtype)
  have hCB := (family_borel LieBorels.factor (LieBorels.factor_commute d hq)
    (LieBorels.factor_sup d) n r hr _ hC (LieBorels.closureSylow d) hSN).1
  change _ ≤ normalizer
    ((LieBorels.closureSylow d : Subgroup (starImage H (localSpan L T))) :
      Set (starImage H (localSpan L T))) at hCB
  rw [LieBorels.closureSylow_coe] at hCB
  have hpre := map_le_iff_le_comap.mp
    ((starProjection_map H (localSpan L T) Y0 (closure_le d) hYL).le.trans hCB)
  rw [starProjection_normalizer_comap H (localSpan L T)
    ((T : Subgroup G) ⊓ localSpan L T) (closure_le d) inf_le_right
    (closure_projection_ker_le_inter d)] at hpre
  refine ⟨heq, he, ?_⟩
  intro y hy
  exact hpre (show (⟨y, hYL hy⟩ : localSpan L T) ∈ Y0.subgroupOf (localSpan L T) from hy)

/-- The four actual larger-field models reduce to a single SL₂ component.
The field degree is even, Y₀ lies in the original relative Borel, and every
choice of SL₂ coordinates has a conjugate Borel marking. -/
theorem source_rank_one_reduction_of_adequate
    (hclass : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} κ) (hYL : Y0 ≤ localSpan L T)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hm : FourModels (starImage H L) F) :
    starImage H L = starImage H (localSpan L T) ∧ Even n ∧
      Y0 ≤ localSpan L T ⊓
        normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) ∧
      Nonempty (starImage H (localSpan L T) ≃* SL(2,F)) ∧
      ∀ e : starImage H (localSpan L T) ≃* SL(2,F),
        ∃ g : SL(2,F), ∀ y : starImage H Y0,
          g * e ⟨y, (map_mono (comap_mono hYL)) y.property⟩ * g⁻¹ ∈
            Matrix.SpecialLinearGroup.rankOneBorel F := by
  obtain ⟨heq, ⟨e⟩, hB⟩ := source_four_models_reduction_of_adequate d hclass hYL n hF hn hm
  have hcard : Nat.card (Y0 ⧸ pCore 2 Y0) = 3 :=
    d.residual ▸ residual_quotient_card M Y V d.extraspecial
  have hq : 2 < Nat.card F := by
    rw [hF]
    calc
      2 = 2 ^ 1 := by norm_num
      _ < 2 ^ n := Nat.pow_lt_pow_right (by decide) hn
  have heven := even_degree_of_equiv H L Y0 T d.replacement d.commutator_eq
    d.sylow_normalizes (BorelInner.ModelSelection.sylow_in_H d)
    hcard hYL n hF hq e
  exact ⟨heq, heven, hB, ⟨e⟩, fun e' => every_equiv_borel_marking H L Y0 T
    d.replacement d.commutator_eq d.sylow_normalizes
    (BorelInner.ModelSelection.sylow_in_H d) hcard hYL hq e'⟩

/-- Source assembly for the larger-field Lie branch after 15.3.49(k).
The only classification premise is the full universal appendix implication;
the local application hypotheses and all concrete model geometry are proved.
The supplied Lie branch records actual model equivalences, not family tags. -/
theorem source_larger_field_reduction_of_adequate
    (hclass : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} κ) (hYL : Y0 ≤ localSpan L T)
    (n : ℕ) (hn : 1 < n) (hm : LieComponentModel (starImage H L) n) :
    starImage H L = starImage H (localSpan L T) ∧ Even n ∧
      Y0 ≤ localSpan L T ⊓
        normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 2 ^ n ∧ Nonempty (starImage H (localSpan L T) ≃* SL(2,F)) ∧
        ∀ e : starImage H (localSpan L T) ≃* SL(2,F),
          ∃ g : SL(2,F), ∀ y : starImage H Y0,
            g * e ⟨y, (map_mono (comap_mono hYL)) y.property⟩ * g⁻¹ ∈
              Matrix.SpecialLinearGroup.rankOneBorel F := by
  obtain ⟨F, hfield, hfinite, hchar, hF, hfour⟩ := four_models_of_lie hm hn
  let _ := hfield
  let _ := hfinite
  let _ := hchar
  obtain ⟨heq, heven, hB, he, hmark⟩ :=
    source_rank_one_reduction_of_adequate d hclass hYL n hF hn hfour
  exact ⟨heq, heven, hB, F, hfield, hfinite, hchar, hF, he, hmark⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
