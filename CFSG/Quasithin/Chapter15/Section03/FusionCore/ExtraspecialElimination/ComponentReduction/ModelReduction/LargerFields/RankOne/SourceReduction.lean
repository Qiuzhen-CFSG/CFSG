module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.LieBorels

/-!
# Applying the model normalizers to the source component family

The full FF classification applies to the actual section action in
`SourceSetup` and makes L* quasisimple. All distinct T-conjugates of L*
therefore form a commuting family generating L₀*. Their actual conjugation
equivalences put them over the same field as L*; central overlaps are retained
until the concrete normalizer theorem excludes them. Intrinsic cubic control
comes from the source Sylow, theta, normalizer and order-three-quotient facts.

The four-model theorem then gives L* = L₀* and an SL₂ equivalence. Its Borel
argument also places Y₀* in the normalizer of the specified T₀*. The actual
quotient-kernel containment lifts this to Y₀ ≤ N_{L₀}(T₀). All local application
hypotheses are discharged; only the universal appendix classification and
the actual four-model branch remain inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49 after (k), printed p.1144; B.5.1 and B.5.6, pp.99–105.
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

/-- The genuine local hypotheses supply intrinsic cubic control on L₀*. -/
theorem source_cubic_control (hYL : Y0 ≤ localSpan L T) :
    CubicSylowControl (starImage H (localSpan L T))
      ((starImage H Y0).subgroupOf (starImage H (localSpan L T))) := by
  exact cubicSylowControl_star H M L Y0 T d.replacement d.commutator_eq
    d.sylow_normalizes (sylow_in_H d) d.sylow_le d.theta_eq d.normalizer_eq
    (d.residual ▸ residual_quotient_card M Y V d.extraspecial) hYL

omit d in
private theorem four_models_transport {D E : Type*} [Group D] [Group E]
    {F : Type} [Field F] (e : D ≃* E) (hm : FourModels D F) : FourModels E F := by
  rcases hm with h | h | h | h
  · exact Or.inl (h.map (e.symm.trans ·))
  · exact Or.inr (Or.inl (h.map (e.symm.trans ·)))
  · exact Or.inr (Or.inr (Or.inl (h.map (e.symm.trans ·))))
  · exact Or.inr (Or.inr (Or.inr (h.map (e.symm.trans ·))))

/-- Apply the full FF classification to obtain quasisimplicity, then collapse
all actual T-conjugate components by their concrete model normalizers. Borel
containment lifts through the star quotient because its kernel lies in T₀. -/
theorem source_four_models_reduction
    (hclass : CompleteClassificationInput.{u,u} κ) (hYL : Y0 ≤ localSpan L T)
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
      (Classification.sourceSetup_component_quotient_quasisimple d hclass)
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
    four_models_transport (LieBorels.factorEquiv d C) hm
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

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
