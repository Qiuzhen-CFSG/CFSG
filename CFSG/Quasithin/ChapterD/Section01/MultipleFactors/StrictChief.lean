module
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceGenerators
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceQuadraticActor
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceChiefActions

/-!
# A strict chief-ratio obstruction at tensor ratio four thirds

Let an elementary normal module lie in a two-subgroup, and choose a maximum
elementary quadratic actor outside the residual core. Two noncentral chief
factors with ratio greater than two force fixed codimension strictly greater
than four times the actor rank modulo that core. Conjugate generators with
ratio at least four thirds, together with maximal elementary rank, give the
opposite bound. The actual qrc application therefore supplies a noncentral
chief factor whose faithful image has ratio at most two.

This is a numerical consequence of the original D.1.3 actor, chief-kernel,
and conjugate-generator estimates, with all quotient ranks kept literal.
Source: Aschbacher--Smith D.1.3, printed pp.173--175.
-/

public section
open Subgroup NoncentralChiefRefinement Representation Representation.BinaryOffender
open scoped ENNReal IsMulCommutative
namespace CFSG.Quasithin.ChapterD.MultipleFactors
variable {H : Type*} [Group H] [Finite H]
  (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]

theorem chiefFactor_rank_gt_twice (s : SeriesOn U) (A R₂ : Subgroup H)
    [IsElementaryAbelian 2 A] (hAR : ¬ A ≤ R₂)
    (hquad : IsQuadratic (normalRepresentation U) A)
    (i : Fin s.series.length)
    (hkernel : A ⊓ (s.factorRepresentation i).ker = A ⊓ R₂)
    (hratio : 2 < quadraticRatio (imageRepresentation (s.factorRepresentation i))) :
    2 * Nat.log 2 (R₂.relIndex A) < fixedCodim (s.factorRepresentation i) A := by
  let σ := s.factorRepresentation i
  have he : σ.ker.relIndex A = R₂.relIndex A := by
    rw [← inf_relIndex_left, hkernel, inf_relIndex_left]
  have hnot : ¬ A ≤ σ.ker := by
    intro hh
    apply hAR
    calc
      A = A ⊓ σ.ker := (inf_eq_left.mpr hh).symm
      _ = A ⊓ R₂ := hkernel
      _ ≤ R₂ := inf_le_right
  have hquadratic := chiefFactor_quadratic U s hquad i
  have hf := quadraticRatio_image_ne_top σ hnot hquadratic
  have hb := quadratic_image_rank_bound_real σ hquadratic hf (le_refl _)
  rw [he] at hb
  have hqR : (2 : ℝ) < (quadraticRatio (imageRepresentation σ)).toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by simp) hf).mpr hratio
  have ha : (0 : ℝ) < Nat.log 2 (R₂.relIndex A) := by
    exact_mod_cast quotient_rank_pos A R₂ hAR
  have hlt : (2 : ℝ) * Nat.log 2 (R₂.relIndex A) < fixedCodim σ A := by
    nlinarith
  exact_mod_cast hlt

theorem false_of_chief_ratio_gt_two_of_generator_ratio_four_thirds
    (s : SeriesOn U) (S A R₂ : Subgroup H)
    (hUS : U ≤ S) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (hAR : ¬ A ≤ R₂) (hc : 1 < s.noncentralCount)
    (hquad : IsQuadratic (normalRepresentation U) A)
    (hkernel : A ⊓ centralizer (U : Set H) ≤ R₂)
    (hfactor : ∀ i, ¬ s.Central i → A ⊓ (s.factorRepresentation i).ker = A ⊓ R₂)
    (hfactorRatio : ∀ i, ¬ s.Central i →
      2 < quadraticRatio (imageRepresentation (s.factorRepresentation i)))
    (W : ℕ → Subrepresentation ((normalRepresentation U).comp (A ⊓ R₂).subtype))
    (n : ℕ)
    (hgen : generatingSpan ((normalRepresentation U).comp (A ⊓ R₂).subtype) W n = ⊤)
    (hgenRatio : ∀ i < n, (4 / 3 : ℝ≥0∞) ≤
      quadraticRatio (imageRepresentation (W i).toRepresentation)) : False := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A ⊓ R₂ : Subgroup H) := IsElementaryAbelian.of_le inf_le_left
  have hqB : IsQuadratic (normalRepresentation U) (A ⊓ R₂) :=
    fun a ha b hb v => hquad a ha.1 b hb.1 v
  have hb := generator_rank_bound U (A ⊓ R₂) W (4 / 3) n
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) hgen hqB hgenRatio
  rw [actionKernel_quotient_rank] at hb
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat] at hb
  have hmono : fixedCodim (normalRepresentation U) (A ⊓ R₂) ≤
      fixedCodim (normalRepresentation U) A := by
    have hm : fixedSpace (normalRepresentation U) A ≤
        fixedSpace (normalRepresentation U) (A ⊓ R₂) := by
      intro v hv a
      exact hv ⟨a,a.property.1⟩
    have hr := Submodule.finrank_mono hm
    have ha := fixedCodim_add_finrank (normalRepresentation U) A
    have hb := fixedCodim_add_finrank (normalRepresentation U) (A ⊓ R₂)
    omega
  have hup := maxElementary_rank_upper U S A R₂ hUS hA hkernel
  have hlo := qrc_chief_factor_lower U s A
    ((2 * Nat.log 2 (R₂.relIndex A) + 1 : ℕ) : ℝ) (by
      intro i hi
      exact_mod_cast (Nat.succ_le_iff.mpr (chiefFactor_rank_gt_twice U s A R₂ hAR hquad i
        (hfactor i hi) (hfactorRatio i hi))))
  have hn : (2 : ℝ) ≤ s.noncentralCount := by exact_mod_cast (Nat.succ_le_iff.mpr hc)
  have ha : (0 : ℝ) ≤ Nat.log 2 (R₂.relIndex A) := Nat.cast_nonneg _
  have hmo : (fixedCodim (normalRepresentation U) (A ⊓ R₂) : ℝ) ≤
      fixedCodim (normalRepresentation U) A := by exact_mod_cast hmono
  push_cast at hlo
  nlinarith

end CFSG.Quasithin.ChapterD.MultipleFactors

namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

theorem source_exists_chief_ratio_le_two_of_four_thirds
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (hnf : letI := d.module_elementary
      ¬ IsFFModule (imageRepresentation G₁ V d.module_normalized))
    (hq : letI := d.module_elementary
      (4 / 3 : ℝ≥0∞) ≤ quadraticRatio (imageRepresentation G₁ V d.module_normalized))
    (s : SeriesOn ((conjugateSpan G₂ V).subgroupOf G₂)) (hc : 1 < s.noncentralCount) :
    letI := source_elementary_span_of_notFF d hV hnf
    letI : IsElementaryAbelian 2 ((conjugateSpan G₂ V).subgroupOf G₂) :=
      IsElementaryAbelian.subgroupOf ((span_le_right_core d hV).trans (twoCore_le G₂))
    ∃ i, ¬ s.Central i ∧ quadraticRatio
      (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ≤ 2 := by
  classical
  let := d.finite_left
  let := d.finite_right
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan G₂ V).subgroupOf G₂
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le G₂))
  dsimp only
  by_contra hn
  have hr : ∀ i, ¬ s.Central i → 2 < quadraticRatio
      (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) := by
    intro i hi
    exact lt_of_not_ge (fun hh => hn ⟨i,hi,hh⟩)
  obtain ⟨S,hS⟩ := d.sylow_right
  obtain ⟨A,hA,hAR,hquad⟩ := source_quadratic_max_actor d hne hV hnf S hS
  have hUS : U ≤ S := by
    intro u hu
    have ht : (u : G) ∈ T := (right_core_le_sylow d) ((span_le_right_core d hV) hu)
    rw [← hS] at ht
    obtain ⟨s,hs,he⟩ := ht
    exact G₂.subtype_injective he ▸ hs
  have hk : A ⊓ centralizer (U : Set G₂) ≤ pCore 2 G₂ :=
    (inf_le_inf_right _ hA.1).trans (source_span_centralizer_sylow_le_core d hne hV hnf S hS)
  obtain ⟨n,W,hgen,hgenRatio⟩ := exists_conjugateGenerator_sequence d hV
    (A ⊓ pCore 2 G₂) inf_le_right
  exact MultipleFactors.false_of_chief_ratio_gt_two_of_generator_ratio_four_thirds
    U s S A (pCore 2 G₂) hUS hA hAR hc hquad hk
    (fun i hi => MultipleFactors.source_chief_sylow_kernel U S
      (source_intrinsic_minimalParabolic_of_notFF d hne hnf S hS) s i hi A hA.1)
    hr W n hgen (fun i hi => hq.trans (hgenRatio i hi))
end CFSG.Quasithin.ChapterD.UniqueFactor
