module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.FourModels

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.SourceReduction

/-!
# The larger-field rank-one reduction in 15.3.49

The genuine earlier local hypotheses and the complete universal appendix
classification make the selected star component quasisimple. Its actual
T-conjugates generate a central product inside L₀*. The four concrete
larger-field models and their normalizers reduce this family to one SL₂
component, giving L* = L₀* and an actual multiplicative equivalence.

The same geometry puts Y₀ in the original relative Borel. Its surviving
cubic element forces even defining-field degree. For every chosen SL₂
actor equivalence, one conjugator puts the entire image of Y₀* in the
standard Borel, so subsequent natural-module coordinates need no assumed
compatibility with the equivalence selected here.

`source_larger_field_reduction` assembles the larger-field Lie branch after
(k). The universal appendix classification remains an explicit permitted
input. Natural-module construction and the B.2.14 splitting belong to the
subsequent field-exclusion argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49 between (k) and (l), printed p.1144.
-/

public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
/-- The Borel marking works for every chosen actor equivalence. -/
theorem every_equiv_borel_marking (H L Y T : Subgroup G)
    (hgen : H = reducedOvergroup L Y T) (hcomm : L = ⁅L,Y⁆)
    (hn : T ≤ normalizer (Y : Set G)) (hT : IsSylowIn 2 T H)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3) (hYL : Y ≤ localSpan L T)
    (hq : 2 < Nat.card F) (e : starImage H (localSpan L T) ≃* SL(2,F)) :
    ∃ g : SL(2,F), ∀ y : starImage H Y,
      g * e ⟨y, (map_mono (comap_mono hYL)) y.property⟩ * g⁻¹ ∈
        Matrix.SpecialLinearGroup.rankOneBorel F := by
  have hLH : localSpan L T ≤ H := hgen ▸ le_sup_left
  have hle : starImage H Y ≤ starImage H (localSpan L T) := map_mono (comap_mono hYL)
  let C := (starImage H Y).subgroupOf (starImage H (localSpan L T))
  let a : starImage H Y ≃* C := (subgroupOfEquivOfLe hle).symm
  obtain ⟨S,hS⟩ := star_sylow_normalizes H L Y T hgen hcomm hn hT
  obtain ⟨g,hg⟩ := RankOne.exists_borel_conjugator_of_equiv C S hS
    (RankOne.cubes_mem_core_of_surjective a.toMonoidHom a.surjective
      (star_cubes H Y (hYL.trans hLH) hY)) hq e
  exact ⟨g, fun y => hg (a y)⟩

/-- A cubic element survives the two-core quotient and forces an even degree. -/
theorem even_degree_of_equiv (H L Y T : Subgroup G)
    (hgen : H = reducedOvergroup L Y T) (hcomm : L = ⁅L,Y⁆)
    (hn : T ≤ normalizer (Y : Set G)) (hT : IsSylowIn 2 T H)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3) (hYL : Y ≤ localSpan L T)
    (n : ℕ) (hF : Nat.card F = 2 ^ n) (hq : 2 < Nat.card F)
    (e : starImage H (localSpan L T) ≃* SL(2,F)) : Even n := by
  have hLH : localSpan L T ≤ H := hgen ▸ le_sup_left
  have hle : starImage H Y ≤ starImage H (localSpan L T) := map_mono (comap_mono hYL)
  obtain ⟨y,hy⟩ := star_cubic H Y (hYL.trans hLH) hY
  obtain ⟨g,hg⟩ := every_equiv_borel_marking H L Y T hgen hcomm hn hT hY hYL hq e
  let f : starImage H Y →* SL(2,F) :=
    (MulAut.conj g).toMonoidHom.comp (e.toMonoidHom.comp (inclusion hle))
  have hf : Function.Injective f := (MulAut.conj g).injective.comp
    (e.injective.comp (inclusion_injective hle))
  let b : Matrix.SpecialLinearGroup.rankOneBorel F := ⟨f y, hg y⟩
  exact RankOne.even_of_borel_cubic hF b
    ((Subgroup.orderOf_coe b).symm.trans ((orderOf_injective f hf y).trans hy))
open BorelInner
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

universe u
variable {G₁ : Type u} [Group G₁] [Finite G₁]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G₁}
    {T : Sylow 2 G₁} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

/-- The four actual larger-field models reduce to a single SL₂ component.
The field degree is even, Y₀ lies in the original relative Borel, and every
choice of SL₂ coordinates has a conjugate Borel marking. -/
theorem source_rank_one_reduction
    (hclass : CompleteClassificationInput.{u,u} κ) (hYL : Y0 ≤ localSpan L T)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hm : FourModels (starImage H L) F) :
    starImage H L = starImage H (localSpan L T) ∧ Even n ∧
      Y0 ≤ localSpan L T ⊓
        normalizer (((T : Subgroup G₁) ⊓ localSpan L T : Subgroup G₁) : Set G₁) ∧
      Nonempty (starImage H (localSpan L T) ≃* SL(2,F)) ∧
      ∀ e : starImage H (localSpan L T) ≃* SL(2,F),
        ∃ g : SL(2,F), ∀ y : starImage H Y0,
          g * e ⟨y, (map_mono (comap_mono hYL)) y.property⟩ * g⁻¹ ∈
            Matrix.SpecialLinearGroup.rankOneBorel F := by
  obtain ⟨heq, ⟨e⟩, hB⟩ := source_four_models_reduction d hclass hYL n hF hn hm
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
theorem source_larger_field_reduction
    (hclass : CompleteClassificationInput.{u,u} κ) (hYL : Y0 ≤ localSpan L T)
    (n : ℕ) (hn : 1 < n) (hm : LieComponentModel (starImage H L) n) :
    starImage H L = starImage H (localSpan L T) ∧ Even n ∧
      Y0 ≤ localSpan L T ⊓
        normalizer (((T : Subgroup G₁) ⊓ localSpan L T : Subgroup G₁) : Set G₁) ∧
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
    source_rank_one_reduction d hclass hYL n hF hn hfour
  exact ⟨heq, heven, hB, F, hfield, hfinite, hchar, hF, he, hmark⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
