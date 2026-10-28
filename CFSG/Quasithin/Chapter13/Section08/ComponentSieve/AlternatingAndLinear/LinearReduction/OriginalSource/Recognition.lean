module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.MiddleNode
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource.Strict

/-!
# Whole-module assembly after the original binary quotient reduction

The uniform seven-point exclusion is applied to the actual normal component
and supplement constructed from 13.8.21. The quotient reduction then gives
the covered local quotient, H* ≃ L₄(2), and H = G₁. On the literal U_H/V₁
we retain both critical cases: a transvection invokes 13.8.5, while absence
of transvections invokes the proved strict whole-module argument.

The marked middle-node exclusion is still an explicit local obligation.
The preceding source and component inputs retain their original contracts;
this conditional assembly is not a completed proof of 13.8.25.
Final discharge belongs to qt-d-138-linear-source, with the preceding field
conclusions supplied by qt-d-138-fields-source.

Source: Aschbacher–Smith, 13.8.24–25, printed pp.958–962/PDF pp.975–979.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FourStructure.ChiefFactors SourceCompletion
open Chapter1.Section02.LocalModels Chapter2.ComponentRefinement.LieType.Binary
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
  (localEarlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G))
  (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
  (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (components : ComponentConclusions (one L T V₁) T G₁ M)

include d earlier localEarlier hG64 hmax hF9all hcentral hcomm hsource components

/-- The earlier A₇ theorem at the actual components used by the overgroup
reduction. Relative normality, the supplement, theta and the solvable-overgroup
premise are supplied from the original source setup. -/
theorem not_alternatingSeven_source
    {H K : Subgroup G} (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    ¬ IsAlternating (K ⧸ pCore 2 K) 7 := by
  have groups := group_facts d hmax hF9all hcentral hcomm hsource components
  exact Seven.OriginalSource.not_alternatingSeven_reduced d earlier localEarlier hG64
    hH (hF9all H hH) hcentral hcomm hKH hK (groups.component_normal hH hKH hK)
    (groups.supplement hH hKH hK).symm (components.base_le hH hKH hK)
    (groups.theta H hH) groups.solvable_overgroups

/-- All conclusions of the linear branch, conditional on the remaining marked
middle-node exclusion. The A₇ exclusion, actual H = G₁ construction and both
whole-module cases have no further callbacks. In particular the module is the
whole literal U_H/V₁, with a compatible actor and linear marking. -/
theorem source_linear_alternative_of_middle_exclusion
    (hmiddle : ∀ (J C : Subgroup G) (_hJ : J ∈ Source.Hz (one L T V₁) T G₁ M)
      (hCJ : C ≤ J) (hC : (C.subgroupOf J).IsCComponent)
      (e : (C ⧸ pCore 2 C) ≃* PSL 4),
      ¬ Parabolics.MiddleNodeMarking J C (one L T V₁) T hCJ hC e)
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) :
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Nonempty (Source.Hstar H ≃* PSL 4) ∧
      (∃ (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
        (eU : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] NaturalSpace),
        (∀ a v, eU (ρ a v) = eH a (eU v)) ∧
        Module.finrank (ZMod 2) (SourceSpace H V₃ V₁) = 4) ∧ H = G₁ := by
  classical
  have groups := group_facts d hmax hF9all hcentral hcomm hsource components
  obtain ⟨hn, hcover, ⟨eH⟩, hHG⟩ := source_linear_reduction_of_middle_exclusion
    d hmax hF9all hcentral hcomm hsource components hmiddle
    (fun hJ hCJ hC => not_alternatingSeven_source d earlier localEarlier hG64 hmax
      hF9all hcentral hcomm hsource components hJ hCJ hC) hH hKH hK hn₀ hn₁ hmodel
  have hcovered : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
    rcases local_quotient_alternatives d with ⟨e, _⟩ | ⟨e, _⟩
    · obtain ⟨f⟩ := hcover.2.1
      have hz := Nat.card_congr (f.symm.trans (centerCongr e)).toEquiv
      have hc : Nat.card (Multiplicative (ZMod 3)) = 3 := by
        simp [Nat.card_eq_fintype_card]
      rw [hc, alternatingGroup.center_eq_bot (by simp), card_bot] at hz
      omega
    · exact ⟨e⟩
  refine ⟨hn, hcover, hcovered, ⟨eH⟩, ?_, hHG⟩
  by_cases ht : ∃ a : Source.Hstar H, fixedCodim ρ (zpowers a) = 1
  · obtain ⟨a, ha⟩ := ht
    exact (TransvectionSource.natural_four d earlier localEarlier hG64 hH ρ hρ eH a ha).2
  · have hno : ∀ a : Source.Hstar H, fixedCodim ρ (zpowers a) ≠ 1 := by
      simpa only [not_exists] using ht
    have eK : Nonempty ((K ⧸ pCore 2 K) ≃* PSL 4) := by
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
      let : Fintype F := Fintype.ofFinite F
      let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
      exact ⟨hn ▸ e.trans (Atlas.fieldEquivPSL n eF)⟩
    obtain ⟨eK⟩ := eK
    let : IsQuasisimple (alternatingGroup (Fin 8)) := {
      toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      simple := by
        let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
        exact ((QuotientGroup.quotientMulEquivOfEq
          (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
    have hqs : IsQuasisimple (Source.starImage H K) :=
      IsQuasisimple.of_mulEquiv ((Parabolics.starLinearEquiv H K hKH hK eK).trans
        Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).symm
    exact FourStructure.OriginalSource.natural_module_of_no_transvections_source d hmax
      hH (hF9all H hH) hcentral hcomm hcovered hK (groups.component_normal hH hKH hK)
      hqs (components.base_le hH hKH hK) (groups.supplement hH hKH hK).symm eK hHG ρ hρ hno

/-- The complete conditional linear assembly with the middle-node geometry
and quotient selection discharged. The two marked B.4 classifications are the
remaining local proof obligations, retained by this source assembly owner. -/
theorem source_linear_alternative_of_b4
    (hSym : ∀ (J C : Subgroup G), J ∈ Source.Hz (one L T V₁) T G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent →
      ∀ eJ : Source.Hstar J ≃* Equiv.Perm (Fin 8),
      (Source.starImage J C).map eJ.toMonoidHom = alternatingGroup (Fin 8) →
      OrthogonalQuotient.B4Extraction.SymmetricB4.{u} (Source.starImage J C) eJ)
    (hComp : ∀ (J C : Subgroup G), J ∈ Source.Hz (one L T V₁) T G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent →
      ∀ (eJ : Source.Hstar J ≃* Equiv.Perm (Fin 8))
        (eC : Source.starImage J C ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace),
      (Source.starImage J C).map eJ.toMonoidHom = alternatingGroup (Fin 8) →
      OrthogonalQuotient.B4Extraction.ComponentB4.{u} (Source.starImage J C) eJ eC)
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) :
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Nonempty (Source.Hstar H ≃* PSL 4) ∧
      (∃ (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
        (eU : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] NaturalSpace),
        (∀ a v, eU (ρ a v) = eH a (eU v)) ∧
        Module.finrank (ZMod 2) (SourceSpace H V₃ V₁) = 4) ∧ H = G₁ := by
  have groups := group_facts d hmax hF9all hcentral hcomm hsource components
  apply source_linear_alternative_of_middle_exclusion d earlier localEarlier hG64 hmax
    hF9all hcentral hcomm hsource components ?_ hH hKH hK hn₀ hn₁ hmodel ρ hρ
  intro J C hJ hCJ hC e hm
  exact middle_node_exclusion_of_b4 d earlier localEarlier hG64 hJ (hF9all J hJ)
    hcentral hcomm hCJ hC (groups.component_normal hJ hCJ hC)
    (components.base_le hJ hCJ hC) (groups.supplement hJ hCJ hC).symm
    (hSym J C hJ hCJ hC) (hComp J C hJ hCJ hC) e hm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
