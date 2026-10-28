module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.FlagDimensions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.SectionStructure.Assembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.CommutatorLift
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.BarQuotients
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.ChiefGeneration

/-!
# Assembly on the actual barred actor for 13.8.6(4)

Construct the relative elementary quotient U_L/V and its conjugation
representation on the source bar image using SectionStructure.Assembly.
The two marked natural modules imply the index-two flag. Applying the
universal earlier 13.7.7 noncentrality statement at the given H then proves
V∩U_H=V₃. Full L₁ difference generation on U_H/V₁ lifts across the retained
identity V₁=[V₃,O₂(L₁)]. The local image dimensions and recognition results
now give two natural planes which generate U_L/V and survive, with their
actual actions, in one irreducible quotient.

The lower-level theorem is conditional on the L₁ difference calculation and
the two specified S₃ quotients of the actual barred local images. The final
`exists_source_local_planes` entry point below constructs those inputs from
the chief-factor clause and the original natural coordinates, while retaining
the remaining parabolic outputs as explicit source hypotheses.
The parabolic U₂ outputs and exact universal earlier inputs are displayed.
No quotient structure, local plane identification, irreducibility or
Steinberg conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6(4), printed p.948 (PDF p.965), with Notation 12.2.5(2),
13.7.3, 13.7.7, 13.8.4(5) and F.9.2(3).
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]

/-- The two natural planes in the action constructed on the actual source bar image,
including their full generation and survival in one irreducible quotient. -/
def SourceLocalPlanes {L H T L₁ L₂ V V₂ V₃ : Subgroup G}
    (d : SectionStructure.Data L H T L₁ L₂ V V₂ V₃)
    (e₁ : (((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict ⧸
      pCore 2 (((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
        (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (e₂ : (((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict ⧸
      pCore 2 (((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
        (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3)) : Prop :=
  let _ := d.normal
  let _ := d.elementary
  let π := (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict
  let P₁ := ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map π
  let P₂ := ((L₂ ⊔ T).subgroupOf (L ⊔ T)).map π
  let S₁ := localImage (Source.UL L H V₃) V (L ⊔ T) π d.normalizes_UL d.action d.conjugation
    (L₁ ⊔ T) (Source.UH H V₃) d.normalizes_UH
  let S₂ := localImage (Source.UL L H V₃) V (L ⊔ T) π d.normalizes_UL d.action d.conjugation
    (L₂ ⊔ T) (Source.U2 H V V₂) d.normalizes_U2
  NaturalPlane S₁.toRepresentation e₁ ∧ NaturalPlane S₂.toRepresentation e₂ ∧
    Submodule.span (ZMod 2) {x | ∃ a, ∃ s : S₁, x = d.action a (s : _)} = ⊤ ∧
    Submodule.span (ZMod 2) {x | ∃ a, ∃ s : S₂, x = d.action a (s : _)} = ⊤ ∧
    ∃ W : Subrepresentation d.action, W ≠ ⊤ ∧ W.quotientRepresentation.IsIrreducible ∧
      Nonempty (S₁.toRepresentation.Equiv (localQuotientMap d.action P₁ S₁ W).range.toRepresentation) ∧
      Nonempty (S₂.toRepresentation.Equiv (localQuotientMap d.action P₂ S₂ W).range.toRepresentation) ∧
      Module.finrank (ZMod 2) (localQuotientMap d.action P₁ S₁ W).range.toSubmodule = 2 ∧
      Module.finrank (ZMod 2) (localQuotientMap d.action P₂ S₂ W).range.toSubmodule = 2

/-- Conditional assembly with the actual centralizer bar kernel. It
constructs every quotient-structure and action hypothesis of the local
plane helpers, applies the earlier noncentrality theorem to H, and lifts
the displayed L₁ difference input. The two local group identifications
and that difference input remain to be proved for final source assembly. -/
theorem exists_source_local_planes_of_difference_generation
    (L H K T L₁ L₂ G₁ M I₂ V V₁ V₂ V₃ : Subgroup G)
    [Finite G] [IsElementaryAbelian 2 V] [IsMulCommutative (conjugateSpanBy V G₁)]
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hHK : (H : Set G) = (K : Set G) * (T : Set G))
    (hK : (K.subgroupOf H).IsCComponent)
    (hcores : ∀ J ∈ Source.Hz L₁ T G₁ M,
      Source.UL L J V₃ ≤ (L ⊔ T).pCoreIn 2)
    (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hCT : T ⊓ centralizer (V : Set G) = (L ⊔ T).pCoreIn 2)
    (h13 : V₁ ≤ V₃) (h3V : V₃ ≤ V)
    (hT₂ : T ≤ normalizer (V₂ : Set G)) (hL₁ : L₁ ≤ L) (hL₂ : L₂ ≤ L)
    (hI : I₂ = conjugateSpanBy ((normalizer (V₁ : Set G)).pCoreIn 2)
      (normalizer (V₂ : Set G)))
    (hres : L₂ = (pResidual 2 I₂).map I₂.subtype)
    (η : Representation (ZMod 2) (Source.Hstar H) U)
    (s : ConjugationSection H (Source.UH H V₃) V₁ η)
    (hker : ∀ h : H, (∀ u : Source.UH H V₃, ⁅(h : G), (u : G)⁆ ∈ V₁) → h ∈ pCore 2 H)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ k : Source.starImage H K, ∀ u,
      E (η k u) = BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (eK k) (E u))
    (hmark : (s.image V₃).map E.toLinearMap = canonicalPlane)
    (hnoncentral : ∀ J ∈ Source.Hz L₁ T G₁ M,
      ¬ ⁅Source.VH J V, J⁆ ≤ Source.UH J V₃)
    (hU : Source.U2 H V V₂ ≤ Source.UL L H V₃)
    (hrank : let _ := SectionStructure.VH_commutative_of_global_span G₁ H V hH.2.1
      Module.finrank (ZMod 2) (Additive (Source.U2 H V V₂)) = 6)
    (hdiff : Coinvariants.ker (η.comp ((QuotientGroup.mk' (pCore 2 H)).comp
      (inclusion (le_sup_left.trans hH.1.2)))) = ⊤)
    (hV₁comm : V₁ = ⁅V₃, L₁.pCoreIn 2⁆)
    (hcomm₂ : Source.U2 H V V₂ = ⁅Source.U2 H V V₂, L₂⁆)
    (e₁ : (((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V n.normalizes_V).rangeRestrict ⧸
      pCore 2 (((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
        (barMap (L ⊔ T) V n.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (e₂ : (((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V n.normalizes_V).rangeRestrict ⧸
      pCore 2 (((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
        (barMap (L ⊔ T) V n.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (hgen : V = conjugateSpanBy V₃ L₂) :
    ∃ d : SectionStructure.Data L H T L₁ L₂ V V₂ V₃, SourceLocalPlanes d e₁ e₂ := by
  have hline : V₁ ≠ ⊥ := by
    intro hz
    have hc := original_V1_card L T V V₁ n hfixed
    rw [hz] at hc
    simp at hc
  have hinter : V ⊓ Source.UH H V₃ = V₃ :=
    (flag_intersection_of_index_two V V₃ (Source.UH H V₃)
      (le_inf h3V (le_conjugateSpanBy V₃ H))
      (source_flag_index L H T V V₁ V₃ n hfixed η s h13 h3V E hmark)
      (seed_not_le_UH_of_noncentral H V V₃ (hnoncentral H hH))).symm
  obtain ⟨d⟩ := SectionStructure.exists_source_structure L H K T L₁ L₂ G₁ M I₂ V V₁ V₂ V₃
    hH hHK hK hcores n hfixed hCT hline h13 h3V hT₂ hL₂ hI hres η s hker eK E he hmark
  let _ := d.normal
  let _ := d.elementary
  let _ := SectionStructure.VH_commutative_of_global_span G₁ H V hH.2.1
  have hcomm₁ := UH_eq_commutator_of_coinvariants H L₁ V₁ V₃
    (le_sup_left.trans hH.1.2) η s hdiff hV₁comm
  have hKL : Source.K2 H V₂ ≤ normalizer (L₂ : Set G) :=
    ((Source.K2_le_centralizer H V₂).trans inf_le_right).trans
      ((centralizer_le_normalizer _).trans
        (TransvectionParabolic.local_normality I₂ L₂ _ V₂ hI hres))
  refine ⟨d, ?_⟩
  exact local_planes_of_source_commutators L H T L₁ L₂ V V₁ V₂ V₃
    (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict d.normalizes_UL d.action d.conjugation
    d.normalizes_UH d.normalizes_U2 n hfixed hL₁ hL₂ η s h13 E hmark hinter hU hrank
    hcomm₁ hcomm₂ e₁ e₂ hgen hKL

/-- Source assembly with the two remaining local inputs constructed from their
literal source descriptions.  The chief-factor calculation supplies the
`L₁` difference generation, while the original natural coordinates supply the
two barred local `S₃` quotients and the conjugate-span generation of `V`.
The equivalences in the conclusion are the actual images under the bar map;
no abstract parabolic actor is substituted for either image. -/
theorem exists_source_local_planes
    (L H K T L₁ L₂ G₁ M I₂ V V₁ V₂ V₃ : Subgroup G)
    [Finite G] [IsElementaryAbelian 2 V] [IsMulCommutative (conjugateSpanBy V G₁)]
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hHK : (H : Set G) = (K : Set G) * (T : Set G))
    (hK : (K.subgroupOf H).IsCComponent)
    (hcores : ∀ J ∈ Source.Hz L₁ T G₁ M,
      Source.UL L J V₃ ≤ (L ⊔ T).pCoreIn 2)
    (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hCT : T ⊓ centralizer (V : Set G) = (L ⊔ T).pCoreIn 2)
    (h13 : V₁ ≤ V₃) (h3V : V₃ ≤ V)
    (hT₂ : T ≤ normalizer (V₂ : Set G)) (hL₁ : L₁ ≤ L) (hL₂ : L₂ ≤ L)
    (hI : I₂ = conjugateSpanBy ((normalizer (V₁ : Set G)).pCoreIn 2)
      (normalizer (V₂ : Set G)))
    (hres : L₂ = (pResidual 2 I₂).map I₂.subtype)
    (η : Representation (ZMod 2) (Source.Hstar H) U)
    (s : ConjugationSection H (Source.UH H V₃) V₁ η)
    (hker : ∀ h : H, (∀ u : Source.UH H V₃, ⁅(h : G), (u : G)⁆ ∈ V₁) → h ∈ pCore 2 H)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ k : Source.starImage H K, ∀ u,
      E (η k u) = BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (eK k) (E u))
    (hmark : (s.image V₃).map E.toLinearMap = canonicalPlane)
    (hnoncentral : ∀ J ∈ Source.Hz L₁ T G₁ M,
      ¬ ⁅Source.VH J V, J⁆ ≤ Source.UH J V₃)
    (hU : Source.U2 H V V₂ ≤ Source.UL L H V₃)
    (hrank : let _ := SectionStructure.VH_commutative_of_global_span G₁ H V hH.2.1
      Module.finrank (ZMod 2) (Additive (Source.U2 H V V₂)) = 6)
    (earlier : ChiefGeneration.Earlier1376ChiefFactors L₁ T G₁ M V₃ V₁)
    (hV₁comm : V₁ = ⁅V₃, L₁.pCoreIn 2⁆)
    (hcomm₂ : Source.U2 H V V₂ = ⁅Source.U2 H V V₂, L₂⁆)
    (hV₂V₃ : V₂ ≤ V₃) (hcard₂ : Nat.card V₂ = 4)
    (hL₁source : L₁ = BarQuotients.sourceResidual L T V₁)
    (hL₂source : L₂ = BarQuotients.sourceResidual L T V₂)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6)) :
    ∃ d : SectionStructure.Data L H T L₁ L₂ V V₂ V₃,
      ∃ e₁ : (((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
          (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict ⧸
          pCore 2 (((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
            (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3),
      ∃ e₂ : (((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
          (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict ⧸
          pCore 2 (((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
            (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3),
        SourceLocalPlanes d e₁ e₂ := by
  have hKH : K ≤ H := by
    intro k hk
    change k ∈ (H : Set G)
    rw [hHK]
    exact ⟨k, hk, 1, T.one_mem, mul_one k⟩
  have hdiff := ChiefGeneration.coinvariants_eq_top_of_earlier
    L₁ T G₁ M H K V₃ V₁ earlier hH hKH hK η s eK E he
  have hindex := source_flag_index L H T V V₁ V₃ n hfixed η s h13 h3V E hmark
  obtain ⟨q₁, q₂, hgen⟩ :=
    BarQuotients.source_quotients_and_generation_of_card n hfixed e V₂ V₃ L₁ L₂
      hV₂V₃ h3V hcard₂ hT₂ hindex hL₁source hL₂source
  obtain ⟨d, hplanes⟩ := exists_source_local_planes_of_difference_generation
    L H K T L₁ L₂ G₁ M I₂ V V₁ V₂ V₃ hH hHK hK hcores n hfixed hCT h13 h3V hT₂
      hL₁ hL₂ hI hres η s hker eK E he hmark hnoncentral hU hrank hdiff hV₁comm
      hcomm₂ q₁.some q₂.some hgen
  exact ⟨d, q₁.some, q₂.some, hplanes⟩
end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

end
