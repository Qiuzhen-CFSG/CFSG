module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.MathieuPlacement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalComponents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.WholeModule
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source
public import Theory.Representation.MathieuCodeRestriction.CodeLocal

/-!
# The ordinary Mathieu exclusion in 14.7.36

The original point residual lies in the hypothetical Mathieu component,
so the entire literal U_I/V₁ is moved by that component. The actual R₁
quadratic actor and the native no-FF theorem make this whole section Irr⁺.
The proved small-quadratic classification identifies its central quotient
with the M₂₂ code, retaining the original group and linear markings.

The natural rank-two seed injects into this same central quotient. The
constructed hexad placement compares the actual two-cores; its radical
fixes only a line in the code. This contradicts the seed's dimension.
The full-point application uses the original residual marking, and the
component-selection consumer removes ordinary M₂₂ from its actual
intrinsic quotient. The retained earlier structural and classification
hypotheses have their existing source producers.
Source: Aschbacher–Smith, 14.7.36, printed p.1059, using F.9.18(7),
B.4.2/B.4.5 and H.16.2(1); refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
open Sporadic.Mathieu
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open Representation Representation.BinaryOffender
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam

/-- The literal code-module contradiction excludes M₂₂ in every original local. -/
theorem local_mathieu_component_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I C : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hCI : C ≤ I) (hC : (C.subgroupOf I).IsCComponent) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* M22) := by
  rintro ⟨e⟩
  let s := localMathieuSetup d h hab structural previous faithful earlier I C hI hCI hC e
  let := s.star_component_normal
  have hgenStar : Chapter13.Section08.Source.starImage I C ⊔
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 I)) = ⊤ := by
    apply top_unique
    rw [←s.star_component_join_sylow]
    exact sup_le_sup_left (map_mono (subgroupOf_mono I le_sup_right)) _
  obtain ⟨hU,a,_,A,hAR,hA,hq,hb,_⟩ := local_prime_supplement_quadratic_actor
    h hab structural previous I hI (Chapter13.Section08.Source.starImage I C) hgenStar
  let := hU
  let : IsElementaryAbelian 2 (Chapter13.Section08.Source.UH I V) := hU
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let act : SourceAction I V (F.Vi 1) := {
    representation := a.representation
    conjugation := a.conjugation }
  have ho := Recognition.F918Source.component_orbit s
  have hgen : I = conjugateSpanBy C (T : Subgroup G) ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) := by
    rw [ho,←sup_assoc]
    exact s.generated
  have hfull : subspaceCommutator act.representation ⊤
      (Chapter13.Section08.Source.starImage I C) = ⊤ := by
    have hh := source_moved_eq_top I V (F.Vi 1) act.representation
      (act.isSourceAction I V (F.Vi 1)) C (F.Li L 1) (T : Subgroup G) hgen
      (ho.symm ▸ s.seed_le_component)
      ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes)) (F.le_seed 1)
      (by rw [commutator_comm,←seed_commutator h F]; exact le_sup_left)
    rwa [ho] at hh
  have he := Recognition.F918Source.source_structure s
  have hn : ¬ Chapter13.Section08.Source.starImage I C ≤ act.representation.ker := by
    intro hk
    have hz : Chapter13.Section08.Source.starImage I C = ⊥ := by
      apply bot_unique
      intro k hkK
      exact a.faithful ((hk hkK).trans (map_one a.representation).symm)
    have hh := Recognition.F918Source.component_nonabelian s
    rw [hz] at hh
    exact hh inferInstance
  have hi : IsIrrPlus act.representation (Chapter13.Section08.Source.starImage I C) ⊤ := by
    have hh := Recognition.NativeSource.whole_isIrrPlus
      (Recognition.F918Source.fittingCoordinates s) act.representation (local_star_sqtk h I hI)
      (by rwa [he.1]) (by rwa [he.1])
      (A.map (QuotientGroup.mk' (pCore 2 I))) hA hq hb
    rwa [he.1] at hh
  have hIs : IsSQTK KnownSimple.IsKnownSimple I := by
    have hne : F.Vi 1 ≠ ⊥ := by
      intro hz
      have hc := F.card 1 (by decide)
      rw [hz,card_bot] at hc
      norm_num at hc
    have hH : IsTwoLocal F.H :=
      ⟨F.Vi 1,hne,IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hI.2.1)).mp
      ((h.source.simpleQTKE.twoLocal_sqtk hH).subgroup (I.subgroupOf F.H))
  have hcode := Recognition.F918Source.central_code s act hIs
    Recognition.NativeSource.smallQuadraticCode (⊤ : Subrepresentation act.representation)
    hi (A.map (QuotientGroup.mk' (pCore 2 I))) hA hq hb
  have hline : F.Vi 1 < V := by
    refine lt_of_le_of_ne (F.le_seed 1) ?_
    intro hz
    have hc := F.card 1 (by decide)
    have hV := F.card 3 (by decide)
    rw [hz] at hc
    rw [F.last] at hV
    norm_num at hc hV
    omega
  have hindex : ((F.Vi 1).subgroupOf V).index = 4 := by
    have hc := ((F.Vi 1).subgroupOf V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv] at hc
    have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    have hV : Nat.card V = 8 := by simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    rw [hp,hV] at hc
    omega
  exact source_central_code_contradiction_of_group_seed I C (F.Li L 1) (T : Subgroup G)
    F.H (normalizer (L : Set G)) V (F.Vi 1) s act hline hindex (seed_commutator h F).symm
    (sup_le ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
      (by simpa only [F.last] using F.invariant 3))
    (fun X hPX hXV hnX => F.invariant_subgroup_of_ambient_natural h.naturalMarking
      (by decide : 3 ≤ 3) X hPX hXV (le_sup_left.trans hnX))
    ⊤ hfull.symm hcode MathieuCode.m24OctadFixedLine

/-- Apply the whole-residual marking before the original point code contradiction. -/
theorem original_mathieu_component_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* M22) := by
  rintro ⟨e⟩
  obtain ⟨he,heK⟩ := original_mathieu_component_residual_marking
    d h hab structural previous faithful earlier C hC e
  have hKC : ((K F).subgroupOf F.H).IsCComponent := by
    rw [←he,subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective]
    exact hC
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  exact local_mathieu_component_impossible d h hab structural previous faithful earlier
    F.H (K F) hH (map_subtype_le _) hKC heK

/-- The original escaping component retains the full catalogue and excludes M₂₂. -/
theorem original_exists_non_mathieu_component_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ∃ C : Subgroup G, C ≤ F.H ∧ (C.subgroupOf F.H).IsCComponent ∧
      (C.subgroupOf F.H).Normal ∧ ¬ C ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ≤ normalizer (C : Set G) ∧
      C ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∈ F.Hz L (normalizer (L : Set G)) ∧
      Chapter13.Section08.Components.Models.F918Models (C ⧸ pCore 2 C) ∧
      SylowOvergroupComponentUnique C ∧ ¬ Nonempty ((C ⧸ pCore 2 C) ≃* M22) := by
  obtain ⟨C,hCH,hC,hn,he,hT,hJ,hm,hu⟩ := original_exists_normal_component_reduction
    d h hab structural previous faithful earlier (F := F)
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  exact ⟨C,hCH,hC,hn,he,hT,hJ,hm,hu,
    local_mathieu_component_impossible d h hab structural previous faithful earlier
      F.H C hH hCH hC⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
