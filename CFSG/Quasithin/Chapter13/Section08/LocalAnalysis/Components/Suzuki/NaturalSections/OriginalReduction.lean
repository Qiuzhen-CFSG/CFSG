module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Original
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# The original Suzuki contradiction reduced to its natural central sections

The actual natural A₆ flag gives [V₃,L₁] = V₃. Its image generates the
literal quotient U_H/V₁ under H*, and the Borel argument proves L₁* normal
in H*. Consequently [Ũ_H,L₁*] = Ũ_H. On the other hand L₁* centralizes
K₀* and has order 2^r 3^s. On a natural Suzuki central section, its action
is scalar and hence trivial; the same holds for the two-factor natural
section. Perfect commutator generation lifts fixation to [Ũ_H,K₀*].
The commuting-actions identity then makes K₀* fix all of Ũ_H, contradicting
the faithful original action.

This is a conditional source reduction: recognition of the whole moved
central section, in the single or exchanged orbit, remains to be supplied
from F.9.18 and the earlier module classifications. It assumes neither a
splitting of the moved module nor equality of that module with Ũ_H.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.16, printed pp.952–953, and 13.7.3(6), printed p.936.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
  (hρ : IsSourceAction H V₃ V₁ ρ)

include d hρ in
/-- Full seed generation is proved on the original natural flag and
transported through its literal quotient map. -/
theorem original_seed_commutator (hLH : one L T V₁ ≤ H) :
    subspaceCommutator ρ (sourceSeedSpace H V₃ V₁) (Source.starImage H (one L T V₁)) =
      sourceSeedSpace H V₃ V₁ := by
  apply Swapped.LinearTwo.ModuleAlternatives.image_commutator_eq H V₃ V₁ ρ hρ
    (one L T V₁) V₃ hLH (le_conjugateSpanBy V₃ H)
    (Section07.ModelExclusions.point_residual_normalizes_seed (localNaturalSetup d))
    (d.line_le_uh H)
  rw [commutator_comm, Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup d)]
  exact le_sup_left

include hρ in
/-- F.9's exact centralizer identity gives faithfulness for any action
with the prescribed representative conjugation formula. -/
theorem original_action_faithful
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    Function.Injective ρ := by
  apply sourceAction_injective H V₃ V₁ ρ hρ
  have hkernel : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁ := by
    have he := f9_commutatorPreimage_eq _ hF9 H le_rfl
    exact (he.trans (inf_eq_right.mpr (map_subtype_le _))).symm
  intro x hx
  have hxQ : (x : G) ∈ Source.QH H := by
    rw [hkernel]
    exact (mem_commutatorPreimage_iff _ _ _
      (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) _).mpr
        ⟨x.property, fun u hu => hx ⟨u, hu⟩⟩
  obtain ⟨y, hy, he⟩ := hxQ
  exact (Subtype.ext he : y = x) ▸ hy

variable
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  {m : ℕ} (hm : 0 < m)
  (eK : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)

include d hρ h hF9all hcentral hcomm hsource hH hKH hK hgen hm eK in
/-- Both Suzuki orbit cases contradict the source once their natural
central section is recognized. All Borel, faithfulness and seed inputs
are discharged here on the original quotient and component orbit. -/
theorem original_natural_sections_impossible
    (hsections : HasNaturalCentralSection H V₃ V₁ ρ K T m ∨
      HasPairedNaturalCentralSection H V₃ V₁ ρ K T m) : False := by
  obtain ⟨hc, hn, r, s, hcard⟩ :=
    BorelSource.original_group_action d h hF9all hcentral hcomm hsource hH hKH hK hgen hm eK
  let := hn
  have hgenerated : subspaceCommutator ρ ⊤ (Source.starImage H (one L T V₁)) = ⊤ := by
    apply commutator_top_of_orbit_seed ρ ⊤ (Source.starImage H (one L T V₁))
      (sourceSeedSpace H V₃ V₁) le_normalizer_of_normal
    · exact original_seed_commutator d ρ hρ (le_sup_left.trans hH.1.2)
    · simpa using sourceSeed_orbit_span H V₃ V₁ ρ hρ
  let : IsQuasisimple (Source.starImage H K) :=
    (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  have hWK := movedSpace_stable H V₃ V₁ ρ K T
  have hWL := movedSpace_stable_of_normalizes H V₃ V₁ ρ K T
    (Source.starImage H (one L T V₁)) (hc.trans (Subgroup.centralizer_le_normalizer _))
  have hWgen := movedSpace_generated H V₃ V₁ ρ K T hKH (le_sup_right.trans hH.1.2)
  have hfixed : movedSpace H V₃ V₁ ρ K T ≤ fixedSpace ρ (Source.starImage H (one L T V₁)) := by
    rcases hsections with ⟨φ, hφ, e, he⟩ | ⟨φ, hφ, e, he⟩
    · exact central_extension_fixed_of_natural ρ _ _ _ hWK hWL hc hWgen m r s hcard φ hφ e he
    · exact central_extension_fixed_of_naturalPair ρ _ _ _ hWK hWL hc hWgen m r s hcard φ hφ e he
  apply contradiction_of_commutator_fixed ρ (orbitActor H K T)
    (Source.starImage H (one L T V₁)) _ hgenerated hfixed
    (componentOrbitStar_not_fixed H K T ρ (original_action_faithful ρ hρ (hF9all H hH)))
  intro l hl k hk
  exact (show Commute k l from mem_centralizer_iff.mp (hc hl) k hk).symm

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections
