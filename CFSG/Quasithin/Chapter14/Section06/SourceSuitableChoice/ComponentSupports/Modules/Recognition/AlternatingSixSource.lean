module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.AlternatingSixFullSupports
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.AlternatingSix.SourceMarking

/-!
# The original A₆ exclusion with all support inputs constructed

Recognize the original homogeneous seed, construct both marked natural
or five-dimensional covering sections, and exhaust the entire component
support. These literal sections discharge every premise of the existing
critical-pair A₆ consumer. The original hypotheses and residual component
identity are retained; no action, support, or vector callback remains.

Source: Aschbacher--Smith14.6.24(2), printed pp.1039--1041.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
open Chapter13.Section08.CriticalGeometry.Reorientation
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- The original normal A₆ alternative is impossible: construct both actual
covering sections and their full support, then apply the literal source consumer. -/
theorem source_normal_a6_false
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hr : (solvableResidual Mc).map Mc.subtype = K)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨hU,a,I,hI,⟨b⟩,_,_,_⟩ := terminal_single_a6_natural_seed
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr eK
  let := hU
  obtain ⟨s,j,σ,σ',⟨d⟩,⟨d'⟩,hm,hm',hfull,hpair,hconj,_,_⟩ :=
    source_normal_a6_full_supports_suitable
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr a hI b
  exact ComponentCriticalPair.AlternatingSix.source_no_alternatingSix_of_original_sections
    hG T hempty hM hunique hmany hcard e hab hsolv K hr hK j _ _ σ σ' d d' hm hm'
      ((originalSection a).subspacePreimage_le _) ((originalSection a).subspacePreimage_le _)
      hfull hpair s s.property hconj
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
