module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalQuotients
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MathieuTwentyFour

/-!
# Placement of the J₄ branch's local M₂₄ quotient

The original module construction applies to every characteristic-two member
of L(G₁,S) outside M_Z. It gives the full FF group catalogue for the literal
normalizer image. Simplicity of M₂₄ makes the induced surjection from K/O₂(K)
injective; the catalogue's checked orders then give a contradiction.

This discharges the local-containment step in Aschbacher--Smith 15.1.20(3),
printed p.1097. Construction of the actual J₄ local subgroup and final
ordinary-catalogue assembly remain with the ordinary pre-exclusion owner.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC.C27Source

open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- A characteristic-two local-family member with actual M₂₄ two-core quotient
lies in M_Z. This applies to arbitrary members of L(G₁,S), including the
local subgroup used to exclude the ordinary J₄ component. -/
theorem localFamily_mathieuTwentyFour_le_MZ (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : generalizedFitting K = pCore 2 K)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) : K ≤ d.MZ := by
  by_contra hout
  obtain ⟨a,hm⟩ := d.localFamily_catalogue hG hempty hM hJ hu h hK hq hout hf
  let := Sporadic.Mathieu.m24_isSimpleGroup
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  let : IsQuasisimple (d.normalizerImage K) := a.quasisimple
  let : IsSimpleGroup ((d.normalizerImage K) ⧸ center (d.normalizerImage K)) := IsQuasisimple.simple
  let : Nontrivial (d.normalizerImage K) := (QuotientGroup.mk'_surjective (center _)).nontrivial
  have hi : Function.Injective a.coreToImage := by
    apply a.coreToImage.ker_eq_bot_iff.mp
    rcases a.coreToImage.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · have he := a.coreToImage.ker_eq_top_iff.mp ht
      obtain ⟨x,hx⟩ := exists_ne (1 : d.normalizerImage K)
      obtain ⟨y,rfl⟩ := a.coreToImage_surjective x
      exact (hx (by rw [he]; rfl)).elim
  exact StarModels.not_mathieuTwentyFour hm ((MulEquiv.ofBijective a.coreToImage ⟨hi,a.coreToImage_surjective⟩).symm.trans e)
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
