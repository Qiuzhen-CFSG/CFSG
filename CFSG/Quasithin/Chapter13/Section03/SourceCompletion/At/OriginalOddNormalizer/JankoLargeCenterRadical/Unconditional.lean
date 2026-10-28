module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.JankoLargeCenterRadical.Unconditional
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.JankoLargeCenterRadical.CoverAssembly
/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.JankoLargeCenterRadical.Unconditional`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers Chapter12.Section02
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
section Component
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original component cannot have the native J₄ central quotient. -/
theorem unitary_original_pushingUp_janko_false
    (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V) {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) : False := by
  obtain ⟨hP,hlarge,_,hn,⟨b⟩⟩ :=
    unitary_original_pushingUp_janko_radical s hcover hJH hc K hK e
  let := hn
  exact Janko4.LocalStructure.LargeCenterRadicals.unitary_radical_false _ hP hlarge _ b

end Component

section OriginalFlag
variable (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
  (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context D.T D.L D.V)
  (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
  (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
  (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
  (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
  (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
  (B : Subgroup G) (hBV : B ≤ D.V)
  (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
  (hHfull : D.H = normalizer (D.V₁ : Set G))
  (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
  (fixed : OriginalFixedModule1332At D.T D.L)
  (five : OriginalAlternatingFiveModules1332At D.T D.L)

include s earlier hUV hZV hTZ hTU hZ hU hBV hTB hB hHfull h1332 fixed five

/-- The actual odd-actor residual has its original unique maximal overgroup.
The complete native cover has no remaining geometry or action premise. -/
theorem unitary_original_oddActorResidual_unique
    (A : Subgroup G) (hAN : A ≤ normalizer (D.L : Set G))
    (hcomm : ⁅A,D.L⁆ ≤ D.L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (D.V : Set G)) :
    UniqueMaximalOvergroup (oddActorResidual D.L A) (normalizer (D.L : Set G)) := by
  exact unitary_original_oddActorResidual_unique_of_janko_cover
    D s earlier hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull h1332 fixed five
    Janko4.LocalStructure.PureFirstNormalizers.CompleteCover.maximalTwoLocalCover A hAN hcomm hodd hAV

end OriginalFlag
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
