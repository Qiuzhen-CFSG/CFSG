module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.JankoLargeCenterRadical.CoverAssembly
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.JankoLargeCenterRadical.NativeQuotients
/-!
# The original unitary J₄ exclusion and odd-normalizer consequence

The completed native four-local theorem supplies the cover in the original
relative-Sylow argument. The source radical retains its whole module in its
center and its residual is normal in the whole native normalizer. This removes
the J₄ component and gives the original odd-actor uniqueness conclusion, with
only the original earlier-source hypotheses retained.

Source: Aschbacher--Smith 4.2.13 and 13.3.16; Kleidman--Wilson (1988),
Section 2, pp.488--493. The complete arbitrary-radical quotient theorem
now supplies the contradiction for the original marked residual.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers Chapter12.Section02
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
section Component
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original component cannot have the native J₄ central quotient. -/
theorem unitary_original_pushingUp_janko_false
    (s : Context T L V) {J H W : Subgroup G}
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
  (s : Context D.T D.L D.V)
  (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
