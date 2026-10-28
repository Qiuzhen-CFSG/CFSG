module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Adequate.Planes

/-!
# The original 13.6.10 obstruction through adequate B.5.6

Both classification bounds are proved on the literal quotient action.
The cubic-plane recovery uses the existing genuine B.5.7 earlier-source
interface. The original local hypotheses then reconstruct the forbidden
normality of V_v, giving the original non-subnormality conclusion.

The adequate B.5 implication and the earlier-source recovery inputs remain
explicit; this does not assert their unconditional discharge.
Source: Aschbacher–Smith, 13.6.10, printed p.928 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (internalUv (A5Module.markedZ s) (A5Module.markedV s))]
local notation "z₀" => A5Module.markedZ s
local notation "v₀" => A5Module.markedV s
local notation "Lstar" => starImage z₀ v₀ (Lv L v₀)

/-- Conditional source 13.6.10 with the corrected projective-line contract.
All the local premises are the same earlier-source data as above. The full
universal classification supplies actual group and module alternatives;
no selected component, branch impossibility or classification bound is input. -/
theorem marked_not_subnormal_of_adequate (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hV : IsPGroup 2 V) (hL : Lv L v₀ ≤ normalizer (V : Set G))
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hsplit : Vv L z₀ v₀ = zpowers v₀ ⊔ ⁅V, Lv L v₀⁆)
    (hsmall : Nat.card ↥(⁅V, Lv L v₀⁆ : Subgroup G) = 4)
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hnormal : ¬ ((Vv L z₀ v₀).subgroupOf (Gv v₀)).Normal)
    {𝒦 : GroupClass.{u}}
    (earlier : Classification.AdequateSource.EarlierSources.{u,u} 𝒦)
    (classification : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v₀))
    (hfull : Lstar = ⁅Lstar, starImage z₀ v₀
      (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆) :
    ¬ (Lstar).IsSubnormal := by
  intro hs
  obtain ⟨hdim, horbit⟩ := Classification.marked_bounds_of_adequate s T S hS hT
    hcore hcard hfull hs earlier classification hSQ
  exact contradiction_of_linear_classification_bounds L V T z₀ v₀
    (A5Module.markedZ_mem_Gv s) S hS hT hV hL hsplit hsmall hdim horbit hnormal

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal
