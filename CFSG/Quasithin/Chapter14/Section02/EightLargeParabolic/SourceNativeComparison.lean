module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.LinearHexagonExchange
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartanPaths
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePathProfile
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCenterProfile

/-!
# The original triality marking from six-path exchange

The original Borel calculation identifies the reduced Sylow with T. The actual
binary and eight-field quotient markings, seven-path transitivity, and odd
fixers construct the native triality comparison from exchange. Reversing both
endpoint maps restores the original H and second parabolic, with their full
intersection retained.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceNativeComparison
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open Reduction OriginalExtension
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
local notation "Fₛ" => reducedFamily Lₛ Sₛ


set_option maxHeartbeats 800000 in
/-- Exchange on the original mixed pair gives its complete marked triality
realization, including the full original Borel. -/
theorem source_marked_triality_of_six_exchange
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ))
    (t : Bool → (reducedAmalgam Lₛ Sₛ).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam Lₛ Sₛ)) i =
      base (Universal.cosetFamily (reducedAmalgam Lₛ Sₛ)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam Lₛ Sₛ)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam Lₛ Sₛ)) (!i))
    (htsq : ∀ i, t i * t i = 1)
    (htnorm : ∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam Lₛ Sₛ).Universal))
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam Lₛ Sₛ).Universal)
      (sourceGraph (reducedAmalgam Lₛ Sₛ))
      (cartanApartment (reducedAmalgam Lₛ Sₛ) (reflectionGroup c t)) 6) :
    Nonempty (MarkedTriality T M Mc H) := by
  let h : HypothesisF11 Lₛ Sₛ :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  obtain ⟨eU⟩ := SourceBinaryCenterProfile.source_binary_marking hG T hempty hM hu hmany hcard e H hH eR
  let μ (i : Bool) : (Lₛ (if i then 1 else 0) ⧸ pCore 2 (Lₛ (if i then 1 else 0))) ≃* SL(2,pathFields i) := by
    cases i
    · exact (path_field_markings (residualQuotientEquiv H eR) eU false).trans
        (Theory.PSL2.sl2QuotientEquiv (pathFields false)).symm
    · exact (path_field_markings (residualQuotientEquiv H eR) eU true).trans
        (Theory.PSL2.sl2QuotientEquiv (pathFields true)).symm
  obtain ⟨_,htrans,hodd⟩ := eight_pair_path_profile
    (K := locals T M Mc H 0) (U := locals T M Mc H 1) (S := Sₛ)
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
    (residualQuotientEquiv H eR) eU
  obtain ⟨_,⟨cmp⟩⟩ := unequal_linear_comparison_of_exchange (G := G) (L := Lₛ) (S := Sₛ) (k := pathFields) h μ c t htfix htmove htsq htnorm
    htrans hodd hexchange (a := 1) (b := 3) (by decide) (by decide)
    (by change Nat.card (ZMod 2) = 2^1; norm_num [Nat.card_zmod])
    (by change Nat.card (GaloisField 2 3) = 2^3; exact GaloisField.card 2 3 (by decide))
  have hs : reducedSylow Lₛ Sₛ = Sₛ :=
    (SourceCartanPaths.source_borel_and_sylow hG T hempty hM hu hmany hcard e H hH eR).2
  let P₀ := parabolic Lₛ (reducedSylow Lₛ Sₛ) 0
  let P₁ := parabolic Lₛ (reducedSylow Lₛ Sₛ) 1
  have hP₀ : P₀ = secondParabolic T M Mc H := by
    dsimp only [P₀]
    rw [hs]
    exact (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.1
  have hP₁ : P₁ = H := by
    dsimp only [P₁]
    rw [hs]
    exact (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1
  let j : Iso (amalgam T M Mc H)
      (Chapter6.Source.RankOneGeneric.Global.sourceParabolicAmalgam Lₛ (reducedSylow Lₛ Sₛ)).reverse :=
    NativeRestoration.subgroupCongrIso inf_le_left inf_le_right inf_le_right inf_le_left hP₁.symm
      (by change H ⊓ secondParabolic T M Mc H = P₀ ⊓ P₁
          rw [hP₀,hP₁,inf_comm]) hP₀.symm
  exact ⟨j.trans cmp.reverse⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceNativeComparison
