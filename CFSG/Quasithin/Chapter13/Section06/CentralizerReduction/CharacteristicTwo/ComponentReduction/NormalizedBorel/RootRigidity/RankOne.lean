module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ActionFacts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.RankOne.UnitaryExtensions
public import Theory.SpecificGroups.SL2.NormalizedRootCentralizers
public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers

/-!
# Rank-one root centralizers in the normalized component

The full model Sylow centers, with their additive coordinates, identify the
literal rootCenter in N(K)/C(K). Uniform centralizers in the actual model
Borels then exclude the marked a*/z* asymmetry. The parent supplies the
compatible model equivalence, Sylow alignment and Borel placement.
The imported extension branch also proves the residual reduction in the
full faithful unitary action, covering the genuine nonsplit alternative.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, with
1.1.5(3a,b), A.2.3–4 and A.3.16–18.
-/

public section
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- Uniform PSL₂ root centralizers transported through the compatible marking. -/
theorem linearTwo_root_centralizers (T : Subgroup G) {v : G} (K : Subgroup (Gv v))
    {F : Type*} [Field F]
    (e : PSL(2,F) ≃* NormalizerAction.componentImage K)
    (hU : (Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K))
    (hB : B ≤ (BenderSuzuki.Converse.PBorel F).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom))
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (XStar K)) =
      B ⊓ centralizer (rootCenter T K : Set (XStar K)) :=
  root_centralizers_of_model T K _ (Subtype.val_injective.comp e.injective)
    (Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F) _ hU B hB
    (Matrix.ProjectiveSpecialLinearGroup.NormalizedRootCentralizers.uniform F) r hr hne

/-- The actual PSL₂ application has no unproved root-centralizer premise. -/
theorem exclude_linearTwo [Finite G] (s : Marking L V)
    (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    {F : Type*} [Field F]
    (e : PSL(2,F) ≃* NormalizerAction.componentImage K)
    (hU : (Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hDB : residualStar s K ≤ B)
    (hB : B ≤ (BenderSuzuki.Converse.PBorel F).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom)) : False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER B hDB
    (linearTwo_root_centralizers T K e hU B hB)

open HermitianForm HermitianForm.BorelTorus

/-- Uniform PSU₃ root centralizers, retaining both field cardinalities. -/
theorem unitaryThree_root_centralizers (T : Subgroup G) {v : G} (K : Subgroup (Gv v))
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (e : ProjectiveSpecialUnitaryMatrixGroup J ≃* NormalizerAction.componentImage K)
    (hU : (projectiveRoot J hJ).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K))
    (hB : B ≤ (projectiveBorel J hJ).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom))
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (XStar K)) =
      B ⊓ centralizer (rootCenter T K : Set (XStar K)) :=
  root_centralizers_of_model T K _ (Subtype.val_injective.comp e.injective)
    (projectiveRoot J hJ) _ hU B hB
    (HermitianForm.NormalizedRootCentralizers.uniform J hn hcard hfixed hJ) r hr hne

/-- The actual PSU₃ application to the marked residual action. -/
theorem exclude_unitaryThree [Finite G] (s : Marking L V)
    (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (e : ProjectiveSpecialUnitaryMatrixGroup J ≃* NormalizerAction.componentImage K)
    (hU : (projectiveRoot J hJ).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hDB : residualStar s K ≤ B)
    (hB : B ≤ (projectiveBorel J hJ).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom)) : False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER B hDB
    (unitaryThree_root_centralizers T K J hJ hn hcard hfixed e hU B hB)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
