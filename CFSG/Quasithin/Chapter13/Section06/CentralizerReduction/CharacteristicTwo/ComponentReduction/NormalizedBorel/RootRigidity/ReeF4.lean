module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ActionFacts
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers

/-!
# Ree–F₄ root centralizers in the literal component quotient

The genuine Ree Borel calculation transports through the specified component
isomorphism and the actual Sylow intersection in X* = N(K)/C(K). It then
contradicts the marked a*/z* action asymmetry.

The full positive-subgroup center identification is proved by fixed-coordinate
commutator calculations in the Theory module's imports. Thus the final
`reeF4_root_centralizers` and `exclude_reeF4` discharge that premise in the
Ree branch of 13.6.6. The earlier conditional interfaces are preserved.
The parent `RootRigidity` assembly retains the actual model equivalence,
normalized Sylow arrangement and genuine Borel placement obligations, together
with the earlier marked-action data; none of these asserts root rigidity.

The carrier is Model m at q = 2^(2*m+1), with m > 0. No assertion about the
derived Tits group is made.
Source: Aschbacher–Smith, proof of 13.6.6, printed p.927; A.2.3–4.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- Conditional transport retaining the exact missing full-center calculation.
The specified Borel lies in the image of the genuine model Borel. -/
theorem reeF4_root_centralizers_of_center_eq (T : Subgroup G) {v : G}
    (K : Subgroup (Gv v)) (m : ℕ) (_hm : 0 < m)
    (hcenter : (center (ReeF4.Parabolics.unipotent m)).map
      (ReeF4.Parabolics.unipotent m).subtype = ReeF4.EvenInvolutionGeometry.longRootGroup m)
    (e : ReeF4.Model m ≃* NormalizerAction.componentImage K)
    (hU : (ReeF4.Parabolics.unipotent m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K))
    (hB : B ≤ (ReeF4.Parabolics.borel m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom))
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (XStar K)) =
      B ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
  let f := (NormalizerAction.componentImage K).subtype.comp e.toMonoidHom
  exact root_centralizers_of_model T K f (Subtype.val_injective.comp e.injective)
    (ReeF4.Parabolics.unipotent m) (ReeF4.Parabolics.borel m) hU B hB
    (ReeF4.NormalizedRootCentralizers.uniform_of_center_eq m hcenter) r hr hne

/-- Actual application of the model calculation to the marked source action.
Full-center identification and earlier Borel placement remain visible premises. -/
theorem exclude_reeF4_of_center_eq [Finite G] (s : Marking L V)
    (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    (m : ℕ) (hm : 0 < m)
    (hcenter : (center (ReeF4.Parabolics.unipotent m)).map
      (ReeF4.Parabolics.unipotent m).subtype = ReeF4.EvenInvolutionGeometry.longRootGroup m)
    (e : ReeF4.Model m ≃* NormalizerAction.componentImage K)
    (hU : (ReeF4.Parabolics.unipotent m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hDB : residualStar s K ≤ B)
    (hB : B ≤ (ReeF4.Parabolics.borel m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom)) : False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER B hDB
    (reeF4_root_centralizers_of_center_eq T K m hm hcenter e hU B hB)

/-- The literal source center `Z(Tᵥ* ∩ K*)` is the image of the concrete
long-root subgroup, through the given actual component isomorphism. -/
theorem reeF4_rootCenter_eq_longRootGroup (T : Subgroup G) {v : G}
    (K : Subgroup (Gv v)) (m : ℕ) (hm : 0 < m)
    (e : ReeF4.Model m ≃* NormalizerAction.componentImage K)
    (hU : (ReeF4.Parabolics.unipotent m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K) :
    rootCenter T K = (ReeF4.EvenInvolutionGeometry.longRootGroup m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) := by
  rw [rootCenter_eq_model_center T K
    ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom)
    (Subtype.val_injective.comp e.injective) (ReeF4.Parabolics.unipotent m) hU,
    ReeF4.EvenInvolutionGeometry.unipotent_center_eq_longRootGroup m hm]

/-- Uniform centralizers for every nonidentity element of the actual source
root center, with the model's full-center calculation discharged. -/
theorem reeF4_root_centralizers (T : Subgroup G) {v : G}
    (K : Subgroup (Gv v)) (m : ℕ) (hm : 0 < m)
    (e : ReeF4.Model m ≃* NormalizerAction.componentImage K)
    (hU : (ReeF4.Parabolics.unipotent m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K))
    (hB : B ≤ (ReeF4.Parabolics.borel m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom))
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (XStar K)) =
      B ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
  let f := (NormalizerAction.componentImage K).subtype.comp e.toMonoidHom
  exact root_centralizers_of_model T K f (Subtype.val_injective.comp e.injective)
    (ReeF4.Parabolics.unipotent m) (ReeF4.Parabolics.borel m) hU B hB
    (ReeF4.NormalizedRootCentralizers.uniform m hm) r hr hne

/-- The Ree branch of the marked-action contradiction on printed p.927.
Only the earlier model, Sylow, Borel placement and marked-action inputs remain;
the center identification and uniform Borel centralizers are proved. -/
theorem exclude_reeF4 [Finite G] (s : Marking L V)
    (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    (m : ℕ) (hm : 0 < m)
    (e : ReeF4.Model m ≃* NormalizerAction.componentImage K)
    (hU : (ReeF4.Parabolics.unipotent m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hDB : residualStar s K ≤ B)
    (hB : B ≤ (ReeF4.Parabolics.borel m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom)) : False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER B hDB
    (reeF4_root_centralizers T K m hm e hU B hB)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
