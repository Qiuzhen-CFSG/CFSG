module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ActionFacts
public import Theory.SpecificGroups.Triality.NormalizedRootCentralizers
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Triality root rigidity in the literal component action

The full center of the genuine positive unipotent group is the descended
highest long root over the base field. The Borel acts on that root by a
base-field scalar, so fixing any nonidentity element fixes the whole center.
Transport through the actual model equivalence identifies that center with
`rootCenter` in X* = N(K)/C(K). Applying the calculation to a* and z* excludes
the marked residual action configuration.

The parent supplies the model equivalence, normalized Sylow placement, Borel
placement and earlier marked action facts. No center identification or uniform
centralizer conclusion remains among those inputs. The calculation holds for
every positive binary exponent, in particular the source range n > 1.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 (`refs/quasithin.pdf`).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open Triality.Standard Triality.Standard.Parabolics
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- The actual triality model supplies uniform centralizers in the specified
Borel image, with the source center defined by the literal Sylow intersection. -/
theorem triality_root_centralizers (T : Subgroup G) {v : G} (K : Subgroup (Gv v))
    (n : ℕ) (hn : 0 < n)
    (e : BinaryCarrier n hn ≃* NormalizerAction.componentImage K)
    (hU : (unipotent (Triality.Standard.binaryParameters n hn)).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K))
    (hB : B ≤ (borel (Triality.Standard.binaryParameters n hn)).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom))
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (XStar K)) =
      B ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
  let f := (NormalizerAction.componentImage K).subtype.comp e.toMonoidHom
  exact root_centralizers_of_model T K f (Subtype.val_injective.comp e.injective)
    (unipotent (Triality.Standard.binaryParameters n hn)) (borel (Triality.Standard.binaryParameters n hn))
    hU B hB (Triality.Standard.NormalizedRootCentralizers.uniform _ rfl) r hr hne

/-- Application to the source a*/z* action asymmetry. All model center and
centralizer premises are discharged by the genuine triality calculation. -/
theorem exclude_triality [Finite G] (s : Marking L V)
    (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    (n : ℕ) (hn : 0 < n)
    (e : BinaryCarrier n hn ≃* NormalizerAction.componentImage K)
    (hU : (unipotent (Triality.Standard.binaryParameters n hn)).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hDB : residualStar s K ≤ B)
    (hB : B ≤ (borel (Triality.Standard.binaryParameters n hn)).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom)) : False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER B hDB
    (triality_root_centralizers T K n hn e hU B hB)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
