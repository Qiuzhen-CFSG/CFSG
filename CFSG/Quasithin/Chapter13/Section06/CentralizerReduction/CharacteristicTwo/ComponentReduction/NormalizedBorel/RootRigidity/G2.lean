module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ActionFacts
public import Theory.AtlasPort.LinearGroups.G2.NormalizedRootCentralizers

/-!
# G₂ root rigidity in the faithful component action

The actual model is identified with `K/Z(K)`, then embedded in
`X* = N(K)/C(K)` by the canonical component-image equivalence. The map's
value and action on each element of K are recorded explicitly, so the same
construction covers the exceptional central extensions of G₂(4).

The supplied normalized Sylow arrangement identifies the whole model U
with `Tᵥ* ∩ K*`. Its center is proved to be the image of `rootA`; the actual
Borel calculation gives equal centralizers for every nonidentity element
of this center. Applying it to a* contradicts the residual's nontrivial
action on z*, as required in the nonsymplectic branch on printed p.927.

The parent supplies the genuine central-quotient model equivalence,
normalized Sylow arrangement, Borel placement inside K*, and the earlier
marked action facts. There is no assumption of uniform root centralizers
or of centerlessness of the component.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927; the root formulas
use the licensed ATLAS model, as documented in the imported Theory module.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] {L V : Subgroup G}
variable {F : Type*} [Field F]

/-- The actual G₂ model embedded in the faithful component action through
K/Z(K). This also applies when K is an exceptional central cover of G₂(4). -/
noncomputable def g2ModelMap {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* Model F) : Model F →* XStar K :=
  (NormalizerAction.componentImage K).subtype.comp
    (e.symm.trans (NormalizerAction.componentCentralQuotientEquiv K)).toMonoidHom

theorem g2ModelMap_injective {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* Model F) : Function.Injective (g2ModelMap K e) :=
  Subtype.val_injective.comp
    (e.symm.trans (NormalizerAction.componentCentralQuotientEquiv K)).injective

/-- The map agrees with the literal normalizer/centralizer quotient on K. -/
theorem g2ModelMap_mk {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* Model F) (k : K) :
    g2ModelMap K e (e (QuotientGroup.mk' (center K) k)) =
      NormalizerAction.quotient K (inclusion K.le_normalizer k) := by
  change ((NormalizerAction.componentCentralQuotientEquiv K)
    (e.symm (e (QuotientGroup.mk' (center K) k))) : XStar K) = _
  rw [e.symm_apply_apply, NormalizerAction.componentCentralQuotientEquiv_mk]

/-- The induced action is conjugation on the genuine component, including
its center; no replacement of the cover by a centerless group is made. -/
theorem g2ModelMap_action_mk {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* Model F) (k : K) :
    NormalizerAction.action K (g2ModelMap K e (e (QuotientGroup.mk' (center K) k))) =
      MulAut.conj k := by
  rw [g2ModelMap_mk]
  ext y
  rfl

variable [CharP F 2]

/-- The full literal rootCenter is the image of the concrete highest root. -/
theorem g2_rootCenter_eq (T : Subgroup G) {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* Model F)
    (hU : (unipotent (K := F)).map (g2ModelMap K e) =
      NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K) :
    rootCenter T K = (highestRoot (F := F)).map (g2ModelMap K e) := by
  rw [rootCenter_eq_model_center T K (g2ModelMap K e) (g2ModelMap_injective K e)
    unipotent hU, unipotent_center]

/-- The G₂ Borel calculation in the actual quotient X* = N(K)/C(K).
The Sylow arrangement and Borel placement use the same central-quotient map. -/
theorem g2_root_centralizers (T : Subgroup G) {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* Model F)
    (hU : (unipotent (K := F)).map (g2ModelMap K e) =
      NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hB : B ≤ (borel (K := F)).map (g2ModelMap K e))
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (XStar K)) =
      B ⊓ centralizer (rootCenter T K : Set (XStar K)) :=
  root_centralizers_of_model T K (g2ModelMap K e) (g2ModelMap_injective K e)
    unipotent borel hU B hB Atlas.G2.NormalizedRootCentralizers.uniform r hr hne

/-- The source a*/z* action asymmetry excludes G₂, also for central covers
of G₂(4), once the earlier source supplies its normalized model arrangement.
No center identification or root-centralizer equality is assumed. -/
theorem exclude_g2 [Finite G] (s : Marking L V)
    (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    (e : K ⧸ center K ≃* Model F)
    (hU : (unipotent (K := F)).map (g2ModelMap K e) =
      NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hDB : residualStar s K ≤ B)
    (hB : B ≤ (borel (K := F)).map (g2ModelMap K e)) : False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER B hDB
    (g2_root_centralizers T K e hU B hB)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
