module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.LocalSubgroups
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max4Image
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Core order and actual conjugation actions in Rudvalis max4

The completed marked-eight action identifies the intrinsic two-core with its
relative centralizer and gives order 2048. We construct conjugation on its
literal center and central quotient, retaining the quotient projections.
If the derived group is central, the quotient action factors through max4/P.
The equality of the center with the marked eight-group remains a separate
concrete calculation; under that equality the central quotient has order 256.

Source: Aschbacher--Smith I.2.2(7), printed pp.412--413, and GLS3 Table 5.3r,
printed pp.291--292. No special-group or Steinberg identification is assumed
in the unconditional core-order and action constructions.
-/

open Subgroup
open Rudvalis Rudvalis.SylowOvergroups Rudvalis.CoreQuotients
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover

namespace Rudvalis.CoveringIncidence

public noncomputable def intrinsicCoreEquiv : pCore 2 max4 ≃* max4Core :=
  (pCore 2 max4).equivMapOfInjective max4.subtype max4.subtype_injective

public theorem max4Core_card : Nat.card max4Core = 2048 := by
  rw [← Nat.card_congr intrinsicCoreEquiv.toEquiv]
  rw [← max4LinearAction_ker_eq_pCore]
  exact max4_kernel_card max4LinearAction max4LinearAction_surjective

public theorem max4Core_isPGroup : IsPGroup 2 max4Core :=
  pCore_isPGroup.map max4.subtype

public theorem max4Core_eq_centralizer :
    max4Core = max4 ⊓ centralizer (elementary 2 : Set Model) := by
  rw [max4Core, ← max4_centralizer_eq_pCore, subgroupOf_map_subtype, inf_comm]

public theorem marked_eight_le_core_center : elementary 2 ≤ max4CoreCenter :=
  marked_eight_le_core_center_of_full_image max4EightAction_surjective

public theorem max4_le_normalizer_core : max4 ≤ normalizer (max4Core : Set Model) := by
  have h := (pCore 2 max4).le_normalizer_map max4.subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, max4Core] using h

public def max4CoreAction : max4 →* MulAut max4Core :=
  max4Core.normalizerMonoidHom.comp (inclusion max4_le_normalizer_core)

@[simp] public theorem max4CoreAction_apply (g : max4) (x : max4Core) :
    (max4CoreAction g x : Model) = (g : Model) * (x : Model) * (g : Model)⁻¹ := by rfl

public def max4CenterAction : max4 →* MulAut (center max4Core) :=
  (MulAut.characteristic (center max4Core)).comp max4CoreAction

@[simp] public theorem max4CenterAction_apply (g : max4) (x : center max4Core) :
    ((max4CenterAction g x : max4Core) : Model) =
      (g : Model) * (x : Model) * (g : Model)⁻¹ := by rfl

public abbrev Max4CentralQuotient := max4Core ⧸ center max4Core

public def max4CentralQuotientAction : max4 →* MulAut Max4CentralQuotient :=
  (quotientAut (center max4Core)).comp max4CoreAction

@[simp] public theorem max4CentralQuotientAction_mk (g : max4) (x : max4Core) :
    max4CentralQuotientAction g (QuotientGroup.mk' (center max4Core) x) =
      QuotientGroup.mk' (center max4Core) (max4CoreAction g x) :=
  quotientAut_apply_mk _ _ _

public noncomputable def centerEquivMarked (hcenter : max4CoreCenter = elementary 2) :
    center max4Core ≃* elementary 2 :=
  ((center max4Core).equivMapOfInjective max4Core.subtype max4Core.subtype_injective).trans
    (MulEquiv.subgroupCongr hcenter)

@[simp] public theorem centerEquivMarked_apply (hcenter : max4CoreCenter = elementary 2)
    (x : center max4Core) :
    (centerEquivMarked hcenter x : Model) = ((x : max4Core) : Model) := by rfl

public theorem centerEquivMarked_action (hcenter : max4CoreCenter = elementary 2)
    (g : max4) (x : center max4Core) :
    centerEquivMarked hcenter (max4CenterAction g x) =
      max4EightAction g (centerEquivMarked hcenter x) := by
  apply Subtype.ext
  rfl

public theorem max4CentralQuotient_card_of_center_eq (hcenter : max4CoreCenter = elementary 2) :
    Nat.card Max4CentralQuotient = 256 := by
  have hc : Nat.card (center max4Core) = 8 :=
    (Nat.card_congr (centerEquivMarked hcenter).toEquiv).trans
      RankOneEightCharacteristic.elementary_two_card
  have h := (center max4Core).card_mul_index
  rw [hc, max4Core_card] at h
  change 8 * Nat.card Max4CentralQuotient = 2048 at h
  omega

public theorem core_le_centralQuotientAction_ker
    (hcomm : _root_.commutator max4Core ≤ center max4Core) :
    pCore 2 max4 ≤ max4CentralQuotientAction.ker := by
  intro g hg
  apply MulEquiv.ext
  intro z
  induction z using Quotient.inductionOn with
  | h x =>
    let p : max4Core := ⟨g, mem_map_of_mem max4.subtype hg⟩
    have he : max4CoreAction g x = p * x * p⁻¹ := by apply Subtype.ext; rfl
    change max4CentralQuotientAction g (QuotientGroup.mk' (center max4Core) x) =
      QuotientGroup.mk' (center max4Core) x
    rw [max4CentralQuotientAction_mk, he]
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hcomm (commutator_mem_commutator (mem_top p) (mem_top x))

public def max4FactorAction (hcomm : _root_.commutator max4Core ≤ center max4Core) :
    (max4 ⧸ pCore 2 max4) →* MulAut Max4CentralQuotient :=
  QuotientGroup.lift (pCore 2 max4) max4CentralQuotientAction
    (core_le_centralQuotientAction_ker hcomm)

@[simp] public theorem max4FactorAction_mk
    (hcomm : _root_.commutator max4Core ≤ center max4Core) (g : max4) :
    max4FactorAction hcomm (QuotientGroup.mk' (pCore 2 max4) g) =
      max4CentralQuotientAction g := by rfl

end Rudvalis.CoveringIncidence
