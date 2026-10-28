module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryIdentification
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldAffineModel
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldCentralizerConsequences

/-!
# Original escaping-point local source conclusions

The original escaping point centralizer constructs its literal ordinary
component and identifies its whole central quotient as PSL3(4). Thus the
core recovery, normalizer equality, ambient centralizers and fully marked
affine model now follow from the original source hypotheses alone.
The affine actor retains the even/full alternatives.

Source: Aschbacher--Smith12.7.5--7, printed pp.840--841.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem escaping_configuration
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    IsComponent H (B.subgroupOf H) ∧ centerIn B = tripleSixPoint D a t ∧
      Nonempty ((B ⧸ center B) ≃* Matrix.PSL3Four.PSL) := by
  obtain ⟨hB,hcenter,hV,hn,he⟩ :=
    original_tripleSix_point_identification_at h structural D a t ht heven hout
  let := hn
  obtain ⟨e⟩ := he
  exact ⟨hB,hcenter,⟨(QuotientGroup.quotientMulEquivOfEq hV.symm).trans e⟩⟩

/-- The full original cores, module centralizer and maximal normalizer
are determined by the original escaping point. -/
theorem original_tripleSix_escaping_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    K.pCoreIn 2 = U ∧ (K ⊔ (T : Subgroup G)).pCoreIn 2 = U ∧
      (normalizer (K : Set G)).pCoreIn 2 = U ∧
      normalizer (U : Set G) = normalizer (K : Set G) ∧
      centralizer (U : Set G) = U ∧
      normalizer (K : Set G) = K ⊔ (T : Subgroup G) := by
  obtain ⟨hB,hcenter,⟨e⟩⟩ := escaping_configuration h structural D a t ht heven hout
  have hc := original_tripleSix_held_core_recovery h structural D a t ht heven hB hcenter e
  exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2,
    original_tripleSix_held_normalizer_eq_join h structural D a t ht heven hB hcenter e⟩

/-- All four original ambient centralizers follow without a supplied component or quotient model. -/
theorem original_tripleSix_escaping_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    centralizer (K : Set G) = ⊥ ∧
      centralizer (Lt : Set G) = tripleSixPoint D a t ∧
      H ⊓ centralizer (B : Set G) = tripleSixPoint D a t ∧
      (T : Subgroup G) ⊓ centralizer (K : Set G) = ⊥ := by
  obtain ⟨hB,hcenter,⟨e⟩⟩ := escaping_configuration h structural D a t ht heven hout
  exact original_tripleSix_held_centralizer_consequences h structural D a t ht heven hB hcenter e

/-- The entire original normalizer has marked affine coordinates, preserving the original module, component action and actual scalar complement. -/
theorem original_tripleSix_escaping_affine_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let M := normalizer (K : Set G)
    ∃ R : Subgroup HexAutomorphisms, (R = hexSign.ker ∨ R = ⊤) ∧
      ∃ Y : Subgroup M, Nat.card Y = 3 ∧
        Y.map M.subtype ≤ tripleSixScalarResidual K ∧
        ∃ E : M ≃* Multiplicative hexacode ⋊[hexAffineAction.comp R.subtype] R,
          (∀ u : U, E (inclusion (D.le_component.trans K.le_normalizer) u) =
            SemidirectProduct.inl (tripleSixPointCoordinates D a u)) ∧
          (∀ k : K, ((E (inclusion K.le_normalizer k)).right : HexAutomorphisms) =
            (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
          (normalizer (Y : Set M)).map E.toMonoidHom =
            (SemidirectProduct.inr : R →*
              Multiplicative hexacode ⋊[hexAffineAction.comp R.subtype] R).range := by
  obtain ⟨hB,hcenter,⟨e⟩⟩ := escaping_configuration h structural D a t ht heven hout
  exact original_tripleSix_held_affine_model h structural D a t ht heven hB hcenter e

end CFSG.Quasithin.Chapter12.Section07
