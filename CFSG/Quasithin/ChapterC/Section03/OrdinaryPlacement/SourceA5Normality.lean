module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5SmallOrders
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5ReeLocal
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.TrialityLocal
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.OddCharacteristicExclusion
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.ExceptionalFiniteLocal
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.ExceptionalFiniteRank
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.JankoHallSimsLocal
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.BinaryUnitaryExclusion
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SourceInputs
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The complete ordinary-component branch of A₅ normality

The proved Theorem C catalogue is applied to the literal central quotient
of an ordinary component of H. The original C.3 placement and local rank
arguments, the rank-one exclusions, and the small elementary-layer action
argument discharge every catalogue row. Thus the original A₅-marked
C.2.8 component is normalized by M whenever H has an ordinary component.

No model, action-kernel or local-inspection premise remains. The constrained
C-component branch is retained separately in the C.4.8 assembly.

Source: Aschbacher–Smith C.3.1 and C.4.8, printed pp.149–154, specialized
to the original A₅ covering configuration of 4.2.12–13, pp.610–611.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- Any ordinary component of H closes the original A₅ normality branch. -/
theorem normalizes_a5_of_ordinary_component
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) :
    M ≤ normalizer (L : Set G) := by
  let := hK.2
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model (h.sqtk.subgroup K)
    theoremA_knownSimple theoremC_knownSimple
  cases hm with
  | alternating n hn e => exact h.normalizes_a5_of_ordinary_alternating a K hK hn e.some
  | odd hm => exact (h.no_ordinary_component_of_theoremC_odd_model K hK hm).elim
  | bender hm =>
    cases hm with
    | linear f hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact (h.no_ordinary_component_sl2_central_quotient K hK
        (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)).elim
    | unitary f hf hm => exact (h.no_ordinary_component_binary_unitary_three K hK hf hm).elim
    | suzuki m hm e => exact (h.no_ordinary_component_suzuki_central_quotient K hK hm e.some).elim
  | rank_two f hm =>
    cases hm with
    | linear hf hm => exact h.normalizes_a5_of_ordinary_isPSL3 a K hK hm
    | symplectic hf hm => exact h.normalizes_a5_of_ordinary_isPSp a K hK hm
    | g2 hf hm => exact h.normalizes_a5_of_ordinary_isG2At a K hK hf hm
    | triality hf hm => exact h.normalizes_a5_of_ordinary_isTrialityGroupAt a K hK hf hm
    | ree_f4 m hm hf e => exact (h.no_ordinary_a5_reeF4 a K hK hm e.some).elim
    | symplectic_derived hf e => exact h.normalizes_a5_of_ordinary_sp_derived_two a K hK e.some
    | g2_derived hf e => exact h.normalizes_a5_of_ordinary_g2_derived_two a K hK e.some
    | tits hf e => exact h.normalizes_a5_of_ordinary_tits a K hK e.some
  | linear_binary n hn hm => exact h.normalizes_a5_of_ordinary_linear_binary a K hK hn hm
  | sporadic hm =>
    rcases hm with ⟨n,hn,⟨e⟩⟩ | ⟨e⟩
    · cases n with
      | m11 => exact h.normalizes_a5_of_ordinary_small_sporadic a K hK _ (by simp) e
      | m12 => exact h.normalizes_a5_of_ordinary_small_sporadic a K hK _ (by simp) e
      | m22 => exact h.normalizes_a5_of_ordinary_small_sporadic a K hK _ (by simp) e
      | m23 => exact h.normalizes_a5_of_ordinary_small_sporadic a K hK _ (by simp) e
      | m24 => exact h.normalizes_a5_of_ordinary_small_sporadic a K hK _ (by simp) e
      | j4 => exact h.normalizes_a5_of_ordinary_small_sporadic a K hK _ (by simp) e
      | j3 => exact (hn rfl).elim
      | j2 => exact h.normalizes_a5_of_ordinary_j2 a K hK e
      | hs => exact h.normalizes_a5_of_ordinary_hs a K hK e
      | he => exact h.normalizes_a5_of_ordinary_held a K hK e
      | ru => exact h.normalizes_a5_of_ordinary_rudvalis a K hK e
    · exact (h.no_ordinary_component_janko_central_quotient K hK e.some).elim

/-- The literal conjugate span is the original component in the ordinary branch. -/
theorem span_eq_a5_of_ordinary_component
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) : conjugateSpanBy L M = L :=
  le_antisymm
    (conjugateSpanBy_le le_rfl (h.normalizes_a5_of_ordinary_component a K hK))
    (le_conjugateSpanBy L M)

end CFSG.Quasithin.ChapterC.HypothesisC28
