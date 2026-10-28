module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinaryRee
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinaryLayer

/-!
# Remaining ordinary covering models for a centerless seed

The genuine Theorem C catalogue supplies actual central-quotient
isomorphisms. The ordinary placement, rank bounds and elementary-layer
arguments exclude every row except J₄ and Held. These two rows remain
explicit mathematical obligations.

OrdinarySource retains the original ambient and module data and applies
this dispatcher to the literal covering and Hall-kernel counterexamples.
Source: Aschbacher--Smith C.3.1 and C.4.8, pp.149--154, used in
4.2.12 and 4.4.6, pp.610,620.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

@[expose] def SimpleOrdinaryRemainder (Q : Type*) [Group Q] : Prop :=
  Nonempty (Q ≃* Janko4.Model) ∨ Nonempty (Q ≃* Held.He)

theorem nonnormal_simple_ordinary_models
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (hn : ¬ M ≤ normalizer (L : Set G))
    (K : Subgroup H) (hK : IsComponent H K) : SimpleOrdinaryRemainder (K ⧸ center K) := by
  let := hK.2
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model (h.sqtk.subgroup K)
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple
  cases hm with
  | alternating n hsmall e =>
    exact (hn (h.normalizes_of_simple_ordinary_alternating hz K hK (by omega) e.some)).elim
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
    | linear hf hm => exact (hn (h.normalizes_of_simple_ordinary_linear_three hz K hK hf hm)).elim
    | symplectic hf hm => exact (hn (h.normalizes_of_simple_ordinary_symplectic hz K hK hm)).elim
    | g2 hf hm => exact (hn (h.normalizes_of_simple_ordinary_g2 hz K hK hf hm)).elim
    | triality hf hm => exact (hn (h.normalizes_of_simple_ordinary_triality hz K hK hf hm)).elim
    | ree_f4 m hm hf e => exact (hn (h.normalizes_of_simple_ordinary_ree hz K hK hm e.some)).elim
    | symplectic_derived hf e =>
      exact (hn (h.normalizes_of_simple_ordinary_alternating hz K hK (by decide : 6 ≤ 9)
        (e.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix))).elim
    | g2_derived hf e => exact (hn (h.normalizes_of_simple_ordinary_g2_derived_two hz K hK e.some)).elim
    | tits hf e => exact (hn (h.normalizes_of_simple_ordinary_tits hz K hK e.some)).elim
  | linear_binary n hsmall hm =>
    exact (hn (h.normalizes_of_simple_ordinary_binary_linear hz K hK hsmall hm)).elim
  | sporadic hm =>
    rcases hm with ⟨n,hnot,⟨e⟩⟩ | ⟨e⟩
    · cases n with
      | m11 => exact (hn (h.normalizes_of_simple_ordinary_mathieu hz K hK _ (by simp) e)).elim
      | m12 => exact (hn (h.normalizes_of_simple_ordinary_mathieu hz K hK _ (by simp) e)).elim
      | m22 => exact (hn (h.normalizes_of_simple_ordinary_mathieu hz K hK _ (by simp) e)).elim
      | m23 => exact (hn (h.normalizes_of_simple_ordinary_mathieu hz K hK _ (by simp) e)).elim
      | m24 => exact (hn (h.normalizes_of_simple_ordinary_mathieu hz K hK _ (by simp) e)).elim
      | j4 => exact Or.inl ⟨e⟩
      | j3 => exact (hnot rfl).elim
      | j2 => exact (hn (h.normalizes_of_simple_ordinary_j2 hz K hK e)).elim
      | hs => exact (hn (h.normalizes_of_simple_ordinary_hs hz K hK e)).elim
      | he => exact Or.inr ⟨e⟩
      | ru => exact (hn (h.normalizes_of_simple_ordinary_rudvalis hz K hK e)).elim
    · exact (h.no_ordinary_component_janko_central_quotient K hK e.some).elim
end CFSG.Quasithin.ChapterC.HypothesisC28
