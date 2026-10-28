module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5Linear
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5RankTwo
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5Normality
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.Symplectic

/-!
# The actual ordinary catalogue with a central source point

Apply the proved Theorem C to the original ordinary component. C.2.8's
rank-one and odd-characteristic exclusions, its actual A₅ seed, and the
concrete central-cover restrictions remove those rows. The result records
the precise remaining quotient models; it does not assert the still needed
natural-module inspection of their local subgroups.

Source: Aschbacher--Smith 12.7.5 and C.3.1, printed pp.840 and 149--151.
-/

@[expose] public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement

/-- Remaining actual models after the central-point and A₅ source filters. -/
def NormalNaturalA5Remainder (Q : Type*) [Group Q] : Prop :=
  ClassicalGroup.IsPSL Q 3 4 ∨
  ClassificationModels.IsG2At Q 4 ∨
  (∃ n : ℕ, n ≤ 8 ∧ Nonempty (Q ≃* alternatingGroup (Fin n))) ∨
  ClassicalGroup.IsPSL Q 4 2 ∨
  (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧ Nonempty (Q ≃* name.Carrier))

end CFSG.Quasithin.ChapterC.OrdinaryPlacement

namespace CFSG.Quasithin.ChapterC.HypothesisC28
open ChapterA.Section02 ClassificationModels OrdinaryPlacement
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

private theorem no_g2_derived_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  apply h.no_ordinary_a5_of_fifteen_free_two_normalizers a K hK e
  intro P _ _ hd
  have hh := hd.trans
    (normalizer (P : Set (commutator (Atlas.G2.Model (ZMod 2))))).card_subgroup_dvd_card
  rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
  norm_num at hh

omit [Finite G] in
private theorem no_linear_five_two
    (_h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) (hz : center K ≠ ⊥)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 5 2) : False := by
  let := hK.2
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let hk : (universalProjection (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker ≃*
      (PUnit : Type) := ChapterI.LieMultipliers.Symplectic.psl5TwoUniversalKernelEquivPUnit F hF
  have hc : Nat.card (universalProjection
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker = 1 := by
    rw [Nat.card_congr hk.toEquiv]
    simp
  exact hz (center_eq_bot_of_centralQuotientEquiv (Subgroup.card_eq_one.mp hc) e)

/-- The genuine source hypotheses produce this narrowed model list.
The central-point premise is supplied by the literal ordinary closure. -/
theorem ordinary_normal_natural_a5_models
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) (hz : center K ≠ ⊥) :
    NormalNaturalA5Remainder (K ⧸ center K) := by
  let := hK.2
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model (h.sqtk.subgroup K)
    theoremA_knownSimple theoremC_knownSimple
  cases hm with
  | alternating n hn e => exact Or.inr (Or.inr (Or.inl ⟨n,hn,e⟩))
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
    | linear hf hm => exact Or.inl (h.ordinary_a5_isPSL3_four a K hK hz hm).2
    | symplectic hf hm => exact (hz (h.ordinary_psp4_center_eq_bot K hK hf hm)).elim
    | g2 hf hm =>
      have hf2 := (h.ordinary_g2_nontrivial_center K hK hz hf hm).1
      exact Or.inr (Or.inl (by simpa only [hf2, show (2 : ℕ) ^ 2 = 4 from rfl] using hm))
    | triality hf hm => exact (hz (h.ordinary_triality_center_eq_bot K hK hf hm)).elim
    | ree_f4 m hm hf e => exact (h.no_ordinary_a5_reeF4 a K hK hm e.some).elim
    | symplectic_derived hf e =>
      exact Or.inr (Or.inr (Or.inl ⟨6,by decide,
        ⟨e.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩⟩))
    | g2_derived hf e => exact (h.no_g2_derived_two a K hK e.some).elim
    | tits hf e => exact (h.no_ordinary_a5_tits a K hK e.some).elim
  | linear_binary n hn hm =>
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl hm)))
    · exact (h.no_linear_five_two K hK hz hm).elim
  | sporadic hm =>
    rcases hm with ⟨n,hn,e⟩ | ⟨e⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n,hn,e⟩)))
    · exact (h.no_ordinary_component_janko_central_quotient K hK e.some).elim

end CFSG.Quasithin.ChapterC.HypothesisC28
