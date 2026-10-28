module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesPaired
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeLinearThree
public import CFSG.Quasithin.ChapterG.Section11.WholeRankOne
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentEvenExclusions
public import Theory.Representation.JankoTwo.NormalSylowBound

/-!
# Whole-component exclusions for the original larger actor

The original invariant alternating form makes the literal component
restriction self-dual. The original G.9 degree window then excludes binary
SL₃ central covers, M₂₃, M₂₄ and binary PSL₅. The already constructed
low-rank witness excludes the Bender families above degree four. For
Hall–Janko, relative normality of the original actor in its point Sylow bounds
its rank by three, contradicting the actual minimum binary degree twelve.

Every exclusion retains the actual whole-component G.9 input and requires
orbit equality before treating that component as normal and irreducible.
The resulting degree and component reductions attach these exclusions to
the original remaining action. Recognition of the other whole-component
rows and ambient exclusion of the marked S₈ action remain open. In degree
six the full dotted G₂(2) equivalence is preserved.

Source: Aschbacher–Smith G.9.3, G.11.7 and 14.3.13–14, printed
pp.353–356,366–367,993–994. No small-actor dimension identity is used.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterG.Section11
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s


/-- The original symplectic form gives self-duality on every actual subgroup. -/
theorem whole_restriction_selfDual (L : Subgroup F.TerminalHdot) :
    Nonempty (Representation.Equiv (F.terminalRepresentation.comp L.subtype)
      (Representation.dual (F.terminalRepresentation.comp L.subtype))) := by
  refine ⟨Representation.Equiv.mk (B.toDual s.hypothesis.nondegenerate) ?_⟩
  intro a
  ext u w
  change B (F.terminalRepresentation a u) w =
    B u (F.terminalRepresentation (a⁻¹ : L) w)
  have he := s.hypothesis.preserves a u (F.terminalRepresentation (a⁻¹ : L) w)
  simpa only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv,
    mul_inv_cancel, map_one, Module.End.one_apply] using he

omit s [IsElementaryAbelian 2 (rankTwoSeed T M)] in
/-- The exact whole-orbit input becomes a single-component G.9 input only
when the original orbit is equal to that component. -/
private theorem single_component_hypothesis {L : Subgroup F.TerminalHdot}
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (hHL : componentOrbit L ⊤ = L) :
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) L L
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
  rwa [hHL] at h9

/-- No whole binary SL₃ central cover fits the original G.9 degree window. -/
theorem not_whole_linear_three_cover {L : Subgroup F.TerminalHdot}
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (π : SL(3,k) →* L) (hπ : Function.Surjective π)
    (hz : π.ker ≤ center SL(3,k))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card k = 2^n) : False :=
  MarkedLinearThree.not_single_component_linear_three
    (single_component_hypothesis h9 hHL) (s.whole_restriction_selfDual L)
    π hπ hz n hn hcard

/-- Both actual projective and special binary linear-three carriers are excluded. -/
theorem not_whole_linear_three {L : Subgroup F.TerminalHdot}
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (hHL : componentOrbit L ⊤ = L) {n : ℕ} (hn : 0 < n)
    (model : ClassicalGroup.IsPSL L 3 (2^n) ∨ Chapter1.Section02.LocalModels.IsSL L 3 (2^n)) : False := by
  rcases model with model | model
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact s.not_whole_linear_three_cover h9 hHL
      (e.symm.toMonoidHom.comp (Matrix.PSL3.projection k))
      (e.symm.surjective.comp (Matrix.PSL3.projection_surjective k))
      (by rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective,Matrix.PSL3.projection_ker]) n hn hcard
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact s.not_whole_linear_three_cover h9 hHL e.symm.toMonoidHom e.symm.surjective
      (by rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le) n hn hcard

/-- The genuine low-rank witness and whole G.9 input exclude all Bender rows
above degree four, without the small-actor dimension identity. -/
theorem not_whole_bender {L : Subgroup F.TerminalHdot}
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (hHL : componentOrbit L ⊤ = L)
    (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat))
    (model : ClassificationModels.IsBenderModel L) : False :=
  ChapterG.Section11.WholeRankOne.not_bender_model s.hypothesis
    (single_component_hypothesis h9 hHL) s.low_rank_witness hd model

/-- Normality in the original point Sylow bounds the Hall–Janko actor by
rank three; the original G.9 bound then contradicts its minimum degree twelve. -/
theorem not_whole_janko_two {L : Subgroup F.TerminalHdot}
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (hHL : componentOrbit L ⊤ = L)
    (e : L ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  have h := single_component_hypothesis h9 hHL
  let := h.normal_H
  let := h.irreducible
  obtain ⟨S,_,hXS,hXn⟩ := s.normal_sylow
  have hcard := Representation.JankoTwo.normal_elementary_actor_card_le_eight
    F.terminalRepresentation h.faithful L e S (F.terminalDot (F.X g)) hXS hXn
  rw [h.card_actor] at hcard
  have hr : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤ 3 :=
    (pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp hcard
  let σ := (F.terminalRepresentation.comp L.subtype).comp e.symm.toMonoidHom
  have hσi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  have hσf : Function.Injective σ := h.faithful.comp
    (L.subtype_injective.comp e.symm.injective)
  have hd := h.degree_le
  have hdeg := Representation.JankoTwo.SmallBinaryDegrees.finrank_twelve_of_lt_twentyEight
    σ hσf hσi (by omega)
  omega

/-- Parity and the literal self-duality exclude M₂₃, M₂₄ and binary PSL₅. -/
theorem not_whole_even_models {L : Subgroup F.TerminalHdot}
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (hHL : componentOrbit L ⊤ = L)
    (model : Nonempty (L ≃* Sporadic.Mathieu.M23) ∨ Nonempty (L ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (L ≃* PSL(5,ZMod 2))) : False :=
  (single_component_hypothesis h9 hHL).not_even_models s.even_degree
    (s.whole_restriction_selfDual L) model


/-- Actual carrier models excluded from a single whole component. Each row
contains a literal group isomorphism, rather than an unattached family name. -/
@[expose] def ExcludedWholeComponentModel (D : Type*) [Group D] : Prop :=
  ClassificationModels.IsBenderModel D ∨
    (∃ n : ℕ, 0 < n ∧ (ClassicalGroup.IsPSL D 3 (2^n) ∨
      Chapter1.Section02.LocalModels.IsSL D 3 (2^n))) ∨
    Nonempty (D ≃* Sporadic.LeechRelated.J2.Carrier) ∨
    Nonempty (D ≃* Sporadic.Mathieu.M23) ∨ Nonempty (D ≃* Sporadic.Mathieu.M24) ∨
    Nonempty (D ≃* PSL(5,ZMod 2))

/-- Apply the whole-action obstructions to the original component, with its
original orbit and G.9 input. Orbit equality is retained as a genuine premise. -/
theorem not_whole_component_models {L : Subgroup F.TerminalHdot}
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (hHL : componentOrbit L ⊤ = L)
    (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat)) :
    ¬ ExcludedWholeComponentModel L := by
  rintro (hb | ⟨n,hn,hm⟩ | ⟨e⟩ | heven)
  · exact s.not_whole_bender h9 hHL hd hb
  · exact s.not_whole_linear_three h9 hHL hn hm
  · exact s.not_whole_janko_two h9 hHL e.some
  · exact s.not_whole_even_models h9 hHL heven

/-- The original degree alternatives, with the proved whole-component model
exclusions attached to the literal remaining G.9 action. The exceptional
marked S₈ action and all other whole-component rows remain explicit. -/
theorem degree_cases_or_full_four_or_restricted_whole :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
          ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
          (componentOrbit L ⊤ = L → ¬ ExcludedWholeComponentModel L)) := by
  rcases s.degree_cases_or_full_four_or_whole with hd | hf | ⟨hd,L,hL,hm,ho,h9⟩
  · exact Or.inl hd
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr ⟨hd,L,hL,hm,ho,h9,
      fun hHL => s.not_whole_component_models h9 hHL hd⟩)

/-- The actual component consumer with the restricted whole-component
remainder. The degree-six alternative still identifies the full dotted G₂(2). -/
theorem component_or_full_four_or_restricted_whole
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    ((∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
      (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
        Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
        F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
          pCore 2 (K.subgroupOf F.H))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
          ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
          (componentOrbit L ⊤ = L → ¬ ExcludedWholeComponentModel L)) := by
  rcases s.degree_cases_or_full_four_or_restricted_whole with hd | hr
  · exact Or.inl (source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis hd hfour hsix)
  · exact Or.inr hr

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
