module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TripleCover
public import Theory.Representation.Mathieu.M22James.Ambient
public import Theory.Representation.Mathieu.M22James.Uniqueness
public import Theory.Mathieu.M22.TripleCover.Recognition

/-!
# Rank exclusion for an identified twelve-dimensional triple-cover action

James's uniqueness theorem supplies an actual intertwining equivalence on
the normal quasisimple component. Its matrix normalizer then transports
every ambient element, including the outer involution, to the genuine
`3.M₂₂.2` action. The concrete involution calculation therefore applies to
the original representation, without an additional representation-matching
premise. The final intrinsic variant also recognizes the component from
quasisimplicity, its center of order three and its actual Mathieu quotient.

The elementary abelian subgroup is used only for its exponent-two property;
no condition on its intersection with the component, its rank, or its
normalizer is needed for this exclusion.

Source: Aschbacher--Smith, A.3.5, G.7.3(2)(iii) and its proof, G.11.2(13),
and the proof of 6.2.19, printed pp.43, 348, 364, 691. The component is
irreducible as in G.7.3 and G.11.6; its identification is with the genuine
perfect cover, whose center has order three.
-/

@[expose] public section

open Sporadic.Mathieu
open M22TripleCover.Ambient
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

namespace Representation.RankTwo.TripleCover

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Identify the component action by James's theorem, retaining its actual
group isomorphism and the full intertwining linear equivalence. -/
theorem component_equiv (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) (e : L ≃* M22TripleCover)
    [Representation.IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 12) :
    Nonempty (Representation.Equiv (ρ.comp L.subtype)
      (M22TripleCover.representationOfEquiv e)) := by
  let τ : Representation (ZMod 2) M22TripleCover V :=
    (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : τ.IsIrreducible :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr inferInstance
  obtain ⟨E⟩ := M22TripleCover.Uniqueness.equiv_of_finrank_twelve τ
    (hf.comp (Subtype.val_injective.comp e.symm.injective)) hd
  refine ⟨Representation.Equiv.mk E.toLinearEquiv ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  change E (ρ (g : G) v) = M22TripleCover.binaryRepresentation (e g) (E v)
  have h := LinearMap.congr_fun (E.isIntertwining' (e g)) v
  change E (ρ ((e.symm (e g) : L) : G) v) = M22TripleCover.binaryRepresentation (e g) (E v) at h
  simpa only [e.symm_apply_apply] using h

/-- The component coordinates extend to every ambient actor through the
proved full matrix normalizer, so the outer action is also identified. -/
theorem no_rank_two_of_component_equiv
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (e : L ≃* M22TripleCover)
    (E : Representation.Equiv (ρ.comp L.subtype) (M22TripleCover.representationOfEquiv e))
    (g : G) (hg : g ^ 2 = 1) :
    Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  let j := markedTripleAmbientHom ρ L e E
  have he : Module.finrank (ZMod 2) (movedSpace ρ g) =
      Module.finrank (ZMod 2) (movedSpace binaryAction (j g)) :=
    finrank_movedSpace_transport ρ (binaryAction.comp j) (MulEquiv.refl G)
      E.toLinearEquiv (markedTripleAmbientHom_intertwining ρ L e E) g
  rw [he]
  apply concrete_no_rank_two
  rw [← map_pow, hg, map_one]

/-- The no-rank-two assertion in 6.2.19 for alternative G.11.2(13).
The group classification supplies `e`; module uniqueness and the outer
action comparison are discharged here. -/
theorem case_thirteen_no_rank_two (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [L.Normal] (e : L ≃* M22TripleCover)
    [Representation.IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 12)
    (X : Subgroup G) [IsElementaryAbelian 2 X] (g : G) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  obtain ⟨E⟩ := component_equiv ρ L e hf hd
  exact no_rank_two_of_component_equiv ρ L e E g
    (elemPow_eq_one_of_isElementaryAbelian g hg)

/-- The intrinsic hat convention suffices: recognize the genuine cover,
identify its twelve-dimensional action, and include every outer actor.
All inputs are source hypotheses; no concrete-model witness is assumed. -/
theorem case_thirteen_no_rank_two_of_central_quotient
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    [Finite L] [Theory.GroupTheory.IsQuasisimple L]
    (hcenter : Nat.card (Subgroup.center L) = 3)
    (hquotient : Nonempty ((L ⧸ Subgroup.center L) ≃* M22))
    [Representation.IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 12)
    (X : Subgroup G) [IsElementaryAbelian 2 X] (g : G) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  obtain ⟨e⟩ := M22TripleCover.nonempty_mulEquiv hcenter hquotient
  exact case_thirteen_no_rank_two ρ L e hf hd X g hg

end Representation.RankTwo.TripleCover
