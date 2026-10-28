module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.Involution

/-!
# From recognized natural/dual coordinates to the cubic lifting argument

Conjugating the literal quotientAction by the recognized coordinates gives
an additive, hence binary-linear, automorphism. The two coordinate summands
are complementary, and the source swap exchanges them. This proves the
involution-coset transitivity used in 15.3.61(1).

The same swap forces an outer actor involution. The actual model centralizer
supplies a cubic subgroup; lifting through H/Z and H/O₂(H) then constructs
a conjugate of the chosen Sylow three-group centralized by t. Neither that
conjugate nor an actor-centralizer witness is an additional hypothesis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.58(3) and the proof of 15.3.61(1), printed pp.1148–1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
open HLocal

private noncomputable def coordinateAction (d : Recognition Z ZS) (t : centralizerH Z) :
    Coordinates ≃ₗ[ZMod 2] Coordinates :=
  let a : Coordinates ≃+ Coordinates := AddEquiv.toMultiplicative.symm
    (d.coordinates.symm.trans ((quotientAction Z ZS t).trans d.coordinates))
  a.toLinearEquiv (ZMod.map_smul a)

private lemma coordinateAction_apply (d : Recognition Z ZS) (t : centralizerH Z)
    (q : VectorQuotient Z ZS) :
    d.coordinates (quotientAction Z ZS t q) =
      Multiplicative.ofAdd (coordinateAction Z ZS d t (d.coordinates q).toAdd) := by
  change d.coordinates (quotientAction Z ZS t q) =
    d.coordinates (quotientAction Z ZS t (d.coordinates.symm (d.coordinates q)))
  rw [MulEquiv.symm_apply_apply]

private abbrev naturalSummand : Submodule (ZMod 2) Coordinates :=
  LinearMap.range (LinearMap.inl (ZMod 2) BinaryLinearThree.Vector
    (Module.Dual (ZMod 2) BinaryLinearThree.Vector))
private abbrev dualSummand : Submodule (ZMod 2) Coordinates :=
  LinearMap.range (LinearMap.inr (ZMod 2) BinaryLinearThree.Vector
    (Module.Dual (ZMod 2) BinaryLinearThree.Vector))

private lemma coordinateAction_swaps (d : Recognition Z ZS) (t : centralizerH Z)
    (hs : Swaps Z ZS d t) :
    (∀ w ∈ naturalSummand, coordinateAction Z ZS d t w ∈ dualSummand) ∧
      (∀ w ∈ dualSummand, coordinateAction Z ZS d t w ∈ naturalSummand) := by
  constructor
  · rintro w ⟨v, rfl⟩
    refine ⟨(coordinateAction Z ZS d t (v, 0)).2, ?_⟩
    exact Prod.ext (hs.1 v).symm rfl
  · rintro w ⟨f, rfl⟩
    refine ⟨(coordinateAction Z ZS d t (0, f)).1, ?_⟩
    exact Prod.ext rfl (hs.2 f).symm

/-- Derive the source coset calculation from the actual recognized action. -/
theorem recognized_quotient_coset_transitive (d : Recognition Z ZS)
    (t : centralizerH Z) (ht : (t : G) ^ 2 = 1) (hs : Swaps Z ZS d t)
    (x : closureU Z ZS) (hx : ((x : G) * (t : G)) ^ 2 ∈ Z) :
    ∃ u : closureU Z ZS,
      (u : G)⁻¹ * (t : G) * (u : G) * ((x : G) * (t : G))⁻¹ ∈ Z := by
  obtain ⟨hA, hB⟩ := coordinateAction_swaps Z ZS d t hs
  exact swapped_quotient_coset_transitive Z ZS t ht d.coordinates
    (coordinateAction Z ZS d t) (coordinateAction_apply Z ZS d t)
    naturalSummand dualSummand LinearMap.isCompl_range_inl_inr hA hB x hx

/-- The recognized swap constructs the centralized cubic conjugate. -/
theorem recognized_centralizes_conjugate [Finite G] (d : Recognition Z ZS)
    (t : centralizerH Z) (ht : (t : G) ^ 2 = 1) (hs : Swaps Z ZS d t)
    (PH : Sylow 3 (centralizerH Z)) :
    ∃ g : G, ((PH : Subgroup (centralizerH Z)).map (centralizerH Z).subtype).map
      (MulAut.conj g).toMonoidHom ≤ centralizer ({(t : G)} : Set G) := by
  obtain ⟨D, hD, hDC⟩ := source_actor_cubic Z ZS d t ht hs
  obtain ⟨hA, hB⟩ := coordinateAction_swaps Z ZS d t hs
  exact source_centralizes_conjugate Z ZS d.subgroup_le d.center_le d.center_card d.core_eq
    t ht d.coordinates (coordinateAction Z ZS d t) (coordinateAction_apply Z ZS d t)
    naturalSummand dualSummand LinearMap.isCompl_range_inl_inr hA hB D hD hDC PH
    (sylow_three_card Z ZS d PH)
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
