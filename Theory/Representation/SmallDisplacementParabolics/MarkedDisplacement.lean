module
public import Theory.Representation.SmallDisplacementParabolics.PairedCentralDisplacement
public import Theory.Representation.BinaryNaturalDual.InvolutionDisplacement
public import Theory.Representation.BinaryOffender.SylowCentral
public import Theory.Representation.BinaryPermutation.CentralTransvections

/-!
# Rank two from a marked Sylow-normal actor in the partner models

Extract a central involution from the nontrivial elementary actor inside
its full Sylow subgroup. A faithful S₈ action excludes a central
transvection. Natural-plus-dual involutions have even displacement or
exchange their summands; paired natural central involutions have equal
block ranks. Thus this same actor contains an element of displacement
two whenever all its elements have displacement at most two.

The group isomorphisms and coordinate maps in `ActionModel` are used
literally. This is a consequence of recognition, not a recognition theorem.
The source assembly owner qt-e-152-critical-pair must still construct the
model for the actual chief quotient before applying this result.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119
(refs/quasithin.pdf p.1136).
-/

public section
open Subgroup
namespace Representation.SmallDisplacementParabolics
open RankTwo.Imprimitive BinaryOffender
variable {D W : Type*} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- In each actual partner model, a Sylow-central involution moves at least a plane. -/
theorem ActionModel.central_involution_displacement_ge_two
    {ρ : Representation (ZMod 2) D W} (hm : ActionModel ρ) (hf : Function.Injective ρ)
    (S : Sylow 2 D) (a : D) (ha : a ∈ (S : Subgroup D))
    (ho : orderOf a = 2) (hc : ∀ s ∈ (S : Subgroup D), Commute a s) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) := by
  have hne : a ≠ 1 := by intro he; simp [he] at ho
  have ha2 : a ^ 2 = 1 := by rw [← ho]; exact pow_orderOf_eq_one a
  have hρ : ρ a ≠ 1 := fun he => hne (hf (he.trans (map_one ρ).symm))
  rcases hm with ⟨e,_⟩ | ⟨n,hn,d,e,⟨E⟩⟩ | ⟨e,E,hE⟩
  · have hz : a ∈ (center S).map (S : Subgroup D).subtype := by
      refine ⟨⟨a,ha⟩,?_,rfl⟩
      apply mem_center_iff.mpr
      intro s
      exact Subtype.ext (hc s s.property).eq.symm
    by_contra hh
    have hp : 0 < Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hρ (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
    exact BinaryPermutation.not_twoCentral_faithful_eight ρ hf e a hne ha2
      (by change Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) = 1; omega) S hz
  · have he (w : W) : d.representation (e a) (E.toLinearEquiv w) = E.toLinearEquiv (ρ a w) :=
      (LinearMap.congr_fun (E.isIntertwining' a) w).symm
    have hr := (displacementRangeEquiv E.toLinearEquiv (ρ a) (d.representation (e a)) he).finrank_eq
    rw [hr]
    apply d.involution_displacement_ge_two hn (e a)
    · simpa only [map_pow,map_one] using congrArg e ha2
    · intro hzero
      apply hρ
      apply LinearMap.ext
      intro w
      apply E.toLinearEquiv.injective
      rw [← he,hzero]
      rfl
  · let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have he (w : W) : pairedRepresentation (e a) (E w) = E (ρ a w) := by
      funext i
      exact (hE a w i).symm
    have hr := (displacementRangeEquiv E (ρ a) (pairedRepresentation (e a)) he).finrank_eq
    rw [hr]
    apply PairedNatural.sylow_central_involution_displacement_ge_two S' (e a)
    · simpa only [map_pow,map_one] using congrArg e ha2
    · exact fun hh => hne (e.injective (hh.trans e.map_one.symm))
    · intro b hb
      change b ∈ (S : Subgroup D).map e.toMonoidHom at hb
      obtain ⟨s,hs,rfl⟩ := hb
      exact (hc s hs).map e.toMonoidHom

/-- The given actor itself supplies rank two; no displacement witness is assumed. -/
theorem ActionModel.exists_rank_two_of_sylow_normal
    {ρ : Representation (ZMod 2) D W} (hm : ActionModel ρ) (hf : Function.Injective ρ)
    (A : Subgroup D) (S : Sylow 2 D) (hA : IsElementaryAbelian 2 A)
    (hne : A ≠ ⊥) (hAS : A ≤ S) (hn : (S : Subgroup D) ≤ normalizer (A : Set D))
    (hd : ∀ a ∈ A, Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2) :
    ∃ a : D, a ∈ A ∧ orderOf a = 2 ∧
      (∀ s ∈ (S : Subgroup D), Commute a s) ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) = 2 := by
  obtain ⟨a,ha,ho,hc⟩ := exists_sylow_central_involution_of_normal_elementary A S hA hne hAS hn
  exact ⟨a,ha,ho,hc,Nat.le_antisymm (hd a ha)
    (hm.central_involution_displacement_ge_two hf S a (hAS ha) ho hc)⟩

end Representation.SmallDisplacementParabolics
