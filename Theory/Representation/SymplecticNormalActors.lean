module
public import Theory.SpecificGroups.SymplecticFour.NormalSylowActors
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.SpecificGroups.SymplecticFour.ThompsonInner

/-!
# The natural action of a small normal symplectic actor

Transport the original ambient conjugation through the actual natural-module
coordinates. Natural normalizers preserve the Dynkin diagram, and the
intersection of the ambient Sylow with the normal component is a component
Sylow. The small-normal-actor bound then proves that every actor is inner.
The marked whole-constituent consumer uses this to obtain coefficient linearity.

Source: Aschbacher–Smith G.11.7, printed pp.367–368.
-/

public noncomputable section
namespace Representation.SymplecticNormalActors
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer SymplecticNaturalNormalizer
variable {D K : Type*} [Group D] [Finite D] [Field K] [Finite K] [CharP K 2]
  [Algebra (ZMod 2) K]

/-- The original small actor, normal in an actual ambient Sylow, acts inner
on its normal natural symplectic component. -/
theorem natural_normal_actor_inner
    (ρ : Representation (ZMod 2) D (Vector K)) (H A : Subgroup D) [H.Normal]
    [IsElementaryAbelian 2 A] (e : H ≃* Sp K)
    (hH : ∀ (h : H) w, ρ h w = symplecticNatural 2 (e h) w)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (S : Sylow 2 D) (hAS : A ≤ S) (hAn : (A.subgroupOf (S : Subgroup D)).Normal)
    (hcard : Nat.card A ≤ 2^(2*n)) :
    A.map (ThompsonInner.action H e) ≤ MulAut.innerSubgroup (Sp K) := by
  let f := ThompsonInner.action H e
  have hq : 2 < Nat.card K := by
    rw [hK]
    simpa using Nat.pow_lt_pow_right (by decide : 1<2) (show 1<n by omega)
  let j : D →* naturalNormalizer (F := K) := (linearAction ρ).codRestrict _
    (operator_mem_naturalNormalizer H hq e ρ hH)
  have hj (x : D) : conjugation hq (j x) = f x := by
    apply conjugation_eq_of_intertwines
    intro g w
    obtain ⟨h,rfl⟩ := e.surjective g
    have hfx : f x (e h) = e (MulAut.conjNormal x h) := by
      apply InvolutionNormalForms.inner_injective
      have he : MulAut.conj (f x (e h)) = f x * MulAut.conj (e h) * (f x)⁻¹ := by
        ext y
        simp
      rw [he, ← ThompsonInner.action_on_K H e h,
        ← ThompsonInner.action_on_K H e (MulAut.conjNormal x h)]
      change f x * f (h : D) * (f x)⁻¹ = f (x * (h : D) * x⁻¹)
      rw [map_mul, map_mul, map_inv]
    rw [hfx]
    change ρ x (symplecticNatural 2 (e h) w) =
      symplecticNatural 2 (e (MulAut.conjNormal x h)) (ρ x w)
    rw [←hH h,←hH (MulAut.conjNormal x h)]
    simp only [←Module.End.mul_apply,←map_mul]
    have he : x*(h:D) = (MulAut.conjNormal x h : D)*x := by
      change x*(h:D)=(x*(h:D)*x⁻¹)*x
      group
    rw [he]
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal H
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  apply NormalSylowActors.small_normal_elementary_inner hn hK P (A.map f)
  · have hP : (P : Subgroup (Sp K)).map (MulAut.conj : Sp K →* MulAut (Sp K)) ≤
        (S : Subgroup D).map f := by
      rintro _ ⟨b,⟨h,hh,rfl⟩,rfl⟩
      refine ⟨(h:D),?_,ThompsonInner.action_on_K H e h⟩
      have hx : h ∈ (S : Subgroup D).subgroupOf H := hR ▸ hh
      exact hx
    apply hP.trans
    rintro _ ⟨x,hx,rfl⟩
    exact le_normalizer_map f (mem_map_of_mem f
      ((normal_subgroupOf_iff_le_normalizer hAS).mp hAn hx))
  · exact (Nat.card_le_card_of_surjective (f.subgroupMap A) (f.subgroupMap_surjective A)).trans hcard
  · rintro _ ⟨x,hx,rfl⟩
    rw [←hj]
    exact conjugation_preservesDiagram hq (j x)
end Representation.SymplecticNormalActors
