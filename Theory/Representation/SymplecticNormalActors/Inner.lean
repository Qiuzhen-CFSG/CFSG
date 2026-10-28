module
public import Theory.Representation.SymplecticNormalActors
public import Theory.ElementaryAbelian.Injective

/-!
# Normal elementary actors on a natural symplectic component

The centralizer of an outer diagram-preserving involution has two-rank at
most 3(n/2)+1, hence at most 2n. An elementary actor containing it is therefore
small enough for the Sylow-orbit obstruction. Thus every normal elementary
actor is inner, without a separate order hypothesis. Faithfulness and the
odd scalar kernel place the actor in the actual normal component.

The original larger-actor consumer is ComponentCatalogueLargeActorDegreesSymplectic.
Source: Aschbacher–Smith G.11.7, printed pp.367–368; field-involution
centralizers as in 16.1.7–8, pp.1172–1173 of refs/quasithin.pdf.
-/
public noncomputable section
open scoped IsMulCommutative
namespace Representation.SymplecticNormalActors
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer SymplecticNaturalNormalizer
variable {D K : Type*} [Group D] [Finite D] [Field K] [Finite K] [CharP K 2]
  [Algebra (ZMod 2) K]

omit [Algebra (ZMod 2) K] in
private theorem normal_elementary_inner {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (P : Sylow 2 (Sp K)) (E : Subgroup (MulAut (Sp K))) [IsElementaryAbelian 2 E]
    (hPE : (P : Subgroup (Sp K)).map (MulAut.conj : Sp K →* MulAut (Sp K)) ≤
      normalizer (E : Set (MulAut (Sp K))))
    (hdiagram : ∀ a ∈ E, PreservesDiagram a) :
    E ≤ MulAut.innerSubgroup (Sp K) := by
  by_contra hnot
  obtain ⟨a,ha,hi⟩ := SetLike.not_le_iff_exists.mp hnot
  have ha1 : a ≠ 1 := fun h => hi (h ▸ (MulAut.innerSubgroup (Sp K)).one_mem)
  have hao : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  obtain ⟨_,hr⟩ :=
    AutomorphismCentralizers.preserving_outer_centralizer_rank_le_of_descent hK hn
      (fun he g hg => InvolutionNormalForms.half_frobenius_cocycle_coboundary
        hK (by omega) he g hg) a hao (hdiagram a ha) hi
  have hEC : E ≤ centralizer ({a} : Set (MulAut (Sp K))) := by
    intro b hb
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨b,hb⟩ : E) ⟨a,ha⟩)
  have he : primeRank 2 E ≤ 2*n :=
    (primeRank_mono 2 hEC).trans (hr.trans (by omega))
  have hc : Nat.card E ≤ 2^(2*n) := by
    let : IsElementaryAbelian 2 (⊤ : Subgroup E) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype Subtype.val_injective
    have hh := (primeRank_le_iff_elementary_card_le E).mp he ⊤ inferInstance
    simpa only [Subgroup.card_top] using hh
  exact hnot (NormalSylowActors.small_normal_elementary_inner hn hK P E hPE hc hdiagram)

/-- A normal elementary actor in an actual ambient Sylow lies in its
faithful normal nonbinary natural symplectic component. -/
theorem natural_normal_actor_le
    (ρ : Representation (ZMod 2) D (Vector K)) (hf : Function.Injective ρ)
    (H A : Subgroup D) [H.Normal] [IsElementaryAbelian 2 A] (e : H ≃* Sp K)
    (hH : ∀ (h : H) w, ρ h w = symplecticNatural 2 (e h) w)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (S : Sylow 2 D) (hAS : A ≤ S) (hAn : (A.subgroupOf (S : Subgroup D)).Normal) :
    A ≤ H := by
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
  have hi : A.map f ≤ MulAut.innerSubgroup (Sp K) := by
    apply normal_elementary_inner hn hK P (A.map f)
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
    · rintro _ ⟨x,hx,rfl⟩
      rw [←hj]
      exact conjugation_preservesDiagram hq (j x)
  intro a ha
  have hin : (j a).val ∈ naturalDerivedImage := by
    by_contra hout
    apply conjugation_not_inner hq (j a) (by
      rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian a ha,map_one]) hout
    rw [hj]
    exact hi (mem_map_of_mem f ha)
  obtain ⟨b,hb⟩ := hin
  have he : ρ a = ρ (e.symm b.val : H) := by
    apply LinearMap.ext
    intro w
    rw [hH,e.apply_symm_apply]
    exact (congrArg (fun z : Vector K ≃ₗ[ZMod 2] Vector K => z w) hb).symm
  exact (hf he).symm ▸ (e.symm b.val).property
end Representation.SymplecticNormalActors
