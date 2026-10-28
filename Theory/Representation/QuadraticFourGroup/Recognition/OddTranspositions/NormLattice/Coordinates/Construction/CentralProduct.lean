module

public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Central quotient coordinates for commuting embedded groups

Multiplication from the external direct product is surjective. Injectivity on
each factor shows that an element of the product maps into the center exactly
when every coordinate is central. The coordinate quotient map therefore descends
and has precisely the intrinsic center as kernel. The resulting isomorphism
records the image of every embedded factor, including nonsplit central products.

This is the central-product calculation used in GLS2, Chapter B, Lemma 3.27.
-/

@[expose] public section

open Subgroup
namespace Subgroup

/-- Coordinates on the central quotient of a product of commuting embedded groups. -/
theorem centralProduct_quotient_coordinates
    {I S E : Type*} [Fintype I] [DecidableEq I] [Group S] [Group E]
    (f : I → S →* E) (hi : ∀ i, Function.Injective (f i))
    (hc : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y))
    (hg : (⨆ i, (f i).range) = ⊤) :
    ∃ e : (E ⧸ center E) ≃* (I → S ⧸ center S),
      ∀ (i : I) (x : S),
        e (QuotientGroup.mk' (center E) (f i x)) =
          Pi.mulSingle i (QuotientGroup.mk' (center S) x) := by
  classical
  let p : (I → S) →* E := MonoidHom.noncommPiCoprod f hc
  have hp : Function.Surjective p := MonoidHom.range_eq_top.mp
    ((MonoidHom.noncommPiCoprod_range f).trans hg)
  have hpi (i : I) (x : S) : p (Pi.mulSingle i x) = f i x :=
    MonoidHom.noncommPiCoprod_mulSingle f i x
  have hcenter (x : I → S) : p x ∈ center E ↔ ∀ i, x i ∈ center S := by
    constructor
    · intro hx i
      apply mem_center_iff.mpr
      intro y
      have he : x * Pi.mulSingle i y * x⁻¹ = Pi.mulSingle i (x i * y * (x i)⁻¹) := by
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [Pi.mulSingle_eq_of_ne hji]
      have he' : f i (x i * y * (x i)⁻¹) = f i y := by
        rw [← hpi, ← he, map_mul, map_mul, map_inv, hpi]
        rw [← mem_center_iff.mp hx (f i y)]
        simp [mul_assoc]
      exact (mul_inv_eq_iff_eq_mul.mp (hi i he')).symm
    · intro hx
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z,rfl⟩ := hp y
      rw [← map_mul, ← map_mul]
      congr 1
      funext i
      exact mem_center_iff.mp (hx i) (z i)
  let q : (I → S) →* (I → S ⧸ center S) :=
    MonoidHom.piMap (fun _ => QuotientGroup.mk' (center S))
  have hq : Function.Surjective q := by
    intro y
    choose x hx using fun i => QuotientGroup.mk'_surjective (center S) (y i)
    exact ⟨x, funext hx⟩
  have hq1 (x : I → S) : q x = 1 ↔ ∀ i, x i ∈ center S := by
    simp only [q, MonoidHom.piMap_apply, funext_iff, Pi.one_apply]
    exact forall_congr' fun i => QuotientGroup.eq_one_iff (x i)
  have hk : p.ker ≤ q.ker := by
    intro x hx
    exact (hq1 x).mpr ((hcenter x).mp (by rw [MonoidHom.mem_ker.mp hx]; exact one_mem _))
  let F : E →* (I → S ⧸ center S) := p.liftOfSurjective hp ⟨q,hk⟩
  have hF (x : I → S) : F (p x) = q x :=
    p.liftOfRightInverse_comp_apply _ _ ⟨q,hk⟩ x
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨x,rfl⟩ := hq y
    exact ⟨p x,hF x⟩
  have hFk : F.ker = center E := by
    ext y
    obtain ⟨x,rfl⟩ := hp y
    change F (p x) = 1 ↔ p x ∈ center E
    rw [hF, hq1, hcenter]
  let e : (E ⧸ center E) ≃* (I → S ⧸ center S) :=
    (QuotientGroup.quotientMulEquivOfEq hFk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective F hFs)
  have he (x : E) : e (QuotientGroup.mk' (center E) x) = F x := rfl
  refine ⟨e, fun i x => ?_⟩
  rw [he, ← hpi, hF]
  funext j
  by_cases hji : j = i
  · subst j; simp [q]
  · simp [q, Pi.mulSingle_eq_of_ne hji]
end Subgroup

end
