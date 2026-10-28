module

public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
/-!
# Moving residuals and quasisimple action images

A normal subgroup that does not contain an ambient C-component residual is
solvable: its intersection with that residual is proper and subnormal, and
the remaining quotient is solvable. A supplement to a normal subgroup
fixing a seed consequently has a C-component residual that still moves it.

A radical supplement surjects onto every quasisimple homomorphic image,
since the radical image is central and a perfect group has no proper
central supplement. These are the two algebraic steps in the seed-action
route to Aschbacher–Smith 13.6.16(2), printed p.930, using A.3.3, pp.42–43.
The Chapter13 SeedMovement consumer supplies the literal action quotient
and the Thompson normalizer; no classification premise is used here.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Proper normal intersections with a C-component residual are solvable. -/
theorem isSolvable_of_normal_not_containing_ccomponent_residual (C : Subgroup G) [C.Normal]
    (hR : (solvableResidual G).IsCComponent)
    (hne : ¬ solvableResidual G ≤ C) : Group.IsSolvable C := by
  let R := solvableResidual G
  let D := C.subgroupOf R
  let : Group.IsSolvable D := hR.isSolvable_of_subnormal_lt_top
    (inferInstance : D.Normal).isSubnormal (fun ht => hne (subgroupOf_eq_top.mp ht))
  let f := (QuotientGroup.mk' R).comp C.subtype
  let j : f.ker →* D :=
    { toFun := fun x => ⟨⟨(x.val : G), (QuotientGroup.eq_one_iff _).mp x.property⟩,
        x.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : D => ((x : R) : G)) he))
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

/-- A supplement to a normal subgroup fixing the seed has a moving C-component residual. -/
theorem moving_residual_of_centralizing_normal_supplement (C N : Subgroup G) [C.Normal] (z : G)
    (hR : (solvableResidual G).IsCComponent)
    (hm : ¬ solvableResidual G ≤ centralizer ({z} : Set G))
    (hC : C ≤ centralizer ({z} : Set G)) (hg : C ⊔ N = ⊤) :
    (solvableResidual N).IsCComponent ∧
      ¬ (solvableResidual N).map N.subtype ≤ centralizer ({z} : Set G) := by
  let : Group.IsSolvable C := isSolvable_of_normal_not_containing_ccomponent_residual C hR (fun he => hm (he.trans hC))
  exact ⟨residual_isCComponent_of_solvable_supplement C N hg hR,
    fun h => hm ((solvableResidual_le_sup_residual_of_sup_eq_top C N hg).trans (sup_le hC h))⟩

open Theory.GroupTheory
variable {D : Type*} [Group D] [Finite D]
/-- Every radical supplement covers a quasisimple homomorphic image. -/
theorem map_radical_supplement_eq_top_of_quasisimple (f : G →* D) (hf : Function.Surjective f)
    [IsQuasisimple D] (B : Subgroup G)
    (hgen : solvableRadical G ⊔ B = ⊤) : B.map f = ⊤ := by
  have hc : (solvableRadical G).map f ≤ center D :=
    (map_solvableRadical_le_of_surjective f hf).trans IsQuasisimple.solvableRadical_le_center
  have hg : (solvableRadical G).map f ⊔ B.map f = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective f hf]
  have hn : (⊤ : Subgroup D) ≤ normalizer (B.map f : Set D) := by
    rw [← hg]
    exact sup_le (hc.trans (center_le_normalizer _)) (B.map f).le_normalizer
  let : (B.map f).Normal := normalizer_eq_top_iff.mp (top_unique hn)
  have hbc : B.map f ⊔ center D = ⊤ := by
    apply top_unique
    rw [← hg]
    exact sup_le (hc.trans le_sup_right) le_sup_left
  apply top_unique
  simpa using Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    hbc (inferInstance : IsMulCommutative (center D))
end Subgroup

end
