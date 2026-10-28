module
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Theory.SpecificGroups.BinaryLinear.Perfect
/-!
# Self-dual binary actions have proper full-linear image

In dimension at least three, elementary transvections force every bilinear
form preserved by the full linear group to vanish. A self-dual representation
therefore cannot have full linear image. The same holds when self-duality is
known only on a normal subgroup with an abelian supplement: perfectness of
binary GL makes that normal subgroup's image full as well.

This supplies the full-linear exclusion in Aschbacher--Smith G.10.16(4)
and G.11.6(6), printed pp.363--365, on the actual constituent action.
-/

public section
open Subgroup Module Representation
open scoped IsMulCommutative
namespace Representation

/-- A self-dual binary action in dimension at least three is not all of GL. -/
theorem binary_not_surjective_of_selfDual {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hd : 3 ≤ finrank (ZMod 2) V) (e : ρ.Equiv ρ.dual)
    (hs : Function.Surjective ρ.asGroupHom) : False := by
  let b := Module.finBasis (ZMod 2) V
  let B : LinearMap.BilinForm (ZMod 2) V := e.toLinearEquiv.toLinearMap
  have hpres (g : G) (u w : V) : B (ρ g u) (ρ g w) = B u w := by
    have hh := LinearMap.congr_fun (e.isIntertwining' g) u
    have hh' := LinearMap.congr_fun hh (ρ g w)
    change B (ρ g u) (ρ g w) = B u (ρ g⁻¹ (ρ g w)) at hh'
    simpa only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply] using hh'
  have hzero (i j : Fin (finrank (ZMod 2) V)) : B (b i) (b j) = 0 := by
    obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    let t := BinaryLinear.transvection (b i) (b.coord k) (by simp [hki])
    obtain ⟨g,hg⟩ := hs ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm t)
    have hact (w : V) : ρ g w = t w := by
      exact congrArg (fun a : LinearMap.GeneralLinearGroup (ZMod 2) V => a.val w) hg
    have hh := hpres g (b k) (b j)
    simp only [hact] at hh
    change B (b k + b.coord k (b k) • b i) (b j + b.coord k (b j) • b i) = _ at hh
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hkj,one_smul,zero_smul,add_zero,
      map_add,LinearMap.add_apply] at hh
    exact add_left_cancel (hh.trans (add_zero (B (b k) (b j))).symm)
  have hB : B = 0 := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    exact hzero i j
  have he0 : e (b ⟨0,by omega⟩) = e 0 := by
    change B (b ⟨0,by omega⟩) = B 0
    rw [hB]
    rfl
  exact b.ne_zero ⟨0,by omega⟩ (e.injective he0)

/-- Self-duality on a normal factor with abelian supplement also excludes GL. -/
theorem binary_not_surjective_of_selfDual_normal_restriction {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (H X : Subgroup G) [H.Normal] [IsMulCommutative X]
    (hgen : H ⊔ X = ⊤) (hd : 3 ≤ finrank (ZMod 2) V)
    (e : Representation.Equiv (ρ.comp H.subtype) (Representation.dual (ρ.comp H.subtype)))
    (hs : Function.Surjective ρ.asGroupHom) : False := by
  let b := Module.finBasis (ZMod 2) V
  let E := (LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin (finrank (ZMod 2) V) → ZMod 2))
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup (finrank (ZMod 2) V)) :=
    BinaryLinear.linearGroup_isPerfect _ hd
  let : Group.IsPerfect (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  let N := H.map ρ.asGroupHom
  let Y := X.map ρ.asGroupHom
  let : N.Normal := Subgroup.Normal.map inferInstance ρ.asGroupHom hs
  have hNY : N ⊔ Y = ⊤ := by
    rw [← Subgroup.map_sup,hgen,← MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr hs]
  have hN : N = ⊤ := by
    have hh := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hNY inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hh
    exact top_unique hh
  apply binary_not_surjective_of_selfDual (ρ.comp H.subtype) hd e
  intro a
  obtain ⟨g,hg,he⟩ := hN.ge (mem_top a)
  exact ⟨⟨g,hg⟩,he⟩

end Representation
