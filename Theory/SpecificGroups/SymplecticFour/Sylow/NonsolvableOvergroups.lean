module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry
public import Theory.SpecificGroups.SL2.SolvableSylowOvergroups

/-!
# Residuals of nonsolvable symplectic Sylow overgroups

A proper overgroup of a full Sylow two-subgroup lies in a point or plane
parabolic. Nonsolvability forces its intersection with the determinant-one
factor to map onto SL₂. The two-group kernel already lies in the Sylow,
so the entire factor lies in the original overgroup. Perfectness then
identifies its literal solvable residual under the same conjugacy.

Source: Aschbacher--Smith 15.1.20(3b), printed pp.1094--1097; the
rank-one Sylow-overgroup calculation is A.3.12, printed pp.47--48.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem contains_local_of_nonsolvable
    (W : Submodule F (Vector F)) (S : Sylow 2 (Sp F))
    (H : Subgroup (Sp F)) (hSH : (S : Subgroup (Sp F)) ≤ H)
    (hSL : (S : Subgroup (Sp F)) ≤ determinantKernel W)
    (hHP : H ≤ stabilizer W) (hns : ¬ Group.IsSolvable H)
    (f : determinantKernel W →* SL(2,F)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : determinantKernel W ≤ H := by
  let K := determinantKernel W
  let A := H.subgroupOf K
  let Q := S.subtype hSL
  have hQA : (Q : Subgroup K) ≤ A := fun _ hx => hSH hx
  have hA : ¬ Group.IsSolvable A := by
    intro hs
    let := hs
    let i : A →* H := {
      toFun x := ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    let c := (determinantCharacter W).comp (inclusion hHP)
    apply hns
    apply Group.isSolvable_of_ker_le_range i c
    intro x hx
    have hxK : (x : Sp F) ∈ K := ⟨⟨x,hHP x.property⟩,hx,rfl⟩
    exact ⟨⟨⟨x,hxK⟩,x.property⟩,rfl⟩
  have him : A.map f = ⊤ := by
    by_contra he
    let : Group.IsNilpotent f.ker := hk.isNilpotent
    let : Group.IsSolvable (A.map f) :=
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
        (Q.mapSurjective hf) (A.map f) (map_mono hQA) he
    let : Group.IsSolvable ((A.map f).comap f) := isSolvable_comap_of_solvable_ker f _
    exact hA (Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (le_comap_map f A)))
  have he : A = ⊤ := by
    have hh := congrArg (comap f) him
    rwa [comap_map_eq_self ((hk.le_sylow_of_normal Q).trans hQA),comap_top] at hh
  exact subgroupOf_eq_top.mp he

/-- Nonsolvability forces the complete determinant-one point factor. -/
theorem nonsolvable_point_overgroup_contains_local
    (S : Sylow 2 (Sp F)) (H : Subgroup (Sp F))
    (hSH : (S : Subgroup (Sp F)) ≤ H) (hHP : H ≤ pointParabolic)
    (hns : ¬ Group.IsSolvable H) : pointLocal ≤ H := by
  apply contains_local_of_nonsolvable (point F) S H hSH _ hHP hns
    pointQuotient pointQuotient_surjective (IsElementaryAbelian.isPGroup 2 pointRadical)
  intro x hx
  let y : stabilizer (point F) := ⟨x,hHP (hSH hx)⟩
  obtain ⟨k,hk⟩ := S.isPGroup'.exists_pow_pow_eq_one ⟨x,hx⟩
  have hy : y^(2^k)=1 := Subtype.ext (congrArg (fun a : S => (a : Sp F)) hk)
  have hc := congrArg (fun a : Fˣ => (a : F)) (congrArg (determinantCharacter (point F)) hy)
  refine ⟨y,?_,rfl⟩
  apply Units.ext
  exact (iterateFrobenius_inj F 2 k) (by simpa [iterateFrobenius_def, map_pow, map_one] using hc)

/-- Nonsolvability forces the complete determinant-one plane factor. -/
theorem nonsolvable_plane_overgroup_contains_local
    (S : Sylow 2 (Sp F)) (H : Subgroup (Sp F))
    (hSH : (S : Subgroup (Sp F)) ≤ H) (hHP : H ≤ planeParabolic)
    (hns : ¬ Group.IsSolvable H) : planeLocal ≤ H := by
  apply contains_local_of_nonsolvable (plane F) S H hSH _ hHP hns
    Plane.quotientMap Plane.quotientMap_surjective (IsElementaryAbelian.isPGroup 2 Plane.radical)
  intro x hx
  let y : stabilizer (plane F) := ⟨x,hHP (hSH hx)⟩
  obtain ⟨k,hk⟩ := S.isPGroup'.exists_pow_pow_eq_one ⟨x,hx⟩
  have hy : y^(2^k)=1 := Subtype.ext (congrArg (fun a : S => (a : Sp F)) hk)
  have hc := congrArg (fun a : Fˣ => (a : F)) (congrArg (determinantCharacter (plane F)) hy)
  refine ⟨y,?_,rfl⟩
  apply Units.ext
  exact (iterateFrobenius_inj F 2 k) (by simpa [iterateFrobenius_def, map_pow, map_one] using hc)

/-- The literal residual is point-local or plane-local under one conjugacy. -/
theorem nonsolvable_sylow_overgroup_residual {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (S : Sylow 2 (Sp F)) (H : Subgroup (Sp F))
    (hSH : (S : Subgroup (Sp F)) ≤ H) (hH : H ≠ ⊤)
    (hns : ¬ Group.IsSolvable H) :
    ∃ g : Sp F,
      (H.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∧
        ((solvableResidual H).map H.subtype).map (MulAut.conj g).toMonoidHom = pointLocal) ∨
      (H.map (MulAut.conj g).toMonoidHom ≤ planeParabolic ∧
        ((solvableResidual H).map H.subtype).map (MulAut.conj g).toMonoidHom = planeLocal) := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  obtain ⟨g,hg⟩ := ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover
    hlarge S H hSH hH
  let a := MulAut.conj g
  let D := H.map a.toMonoidHom
  let Q := S.mapSurjective (f := a.toMonoidHom) a.surjective
  have hQD : (Q : Subgroup (Sp F)) ≤ D := map_mono hSH
  have hD : ¬ Group.IsSolvable D := by
    intro hs
    let := hs
    exact hns (Group.isSolvable_of_isSolvable_injective
      (f := (H.equivMapOfInjective a.toMonoidHom a.injective).toMonoidHom)
      (H.equivMapOfInjective a.toMonoidHom a.injective).injective)
  have he : ((solvableResidual H).map H.subtype).map a.toMonoidHom =
      (solvableResidual D).map D.subtype := by
    let t : H ≃* D := H.equivMapOfInjective a.toMonoidHom a.injective
    rw [map_map]
    have heq : a.toMonoidHom.comp H.subtype = D.subtype.comp t.toMonoidHom := rfl
    rw [heq,←map_map,map_solvableResidual_eq _ t.surjective]
  refine ⟨g,?_⟩
  rw [he]
  rcases hg with hp | hp
  · left
    let := pointLocal_perfect hF hn
    exact ⟨hp,le_antisymm ((map_solvableResidual_mono hp).trans_eq
      (pointParabolic_solvableResidual_eq hF hn))
      (le_map_solvableResidual_of_isPerfect _ D
        (nonsolvable_point_overgroup_contains_local Q D hQD hp hD))⟩
  · right
    let := planeLocal_perfect hF hn
    exact ⟨hp,le_antisymm ((map_solvableResidual_mono hp).trans_eq
      (planeParabolic_solvableResidual_eq hF hn))
      (le_map_solvableResidual_of_isPerfect _ D
        (nonsolvable_plane_overgroup_contains_local Q D hQD hp hD))⟩
end Theory.SpecificGroups.SymplecticFour
