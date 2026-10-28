module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue.Fitting
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The seed supplement in the nilpotent SL₂(5) catalogue row

Every proper subgroup of SL₂(5) is solvable, by the actual A₅ central
quotient. A nontrivial perfect seed whose projection kernel is solvable
therefore projects onto SL₂(5). The original quotient map then gives the
Fitting-times-seed product, without any splitting premise.

The chosen-flag application and exclusion are in Catalogue.Nilpotent.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {A : Type*} [Group A] [Finite A]

private theorem sl2_five_proper_solvable (B : Subgroup SL(2,ZMod 5)) (hB : B ≠ ⊤) :
    Group.IsSolvable B := by
  let q := QuotientGroup.mk' (center SL(2,ZMod 5))
  have hproper : B.map q ≠ ⊤ := by
    intro he
    have hh := congrArg (comap q) he
    rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
    let : Group.IsPerfect SL(2,ZMod 5) := GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod 5) (by simp)
    exact hB (eq_top_of_sup_center_eq_top B hh)
  let e := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some
  let : Group.IsSolvable (B.map q) :=
    alternatingGroup.isSolvable_subgroup_of_equiv_five e _ hproper
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable ((B.map q).comap q) := isSolvable_comap_of_solvable_ker q _
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (le_comap_map q B)) (inclusion_injective _)

omit [Finite A] in
/-- A nontrivial perfect seed with solvable projection kernel fills SL₂(5).
This is the supplement argument for the nilpotent-extension row. -/
theorem sl2_five_surjective_of_perfect [Group.IsPerfect A] [Nontrivial A]
    {B : Type*} [Group B] [Finite B] (hm : Source.IsSL B 2 5)
    (f : A →* B) [Group.IsSolvable f.ker] : Function.Surjective f := by
  classical
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let a := (ZMod.ringEquivOfPrime F (by decide : Nat.Prime 5)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let e' := e.trans (Atlas.fieldEquivSL 2 a)
  let g := e'.toMonoidHom.comp f
  have hg : Function.Surjective g := by
    apply MonoidHom.range_eq_top.mp
    by_contra hne
    let : Group.IsSolvable g.range := sl2_five_proper_solvable g.range hne
    have hk : g.ker = f.ker := by
      ext x
      change e' (f x) = 1 ↔ f x = 1
      exact map_eq_one_iff e' e'.injective
    let : Group.IsSolvable g.ker := hk ▸ inferInstance
    let : Group.IsSolvable A :=
      Group.isSolvable_of_ker_le_range g.ker.subtype g.rangeRestrict (by
        intro x hx
        exact ⟨⟨x,congrArg Subtype.val (show g.rangeRestrict x = 1 from hx)⟩,rfl⟩)
    exact Group.IsPerfect.not_isSolvable A inferInstance
  intro b
  obtain ⟨x,hx⟩ := hg (e' b)
  exact ⟨x,e'.injective hx⟩

/-- In the nilpotent SL₂(5) row, a nontrivial perfect seed generates the
whole group together with the literal two-Fitting preimage. -/
theorem fitting_seed_split_of_sl2_five (C : Subgroup A)
    [Group.IsPerfect C] [Nontrivial C]
    (hm : Source.IsSL (A ⧸ twoFittingCore A) 2 5) :
    twoFittingCore A ⊔ C = ⊤ := by
  let q := QuotientGroup.mk' (twoFittingCore A)
  let f := q.comp C.subtype
  have hk : f.ker = (twoFittingCore A).subgroupOf C := by
    ext x
    exact QuotientGroup.eq_one_iff x.val
  let : Group.IsSolvable (twoFittingCore A) := twoFittingCore_solvable
  let : Group.IsSolvable f.ker := by
    rw [hk]
    exact Group.isSolvable_of_isSolvable_injective
      (f := C.subtype.subgroupComap (twoFittingCore A)) (by
        intro x y he
        exact Subtype.ext (Subtype.ext (congrArg (fun x : twoFittingCore A => (x : A)) he)))
  have hsur := sl2_five_surjective_of_perfect hm f
  have him : C.map q = ⊤ := by
    simpa only [f,MonoidHom.range_comp,range_subtype] using
      MonoidHom.range_eq_top.mpr hsur
  have hh := congrArg (comap q) him
  simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top,sup_comm] using hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
