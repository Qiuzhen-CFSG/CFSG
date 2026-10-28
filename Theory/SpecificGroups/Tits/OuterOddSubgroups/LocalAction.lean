module

public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.Stabilizers
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Restriction of Tits automorphisms to the marked Sylow subgroup

The stabilizer below consists of all automorphisms preserving the actual
certified Sylow subgroup. Restriction is a homomorphism, and its kernel fixes
that Sylow subgroup pointwise. Both concrete parabolics are invariant under
this stabilizer, by their intrinsic centralizer and normalizer descriptions.

Sylow conjugacy shows that the stabilizer surjects onto the actual outer
automorphism quotient. Thus bounding the restriction image and kernel controls
all outer automorphisms, without assuming automorphism exhaustiveness for a
chosen extension of the group.

Source: the local route to the Tits case of the outer-group inspection in
Aschbacher–Smith, combined manuscript, printed p.510; compare GLS3, 2.5.15.
-/

@[expose] public section
namespace Tits.OuterOddSubgroups
open Subgroup

/-- All automorphisms preserving the certified Sylow two-subgroup. -/
def sylowStabilizer : Subgroup (MulAut Atlas1600Group) where
  carrier := {a | atlas1600SylowTwoSubgroup.map a.toMonoidHom = atlas1600SylowTwoSubgroup}
  one_mem' := Subgroup.map_id _
  mul_mem' {a b} ha hb := by
    change atlas1600SylowTwoSubgroup.map (a.toMonoidHom.comp b.toMonoidHom) = _
    rw [← Subgroup.map_map, hb, ha]
  inv_mem' {a} ha := by
    calc
      atlas1600SylowTwoSubgroup.map a⁻¹.toMonoidHom =
          (atlas1600SylowTwoSubgroup.map a.toMonoidHom).map a⁻¹.toMonoidHom := by rw [ha]
      _ = atlas1600SylowTwoSubgroup := by
        rw [Subgroup.map_map]
        rw [show a⁻¹.toMonoidHom.comp a.toMonoidHom = MonoidHom.id _ by
          ext x
          exact a.symm_apply_apply x, Subgroup.map_id]

/-- The actual restriction of a Sylow-preserving automorphism. -/
def sylowRestriction : sylowStabilizer →* MulAut atlas1600SylowTwoSubgroup where
  toFun a := (a.val.subgroupMap atlas1600SylowTwoSubgroup).trans
    (MulEquiv.subgroupCongr a.property)
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

@[simp] theorem sylowRestriction_apply (a : sylowStabilizer)
    (x : atlas1600SylowTwoSubgroup) :
    (sylowRestriction a x : Atlas1600Group) = a.val x := rfl

/-- The restriction kernel is precisely pointwise fixation of the Sylow subgroup. -/
theorem mem_sylowRestriction_ker_iff (a : sylowStabilizer) :
    a ∈ sylowRestriction.ker ↔
      ∀ x ∈ atlas1600SylowTwoSubgroup, a.val x = x := by
  constructor
  · intro ha x hx
    exact congrArg Subtype.val (DFunLike.congr_fun ha ⟨x, hx⟩)
  · intro ha
    apply MulEquiv.ext
    intro x
    exact Subtype.ext (ha x x.property)

/-- Sylow preservation forces preservation of the first full parabolic. -/
theorem preserves_first (a : sylowStabilizer) :
    ExceptionalParabolics.first.map a.val.toMonoidHom = ExceptionalParabolics.first :=
  RelativeParabolicNormalizers.first_stabilized a.val a.property

/-- Sylow preservation forces preservation of the second full parabolic. -/
theorem preserves_second (a : sylowStabilizer) :
    ExceptionalParabolics.second.map a.val.toMonoidHom = ExceptionalParabolics.second :=
  RelativeParabolicNormalizers.second_stabilized a.val a.property

/-- Restriction to the two intrinsic parabolics. -/
def parabolicRestriction : sylowStabilizer →*
    MulAut ExceptionalParabolics.first × MulAut ExceptionalParabolics.second where
  toFun a :=
    ((a.val.subgroupMap ExceptionalParabolics.first).trans
      (MulEquiv.subgroupCongr (preserves_first a)),
     (a.val.subgroupMap ExceptionalParabolics.second).trans
      (MulEquiv.subgroupCongr (preserves_second a)))
  map_one' := by apply Prod.ext <;> ext x <;> rfl
  map_mul' a b := by apply Prod.ext <;> ext x <;> rfl

/-- The two restrictions determine the automorphism, since the parabolics generate. -/
theorem parabolicRestriction_injective : Function.Injective parabolicRestriction := by
  intro a b hab
  let E := a.val.toMonoidHom.eqLocus b.val.toMonoidHom
  have hfirst : ExceptionalParabolics.first ≤ E := by
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun (congrArg Prod.fst hab) ⟨x, hx⟩)
  have hsecond : ExceptionalParabolics.second ≤ E := by
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun (congrArg Prod.snd hab) ⟨x, hx⟩)
  have ht : (⊤ : Subgroup Atlas1600Group) ≤ E := by
    rw [← ExceptionalParabolics.generate]
    exact sup_le hfirst hsecond
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  exact ht (mem_top x)

/-- The outer class of a Sylow-preserving automorphism. -/
def toOuter : sylowStabilizer →* MulAut.Outer Atlas1600Group :=
  (QuotientGroup.mk' (MulAut.innerSubgroup Atlas1600Group)).comp sylowStabilizer.subtype

/-- Every outer class has a representative preserving the marked Sylow subgroup. -/
theorem toOuter_surjective : Function.Surjective toOuter := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup Atlas1600Group) q
  let Q : Sylow 2 Atlas1600Group :=
    atlas1600SylowTwo.mapSurjective (f := a.toMonoidHom) a.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Atlas1600Group Q atlas1600SylowTwo
  have hmap : atlas1600SylowTwoSubgroup.map
      ((MulAut.conj g) * a).toMonoidHom = atlas1600SylowTwoSubgroup := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, atlas1600SylowTwo_coe] at hh
    change (Q : Subgroup Atlas1600Group).map (MulAut.conj g).toMonoidHom = _ at hh
    rw [show (Q : Subgroup Atlas1600Group) =
        atlas1600SylowTwoSubgroup.map a.toMonoidHom from
      by simpa only [atlas1600SylowTwo_coe] using
        (Sylow.coe_mapSurjective (f := a.toMonoidHom) a.surjective atlas1600SylowTwo),
      Subgroup.map_map] at hh
    exact hh
  refine ⟨⟨(MulAut.conj g) * a, hmap⟩, ?_⟩
  change QuotientGroup.mk' (MulAut.innerSubgroup Atlas1600Group) ((MulAut.conj g) * a) = _
  have hi : QuotientGroup.mk' (MulAut.innerSubgroup Atlas1600Group) (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (show MulAut.conj g ∈
      MulAut.innerSubgroup Atlas1600Group from ⟨g, rfl⟩)
  rw [map_mul, hi, one_mul]

end Tits.OuterOddSubgroups
end
