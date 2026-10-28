module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCoreCover
public import Theory.Representation.PSL3Two.ParabolicFixedFree

/-!
# Natural coefficients on the full center of a nonabelian binary core

The distance-four cover has a naturally marked derived subgroup. The original
component two-core fixes that derived subgroup. Its image under the weak center
projection is injective, since the natural module has no fixed vectors, and is
therefore onto. Consequently every central core element is a derived element
times a component-central element. This proves centralization of the full
center while retaining its possible fixed kernel, and identifies the literal
natural coefficient quotient used by the source 15.3.31 argument.

Source: Aschbacher--Smith C.1.34(3) and 15.3.31, printed pp.136--137 and1132.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.FullCoreDoubleDualCover
variable {A : Type*} [Group A] (c : FullCoreDoubleDualCover A)

private def derivedConjugate (a : A) (x : _root_.commutator (blockU A)) :
    _root_.commutator (blockU A) :=
  ⟨blockConjugate A a x, by
    have h := mem_map_of_mem (MulAut.conjNormal a).toMonoidHom x.property
    have he : (_root_.commutator (blockU A)).map
        (MulAut.conjNormal a).toMonoidHom = _root_.commutator (blockU A) := by
      have hr : ((MulAut.conjNormal a : MulAut (blockU A)).toMonoidHom).range = ⊤ :=
        MonoidHom.range_eq_top.mpr (MulAut.conjNormal a).surjective
      rw [map_commutator_eq, hr, ← _root_.commutator_def]
    rw [he] at h
    exact h⟩

include c

/-- The original two-core fixes the entire derived core. -/
theorem core_centralizes_derived (r : A) (hr : r ∈ pCore 2 A)
    (x : _root_.commutator (blockU A)) : r * (x.val : A) * r⁻¹ = x.val := by
  have he := c.derivedAction r x (derivedConjugate r x) rfl
  have hr1 : QuotientGroup.mk' (pCore 2 A) r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  rw [hr1, map_one, map_one] at he
  have hx : derivedConjugate r x = x := c.derivedEquiv.injective
    (Multiplicative.toAdd.injective he)
  exact congrArg (fun z : _root_.commutator (blockU A) => (z.val : A)) hx

/-- In the full-cover output the derived core lies in the actual core center. -/
theorem derived_le_center : _root_.commutator (blockU A) ≤ center (blockU A) := by
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have h := c.core_centralizes_derived (y : A) (blockU_le_core y.property) ⟨x,hx⟩
  exact mul_inv_eq_iff_eq_mul.mp h

def derivedLayer : _root_.commutator (blockU A) →* c.layer where
  toFun x := ⟨x.val,c.center_le (mem_map_of_mem _ (c.derived_le_center x.property))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem derived_central_trivial (x : _root_.commutator (blockU A))
    (hx : (x.val : A) ∈ center A) : x = 1 := by
  have hv : (c.derivedEquiv x).toAdd = 0 := by
    apply BinaryLinearThree.ParabolicFixedFree.natural_fixed_eq_zero
    intro g _
    obtain ⟨q,rfl⟩ := c.marking.surjective g
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) q
    have hc : (x : blockU A) = blockConjugate A a (x : blockU A) := by
      apply Subtype.ext
      have he := mem_center_iff.mp hx a
      change (x.val : A) = a * (x.val : A) * a⁻¹
      rw [he,mul_inv_cancel_right]
    exact (c.derivedAction a x x hc).symm
  apply c.derivedEquiv.injective
  exact (Multiplicative.toAdd.injective hv).trans c.derivedEquiv.map_one.symm

/-- The weak natural center map is already bijective on the derived core. -/
theorem derived_projection_bijective :
    Function.Bijective (c.projection.comp c.derivedLayer) := by
  have hi : Function.Injective (c.projection.comp c.derivedLayer) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply _root_.eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    exact derived_central_trivial c x (c.kernel_central (c.derivedLayer x) hx)
  exact ⟨hi, (Finite.surjective_of_injective
    (hi.comp c.derivedEquiv.symm.injective)).of_comp⟩

/-- Every central core element differs from a derived element by a component-central element. -/
theorem center_decomposition (z : center (blockU A)) :
    ∃ x : _root_.commutator (blockU A), (z.val : A) * (x.val : A)⁻¹ ∈ center A := by
  let zL : c.layer := ⟨z.val,c.center_le (mem_map_of_mem _ z.property)⟩
  obtain ⟨x,hx⟩ := c.derived_projection_bijective.2 (c.projection zL)
  refine ⟨x,c.kernel_central (zL * (c.derivedLayer x)⁻¹) ?_⟩
  rw [map_mul,map_inv,show c.projection (c.derivedLayer x) = c.projection zL from hx,
    mul_inv_cancel]

/-- The original two-core centralizes the whole center, including its retained fixed kernel. -/
theorem core_centralizes_center (r : A) (hr : r ∈ pCore 2 A)
    (z : center (blockU A)) : r * (z.val : A) * r⁻¹ = z.val := by
  obtain ⟨x,hx⟩ := c.center_decomposition z
  have he := mem_center_iff.mp hx r
  have hd := c.core_centralizes_derived r hr x
  calc
    r * (z.val : A) * r⁻¹ = r * ((z.val : A) * (x.val : A)⁻¹ * (x.val : A)) * r⁻¹ := by
      rw [inv_mul_cancel_right]
    _ = ((z.val : A) * (x.val : A)⁻¹) * (r * (x.val : A) * r⁻¹) := by
      rw [←mul_assoc, he]
      group
    _ = (z.val : A) := by rw [hd,inv_mul_cancel_right]

/-- The literal coefficient map on the full center. -/
def centerProjection : center (blockU A) →* Multiplicative BinaryLinearThree.Vector :=
  c.projection.comp {
    toFun z := ⟨z.val,c.center_le (mem_map_of_mem _ z.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }

/-- The natural derived subgroup makes the full-center coefficient map onto. -/
theorem centerProjection_surjective : Function.Surjective c.centerProjection := by
  intro v
  obtain ⟨x,hx⟩ := c.derived_projection_bijective.2 v
  exact ⟨⟨x.val,c.derived_le_center x.property⟩,hx⟩

/-- The kernel is exactly the retained component-central part. -/
theorem centerProjection_eq_one_iff (z : center (blockU A)) :
    c.centerProjection z = 1 ↔ (z.val : A) ∈ center A := by
  constructor
  · exact c.kernel_central _
  · intro hz
    apply Multiplicative.toAdd.injective
    apply BinaryLinearThree.ParabolicFixedFree.natural_fixed_eq_zero
    intro g _
    obtain ⟨q,rfl⟩ := c.marking.surjective g
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) q
    let zL : c.layer := ⟨z.val,c.center_le (mem_map_of_mem _ z.property)⟩
    have he := c.action a zL
    have hz' : (⟨a * (zL : A) * a⁻¹,c.normal.conj_mem zL zL.property a⟩ : c.layer) = zL := by
      apply Subtype.ext
      change a * (z.val : A) * a⁻¹ = (z.val : A)
      rw [mem_center_iff.mp hz a,mul_inv_cancel_right]
    rw [hz'] at he
    exact he.symm

end CFSG.Quasithin.ChapterC.BinaryMS.FullCoreDoubleDualCover
