module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.ResidualFixer

/-!
# Central displacement in the double cover of PSL₃(4)

The preimage of the projective graph-field fixed subgroup maps onto that
subgroup. For a compatible automorphism a of a perfect central cover,
x ↦ a(x)x⁻¹ is a homomorphism from this preimage to the covering center.
Its kernel is exactly the actual fixed subgroup. When the full kernel is
the center of order two, the displacement descends through the projective
map, and the relative quotient by the center is the projective fixed group.

These constructions retain the covering map and the actual lifted action.
Nontriviality of the displacement is a separate covering calculation; it
is not asserted by the constructions or by the two-element image criterion.
The character kills the displayed E₉ by coprime orders.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(3) and the nontrivial-cover case of 16.4.9(2), pp.409–410, 1191.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover
noncomputable section
open ExtendedCentralizer.ProjectiveFixer
variable {H : Type*} [Group H]
variable (c : PerfectCentralCovering.Cover H PSL)
/-- Preimage of the concrete projective graph-field fixed subgroup. -/
def fixedPreimage : Subgroup H := graphField.fixedSubgroup.comap c.toMonoidHom

variable (a : MulAut H)
variable (ha : ∀ x, c.toMonoidHom (a x) = graphField (c.toMonoidHom x))

include ha in
theorem displacement_mem_center (x : fixedPreimage c) :
    a x * (x : H)⁻¹ ∈ center H := by
  apply c.ker_le_center
  change c.toMonoidHom (a x * (x : H)⁻¹) = 1
  rw [map_mul, map_inv, ha, (MulAut.mem_fixedSubgroup _ _).mp x.property, mul_inv_cancel]

/-- The central displacement of a lift of a projective fixed element. -/
def displacement : fixedPreimage c →* center H where
  toFun x := ⟨a x * (x : H)⁻¹, displacement_mem_center c a ha x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    change a ((x : H) * y) * ((x : H) * y)⁻¹ =
      (a x * (x : H)⁻¹) * (a y * (y : H)⁻¹)
    have hc := mem_center_iff.mp (displacement_mem_center c a ha y) (x : H)⁻¹
    rw [map_mul, _root_.mul_inv_rev]
    calc
      a x * a y * ((y : H)⁻¹ * (x : H)⁻¹) =
          a x * ((a y * (y : H)⁻¹) * (x : H)⁻¹) := by group
      _ = a x * ((x : H)⁻¹ * (a y * (y : H)⁻¹)) := by rw [← hc]
      _ = (a x * (x : H)⁻¹) * (a y * (y : H)⁻¹) := by group

@[simp] theorem displacement_eq_one_iff (x : fixedPreimage c) :
    displacement c a ha x = 1 ↔ a (x : H) = x := by
  rw [Subtype.ext_iff]
  change a (x : H) * (x : H)⁻¹ = 1 ↔ _
  exact mul_inv_eq_one

theorem displacement_kernel :
    (displacement c a ha).ker = a.fixedSubgroup.subgroupOf (fixedPreimage c) := by
  ext x
  exact (displacement_eq_one_iff c a ha x).trans (MulAut.mem_fixedSubgroup _ _).symm

theorem fixes_center_of_card_two (hZ : Nat.card (center H) = 2) (x : center H) :
    a (x : H) = x := by
  by_cases hx : x = 1
  · rw [hx]; exact map_one a
  · obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : center H)).mp hZ
    have hx' : Subgroup.centerCongr a x ≠ 1 := by
      intro he
      exact hx ((Subgroup.centerCongr a).injective (he.trans (map_one _).symm))
    exact congrArg Subtype.val ((hz _ hx').trans (hz _ hx).symm)

/-- The preimage maps onto precisely the concrete fixed subgroup. -/
def fixedProjection : fixedPreimage c →* graphField.fixedSubgroup :=
  c.toMonoidHom.restrict (fun _ hx => hx)

theorem fixedProjection_surjective : Function.Surjective (fixedProjection c) := by
  intro y
  obtain ⟨x, hx⟩ := c.surjective y
  exact ⟨⟨x, show c.toMonoidHom x ∈ graphField.fixedSubgroup from hx ▸ y.property⟩, Subtype.ext hx⟩

variable (hk : c.toMonoidHom.ker = center H)

include hk in
theorem fixedProjection_kernel :
    (fixedProjection c).ker = (center H).subgroupOf (fixedPreimage c) := by
  ext x
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change c.toMonoidHom (x : H) = 1 ↔ (x : H) ∈ center H
  rw [← hk]
  rfl

/-- The quotient is relative to the actual preimage subgroup. -/
def quotientFixedEquiv :
    (fixedPreimage c ⧸ (center H).subgroupOf (fixedPreimage c)) ≃*
      graphField.fixedSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq (fixedProjection_kernel c hk).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (fixedProjection c) (fixedProjection_surjective c))

include hk in
theorem fixedProjection_kernel_le_displacement_kernel (hZ : Nat.card (center H) = 2) :
    (fixedProjection c).ker ≤ (displacement c a ha).ker := by
  intro x hx
  rw [fixedProjection_kernel c hk] at hx
  exact (displacement_eq_one_iff c a ha x).mpr
    (fixes_center_of_card_two a hZ ⟨x, hx⟩)

/-- The central displacement descends to the concrete projective fixed group. -/
def projectiveDisplacement (hZ : Nat.card (center H) = 2) :
    graphField.fixedSubgroup →* center H :=
  (QuotientGroup.lift (fixedProjection c).ker (displacement c a ha)
    (fixedProjection_kernel_le_displacement_kernel c a ha hk hZ)).comp
    (QuotientGroup.quotientKerEquivOfSurjective
      (fixedProjection c) (fixedProjection_surjective c)).symm.toMonoidHom

theorem projectiveDisplacement_apply (hZ : Nat.card (center H) = 2) (x : fixedPreimage c) :
    projectiveDisplacement c a ha hk hZ (fixedProjection c x) = displacement c a ha x := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    (fixedProjection c) (fixedProjection_surjective c)
  have hx : e.symm (fixedProjection c x) = QuotientGroup.mk' (fixedProjection c).ker x :=
    e.symm_apply_apply (QuotientGroup.mk' (fixedProjection c).ker x)
  change (QuotientGroup.lift (fixedProjection c).ker (displacement c a ha)
    (fixedProjection_kernel_le_displacement_kernel c a ha hk hZ))
    (e.symm (fixedProjection c x)) = _
  rw [hx]
  rfl

/-- Nontriviality is exactly the missing two-element image calculation. -/
theorem displacement_surjective_iff (hZ : Nat.card (center H) = 2) :
    Function.Surjective (displacement c a ha) ↔
      ∃ x : fixedPreimage c, a (x : H) ≠ x := by
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : center H)).mp hZ
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs z
    exact ⟨x, fun he => hz (hx.symm.trans ((displacement_eq_one_iff c a ha x).mpr he))⟩
  · rintro ⟨x, hx⟩ y
    by_cases hy : y = 1
    · exact ⟨1, (map_one _).trans hy.symm⟩
    · exact ⟨x, (huniq _ (fun he => hx ((displacement_eq_one_iff c a ha x).mp he))).trans
        (huniq _ hy).symm⟩

variable (hZ : Nat.card (center H) = 2)

/-- Odd order forces the actual residual model into the character kernel. -/
theorem projectiveDisplacement_model (x : model) :
    projectiveDisplacement c a ha hk hZ ⟨x, graphField_fixes_model x.property⟩ = 1 := by
  let f : model →* center H :=
    (projectiveDisplacement c a ha hk hZ).comp (inclusion graphField_fixes_model)
  change f x = 1
  have h9 : (f x) ^ 9 = 1 := by
    have hx : x ^ 9 = 1 := by simpa only [model_card] using (pow_card_eq_one' (x := x))
    rw [← map_pow, hx, map_one]
  have h2 : (f x) ^ 2 = 1 := by
    simpa only [hZ] using (pow_card_eq_one' (x := f x))
  have he : (f x) ^ 9 = f x := by
    rw [show 9 = 2 * 4 + 1 from rfl, pow_succ, pow_mul, h2, one_pow, one_mul]
  exact he.symm.trans h9

theorem projectiveDisplacement_surjective_iff :
    Function.Surjective (projectiveDisplacement c a ha hk hZ) ↔
      Function.Surjective (displacement c a ha) := by
  constructor
  · intro hf y
    obtain ⟨u, hu⟩ := hf y
    obtain ⟨x, rfl⟩ := fixedProjection_surjective c u
    exact ⟨x, (projectiveDisplacement_apply c a ha hk hZ x).symm.trans hu⟩
  · intro hf y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨fixedProjection c x, (projectiveDisplacement_apply c a ha hk hZ x).trans hx⟩

end
end Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover
