module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.AlternatingSeven.Basic
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.Quasithin.EvenCharacteristic
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.CoverIntersections
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# Fixed points and intersections in the A₇ central covers

A fixed point in the central quotient lifts to a fixed point of the involution:
if `c = α(x)x⁻¹` is the displacement, then `α(c) = c⁻¹` and `c³ = 1`, so
`c⁻¹x` is fixed. Thus the lifted fixed subgroup maps onto the entire partition
stabilizer. Centralizer containment in the local setup puts it inside `L ∩ M`.

If the intersection has characteristic two, its map into the central quotient
is injective by the odd-center argument. We construct the resulting equivalence
with its image and transport characteristic two through that equivalence.
The intersection is subnormal in `H ∩ M`, so characteristic-two inheritance
supplies the injectivity premise directly from the local setup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.3(1), 1.1.5(3)(d), and 2.3.9(7)(c), printed pp.500–501 and 525–526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSeven

open Subgroup

variable {K P : Type*} [Group K] [Group P]

/-- Correct a lift by its displacement under the involution. -/
private theorem exists_fixed_lift_of_cube_kernel (f : K →* P) (hf : Function.Surjective f)
    (hker : ∀ c ∈ f.ker, c ^ 3 = 1) (α : MulAut K) (hα : α ^ 2 = 1)
    (y : P) (hy : ∀ x, f x = y → f (α x) = y) :
    ∃ x : K, f x = y ∧ α x = x := by
  obtain ⟨x, hx⟩ := hf y
  let c : K := α x * x⁻¹
  have hfc : f c = 1 := by simp [c, hy x hx, hx]
  have hc : c ^ 3 = 1 := hker c (MonoidHom.mem_ker.mpr hfc)
  have hαα : α (α x) = x := by
    have hh := DFunLike.congr_fun hα x
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hαc : α c = c⁻¹ := by
    dsimp [c]
    rw [map_mul, map_inv, hαα]
    group
  have hαx : α x = c * x := by simp [c]
  have hcc : c * c = c⁻¹ := by
    apply (eq_inv_iff_mul_eq_one).mpr
    simpa only [pow_succ, pow_zero, one_mul] using hc
  refine ⟨c⁻¹ * x, by simp [hfc, hx], ?_⟩
  rw [map_mul, map_inv, hαc, inv_inv, hαx, ← mul_assoc, hcc]

private theorem center_cube (hZ : Nat.card (center K) = 1 ∨ Nat.card (center K) = 3)
    (c : K) (hc : c ∈ center K) : c ^ 3 = 1 := by
  have hh := pow_card_eq_one' (x := (⟨c, hc⟩ : center K))
  rcases hZ with hZ | hZ
  · rw [hZ, pow_one] at hh
    have hc1 : c = 1 := congrArg Subtype.val hh
    rw [hc1, one_pow]
  · rw [hZ] at hh
    exact congrArg Subtype.val hh

/-- The fixed subgroup of the genuine lifted action. -/
def fixedSubgroup (α : MulAut K) : Subgroup K :=
  α.toMonoidHom.eqLocus (MonoidHom.id K)

/-- The fixed subgroup maps onto the whole alternating partition stabilizer,
including for the nonsplit threefold cover. -/
theorem fixedSubgroup_image (e : (K ⧸ center K) ≃* A7)
    (hZ : Nat.card (center K) = 1 ∨ Nat.card (center K) = 3)
    (α : MulAut K) (hα : α ^ 2 = 1) (ha : ActsAsTripleSwap e α) :
    (fixedSubgroup α).map (quotientMap e) = alternatingStabilizer := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change α x = x at hx
    apply (mem_alternatingStabilizer _).mpr
    have he := ha x
    rw [hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · intro y hy
    have hlift : ∀ x : K, quotientMap e x = y → quotientMap e (α x) = y := by
      intro x hx
      apply Subtype.ext
      have he := ha x
      rw [hx] at he
      rw [he, ← (mem_alternatingStabilizer _).mp hy, mul_inv_cancel_right]
    obtain ⟨x, hx, hfix⟩ := exists_fixed_lift_of_cube_kernel (quotientMap e)
      (quotientMap_surjective e)
      (fun c hc => center_cube hZ c (by simpa only [quotientMap_ker] using hc))
      α hα y hlift
    exact mem_map.mpr ⟨x, hfix, hx⟩

/-- On a characteristic-two subgroup the actual quotient map is injective. -/
theorem quotientMap_injective_on_even [Finite K]
    (e : (K ⧸ center K) ≃* A7)
    (hZ : Nat.card (center K) = 1 ∨ Nat.card (center K) = 3)
    {N : Subgroup K} (hN : N ∈ Chapter1.He K) :
    Function.Injective ((quotientMap e).comp N.subtype) := by
  have hp : IsPGroup 3 (center K) := by
    apply IsPGroup.iff_card.mpr
    rcases hZ with hZ | hZ
    · exact ⟨0, by simpa using hZ⟩
    · exact ⟨1, by simpa using hZ⟩
  exact e.injective.comp (central_quotient_injective_of_even hN hp (by decide))

/-- The quotient restricted to a subgroup, with codomain its actual image. -/
def imageMap (e : (K ⧸ center K) ≃* A7) (N : Subgroup K) :
    N →* N.map (quotientMap e) :=
  ((quotientMap e).comp N.subtype).codRestrict _
    (fun x => mem_map.mpr ⟨x, x.property, rfl⟩)

/-- This equivalence retains the original quotient map on elements. -/
noncomputable def imageEquiv (e : (K ⧸ center K) ≃* A7) (N : Subgroup K)
    (hinj : Function.Injective ((quotientMap e).comp N.subtype)) :
    N ≃* N.map (quotientMap e) :=
  MulEquiv.ofBijective (imageMap e N) ⟨
    fun _ _ h => hinj (congrArg Subtype.val h),
    fun y => by
      obtain ⟨x, hx, he⟩ := y.property
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩⟩

@[simp] theorem imageEquiv_apply (e : (K ⧸ center K) ≃* A7) (N : Subgroup K)
    (hinj : Function.Injective ((quotientMap e).comp N.subtype)) (x : N) :
    (imageEquiv e N hinj x : A7) = quotientMap e (x : K) := rfl

/-- The image inherits characteristic two by the proved injectivity, rather
than by an invalid general quotient-inheritance assertion. -/
theorem image_even [Finite K] (e : (K ⧸ center K) ≃* A7)
    (hZ : Nat.card (center K) = 1 ∨ Nat.card (center K) = 3)
    {N : Subgroup K} (hN : N ∈ Chapter1.He K) :
    N.map (quotientMap e) ∈ Chapter1.He A7 := by
  apply Chapter1.mem_He_iff.mpr
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (imageEquiv e N (quotientMap_injective_on_even e hZ hN))).mp
    (Chapter1.mem_He_iff.mp hN)

variable {G : Type*} [Group G]

/-- The two intrinsic copies of the intersection: this is the bridge from
subnormality inside `H ∩ M` to a subgroup of the component. -/
def intersectionInLocalEquiv {H L M : Subgroup G} (hLH : L ≤ H) :
    M.subgroupOf L ≃* L.subgroupOf (H ⊓ M) where
  toFun x := ⟨⟨(x : L), hLH (x : L).property, x.property⟩, (x : L).property⟩
  invFun x := ⟨⟨((x : (H ⊓ M : Subgroup G)) : G), x.property⟩, (x : (H ⊓ M : Subgroup G)).property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The relative subnormality needed for characteristic-two inheritance. -/
theorem intersection_subnormal {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) : (L.subgroupOf (H ⊓ M)).IsSubnormal := by
  exact h.component.1.comap (Subgroup.inclusion (show H ⊓ M ≤ H from inf_le_left))

/-- The actual component intersection inherits characteristic two from
`H ∩ M` along its relative subnormal chain. -/
theorem intersection_even {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) : M.subgroupOf L ∈ Chapter1.He L := by
  let : Finite G := h.finite
  apply Chapter1.mem_He_iff.mpr
  apply (Theory.Quasithin.centralizer_pCore_le_iff 2
    (intersectionInLocalEquiv h.component_le)).mpr
  exact Subgroup.subnormal_core_selfCentralizing
    (Chapter1.mem_He_iff.mp h.local_even) _ (intersection_subnormal h)

/-- Centralizer containment from the local setup puts every lifted fixed
point in the actual intersection. -/
theorem fixedSubgroup_le_intersection {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹) :
    fixedSubgroup α ≤ M.subgroupOf L := by
  intro x hx
  change α x = x at hx
  have he := hα x
  rw [hx] at he
  exact h.centralizer_le (mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp he.symm).symm)

/-- The entire partition stabilizer, not just some quotient subgroup, lies
in the image of the intersection. No characteristic-two premise is used here. -/
theorem stabilizer_le_intersection_image {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : (L ⧸ center L) ≃* A7)
    (hZ : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (ha : ActsAsTripleSwap e α) :
    alternatingStabilizer ≤ (M.subgroupOf L).map (quotientMap e) := by
  rw [← fixedSubgroup_image e hZ α (h.action_sq α hα) ha]
  exact map_mono (fixedSubgroup_le_intersection h α hα)

end CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSeven
end
