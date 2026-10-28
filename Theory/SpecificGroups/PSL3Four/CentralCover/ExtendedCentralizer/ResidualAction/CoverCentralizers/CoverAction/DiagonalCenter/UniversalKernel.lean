module

public import Theory.SpecificGroups.PSL3Four.CentralCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Transferring universal-kernel displacement to the four-cover

Every projective automorphism lifts uniquely to the constructed universal
perfect central cover. Its action on the kernel depends only on its outer
class. For a compatible perfect four-cover, the universal map intertwines
these lifts. If the covering center were fixed pointwise, that map would kill
both squares in the universal kernel and all displacements under the lift.
Generation of the kernel by those elements would then kill the entire
nontrivial covering center.

The generation premise is explicit. This module supplies the universal-cover
transfer, not the exceptional multiplier action calculation. Source:
Aschbacher--Smith 15.3.38, printed pp.1136--1137, and I.1.3(6), manuscript
of 1 March 2004.
-/

public section

open Subgroup PerfectCentralCovering
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter

private instance : Group.IsPerfect PSL := Atlas.psl_perfect (F := F) 3 (by decide)

private theorem exists_universalLift (β : MulAut PSL) :
    ∃ a : MulAut (UniversalGroup PSL), ∀ x,
      universalProjection PSL (a x) = β (universalProjection PSL x) := by
  let p := universalProjection PSL
  let q := β.symm.toMonoidHom.comp p
  have hq : Function.Surjective q := β.symm.surjective.comp
    (universalProjection_surjective PSL)
  have hqker : q.ker ≤ center (UniversalGroup PSL) := by
    intro x hx
    apply universalProjection_ker_le_center PSL
    change β.symm (p x) = 1 at hx
    exact β.symm.injective (hx.trans (map_one β.symm).symm)
  obtain ⟨a, ha, _⟩ := universalProjection_existsUnique_lift q hq hqker
  have hasurj : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect q a
      (ha ▸ universalProjection_surjective PSL) hqker
  let e := MulEquiv.ofBijective a
    ⟨(Finite.injective_iff_surjective).mpr hasurj, hasurj⟩
  refine ⟨e, fun x => ?_⟩
  have hx := DFunLike.congr_fun ha x
  change β.symm (p (a x)) = p x at hx
  exact β.symm.injective (hx.trans (β.symm_apply_apply (p x)).symm)

/-- The unique lift to the actual universal perfect central cover. -/
noncomputable def universalLift (β : MulAut PSL) : MulAut (UniversalGroup PSL) :=
  Classical.choose (exists_universalLift β)

theorem universalLift_compatible (β : MulAut PSL) (x : UniversalGroup PSL) :
    universalProjection PSL (universalLift β x) = β (universalProjection PSL x) :=
  Classical.choose_spec (exists_universalLift β) x

/-- Perfectness makes a compatible lift unique. -/
theorem universalLift_unique (β : MulAut PSL) (a : MulAut (UniversalGroup PSL))
    (ha : ∀ x, universalProjection PSL (a x) = β (universalProjection PSL x)) :
    a = universalLift β := by
  apply MulEquiv.toMonoidHom_injective
  apply monoidHom_eq_of_isPerfect_of_comp_eq (universalProjection PSL)
    (universalProjection_ker_le_center PSL)
  ext x
  exact (ha x).trans (universalLift_compatible β x).symm

/-- Lifting respects composition of the actual projective automorphisms. -/
theorem universalLift_mul (β γ : MulAut PSL) :
    universalLift (β * γ) = universalLift β * universalLift γ := by
  apply Eq.symm
  apply universalLift_unique
  intro x
  change universalProjection PSL (universalLift β (universalLift γ x)) = _
  rw [universalLift_compatible, universalLift_compatible]
  rfl

/-- An inner projective automorphism acts trivially on the central kernel. -/
theorem universalLift_inner_apply (g : PSL) (z : (universalProjection PSL).ker) :
    universalLift (MulAut.conj g) z = z := by
  obtain ⟨u, rfl⟩ := universalProjection_surjective PSL g
  have hu : MulAut.conj u = universalLift (MulAut.conj (universalProjection PSL u)) := by
    apply universalLift_unique
    intro x
    change universalProjection PSL (u * x * u⁻¹) = _
    simp only [map_mul, map_inv, MulAut.conj_apply]
  rw [← hu]
  change u * (z : UniversalGroup PSL) * u⁻¹ = z
  rw [mem_center_iff.mp (universalProjection_ker_le_center PSL z.property) u,
    mul_inv_cancel_right]

/-- On the universal kernel, an inner factor does not change the lifted action. -/
theorem universalLift_mul_inner_apply (β : MulAut PSL) (g : PSL)
    (z : (universalProjection PSL).ker) :
    universalLift (β * MulAut.conj g) z = universalLift β z := by
  rw [universalLift_mul, MulAut.mul_apply, universalLift_inner_apply]

/-- Squares and lift displacements, generated inside the actual universal cover. -/
@[expose] noncomputable def kernelSquaresAndDisplacements (β : MulAut PSL) :
    Subgroup (UniversalGroup PSL) :=
  closure (Set.range (fun z : (universalProjection PSL).ker => (z : UniversalGroup PSL) ^ 2) ∪
    Set.range (fun z : (universalProjection PSL).ker =>
      universalLift β z * (z : UniversalGroup PSL)⁻¹))

/-- All the displayed generators lie in the universal covering kernel. -/
theorem kernelSquaresAndDisplacements_le (β : MulAut PSL) :
    kernelSquaresAndDisplacements β ≤ (universalProjection PSL).ker := by
  apply (closure_le _).mpr
  rintro _ (⟨z, rfl⟩ | ⟨z, rfl⟩)
  · exact (universalProjection PSL).ker.pow_mem z.property 2
  · change universalProjection PSL (universalLift β z * (z : UniversalGroup PSL)⁻¹) = 1
    rw [map_mul, map_inv, universalLift_compatible, show universalProjection PSL z = 1
      from z.property, map_one, inv_one, mul_one]

/-- The kernel generation problem is unchanged by an inner projective factor. -/
theorem kernelSquaresAndDisplacements_mul_inner (β : MulAut PSL) (g : PSL) :
    kernelSquaresAndDisplacements (β * MulAut.conj g) = kernelSquaresAndDisplacements β := by
  simp only [kernelSquaresAndDisplacements, universalLift_mul_inner_apply]

/-- Kernel generation forces movement in every compatible perfect four-cover. -/
theorem cover_moves_center_of_kernel_generation {E : Type*} [Group E]
    (c : FourCover E) (a : MulAut E) (β : MulAut PSL)
    (hab : ∀ x, c.toMonoidHom (a x) = β (c.toMonoidHom x))
    (hgen : (universalProjection PSL).ker ≤ kernelSquaresAndDisplacements β) :
    ∃ z : center E, a (z : E) ≠ z := by
  classical
  by_contra h
  push Not at h
  let := c.isPerfect
  let := c.center_isKleinFour
  obtain ⟨f, hf, _⟩ := universalProjection_existsUnique_lift
    c.toMonoidHom c.surjective c.ker_le_center
  have hf' (x) : c.toMonoidHom (f x) = universalProjection PSL x :=
    DFunLike.congr_fun hf x
  have hsurj : Function.Surjective f :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect c.toMonoidHom f
      (hf ▸ universalProjection_surjective PSL) c.ker_le_center
  have hnat : f.comp (universalLift β).toMonoidHom = a.toMonoidHom.comp f := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq c.toMonoidHom c.ker_le_center
    ext x
    exact (hf' _).trans ((universalLift_compatible β x).trans
      ((congrArg β (hf' x)).symm.trans (hab (f x)).symm))
  have hfZ (z : (universalProjection PSL).ker) : f z ∈ center E := by
    apply c.ker_le_center
    exact (hf' z).trans z.property
  have hkill : kernelSquaresAndDisplacements β ≤ f.ker := by
    apply (closure_le f.ker).2
    rintro _ (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · change f ((z : UniversalGroup PSL) ^ 2) = 1
      rw [map_pow]
      exact congrArg Subtype.val (show (⟨f z, hfZ z⟩ : center E) ^ 2 = 1 by
        rw [pow_two, IsKleinFour.mul_self])
    · change f (universalLift β z * (z : UniversalGroup PSL)⁻¹) = 1
      rw [map_mul, map_inv]
      have hn := DFunLike.congr_fun hnat (z : UniversalGroup PSL)
      change f (universalLift β z) = a (f z) at hn
      rw [hn, h ⟨f z, hfZ z⟩, mul_inv_cancel]
  have hZ : center E = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    obtain ⟨x, rfl⟩ := hsurj z
    have hzker : f x ∈ c.toMonoidHom.ker := c.ker_eq_center.symm ▸ hz
    have hx : x ∈ (universalProjection PSL).ker := (hf' x).symm.trans hzker
    exact hkill (hgen hx)
  have hc := c.center_isKleinFour.card_four
  rw [hZ, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩] at hc
  contradiction

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
