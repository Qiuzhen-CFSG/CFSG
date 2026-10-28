module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Roots

/-!
# Additive coordinates for automorphisms preserving Hermitian root groups

In odd characteristic, each zero-first-coordinate element is a single
commutator. Consequently any coordinate-group automorphism induces an additive
field equivalence. If it fixes the first coordinate and commutes with the torus
element at `-1`, it fixes the whole coordinate group: apply it to the product
of `(a,b)` and `(-a,b)` and cancel `2` in the second coordinate.

This supplies the commutator calculation in Steinberg, Theorem 36, step (2),
and an odd-characteristic substitute
for the shear calculation in step (7), in `refs/KGroup/GLS3/Chapter2St1.tex`.
The actual projective root embeddings transport ambient automorphisms to these
coordinates; torus preservation and field recovery remain separate assertions.
-/

open Matrix BenderSuzuki.External
open scoped commutatorElement
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private def firstSection (h2 : (2 : E) ≠ 0) (a : E) : hermitianUnipotentCoord J :=
  ⟨(a, -(a * J.conj a) / 2), by
    dsimp only
    rw [map_div₀, map_neg, map_mul, map_ofNat, J.conj_involutive]
    field_simp
    ring⟩

/-- Every field element occurs as a first root coordinate in odd characteristic. -/
public theorem coord_first_surjective (h2 : (2 : E) ≠ 0) :
    Function.Surjective (fun z : hermitianUnipotentCoord J => z.val.1) :=
  fun a => ⟨firstSection J h2 a, rfl⟩

private theorem fst_mul (z w : hermitianUnipotentCoord J) :
    (z * w).val.1 = z.val.1 + w.val.1 := rfl
private theorem fst_inv (z : hermitianUnipotentCoord J) :
    z⁻¹.val.1 = -z.val.1 := rfl

public theorem zero_first_is_commutator (h2 : (2 : E) ≠ 0)
    (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    ∃ x y : hermitianUnipotentCoord J, ⁅x, y⁆ = z := by
  refine ⟨firstSection J h2 1, firstSection J h2 (z.val.2 / 2), ?_⟩
  rw [hermitianUnipotent_commutator]
  apply Subtype.ext
  apply Prod.ext
  · exact hz.symm
  · change z.val.2 / 2 * J.conj 1 - 1 * J.conj (z.val.2 / 2) = z.val.2
    rw [map_one, map_div₀, map_ofNat, mul_one, one_mul]
    have hp := z.property
    rw [hz, zero_mul, add_zero] at hp
    field_simp [h2]
    linear_combination -hp

public theorem coordAut_first_zero (h2 : (2 : E) ≠ 0)
    (φ : MulAut (hermitianUnipotentCoord J))
    (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    (φ z).val.1 = 0 := by
  obtain ⟨x, y, rfl⟩ := zero_first_is_commutator J h2 z hz
  rw [map_commutatorElement, hermitianUnipotent_commutator]

public theorem coordAut_first_eq (h2 : (2 : E) ≠ 0)
    (φ : MulAut (hermitianUnipotentCoord J))
    (z w : hermitianUnipotentCoord J) (hzw : z.val.1 = w.val.1) :
    (φ z).val.1 = (φ w).val.1 := by
  have hh := coordAut_first_zero J h2 φ (z * w⁻¹) (by
    rw [fst_mul, fst_inv, hzw, add_neg_cancel])
  rw [map_mul, map_inv, fst_mul, fst_inv] at hh
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hh)

public def coordFirstAddHom (h2 : (2 : E) ≠ 0)
    (φ : MulAut (hermitianUnipotentCoord J)) : E →+ E where
  toFun a := (φ (firstSection J h2 a)).val.1
  map_zero' := by
    exact coordAut_first_zero J h2 φ _ rfl
  map_add' a b := by
    have hh := coordAut_first_eq J h2 φ
      (firstSection J h2 (a + b)) (firstSection J h2 a * firstSection J h2 b) rfl
    simpa only [map_mul, fst_mul] using hh

public theorem coordFirstAddHom_apply (h2 : (2 : E) ≠ 0)
    (φ : MulAut (hermitianUnipotentCoord J)) (z : hermitianUnipotentCoord J) :
    coordFirstAddHom J h2 φ z.val.1 = (φ z).val.1 :=
  coordAut_first_eq J h2 φ _ z rfl

public theorem coordFirstAddHom_bijective (h2 : (2 : E) ≠ 0)
    (φ : MulAut (hermitianUnipotentCoord J)) :
    Function.Bijective (coordFirstAddHom J h2 φ) := by
  constructor
  · intro a b hab
    have hh := coordAut_first_eq J h2 φ.symm
      (φ (firstSection J h2 a)) (φ (firstSection J h2 b)) hab
    simpa [firstSection] using hh
  · intro a
    refine ⟨(φ.symm (firstSection J h2 a)).val.1, ?_⟩
    rw [coordFirstAddHom_apply, φ.apply_symm_apply]
    rfl

public noncomputable def coordFirstAddEquiv (h2 : (2 : E) ≠ 0)
    (φ : MulAut (hermitianUnipotentCoord J)) : E ≃+ E :=
  AddEquiv.ofBijective (coordFirstAddHom J h2 φ)
    (coordFirstAddHom_bijective J h2 φ)

public theorem coordFirstAddEquiv_apply (h2 : (2 : E) ≠ 0)
    (φ : MulAut (hermitianUnipotentCoord J)) (z : hermitianUnipotentCoord J) :
    coordFirstAddEquiv J h2 φ z.val.1 = (φ z).val.1 :=
  coordFirstAddHom_apply J h2 φ z

public theorem coordAut_fixes_zero_first (h2 : (2 : E) ≠ 0)
    (φ : MulAut (hermitianUnipotentCoord J))
    (hφ : ∀ z, (φ z).val.1 = z.val.1)
    (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) : φ z = z := by
  obtain ⟨x, y, rfl⟩ := zero_first_is_commutator J h2 z hz
  rw [map_commutatorElement, hermitianUnipotent_commutator, hermitianUnipotent_commutator]
  apply Subtype.ext
  dsimp only
  rw [hφ x, hφ y]

public theorem coordAut_eq_one_of_first_fixed (h2 : (2 : E) ≠ 0)
    (φ : MulAut (hermitianUnipotentCoord J))
    (hφ : ∀ z, (φ z).val.1 = z.val.1)
    (hneg : ∀ z, φ (hermitianTorusAction J (-1) z) =
      hermitianTorusAction J (-1) (φ z)) : φ = 1 := by
  apply MulEquiv.ext
  intro z
  have hτ (w : hermitianUnipotentCoord J) :
      (hermitianTorusAction J (-1) w).val.1 = -w.val.1 ∧
      (hermitianTorusAction J (-1) w).val.2 = w.val.2 := by
    simp [hermitianTorusAction_fst, hermitianTorusAction_snd]
  have hfix := coordAut_fixes_zero_first J h2 φ hφ
    (z * hermitianTorusAction J (-1) z) (by rw [fst_mul, (hτ z).1, add_neg_cancel])
  rw [map_mul, hneg] at hfix
  have hs := congrArg (fun t : hermitianUnipotentCoord J => t.val.2) hfix
  change (φ z).val.2 + (hermitianTorusAction J (-1) (φ z)).val.2 -
      (φ z).val.1 * J.conj (hermitianTorusAction J (-1) (φ z)).val.1 =
    z.val.2 + (hermitianTorusAction J (-1) z).val.2 -
      z.val.1 * J.conj (hermitianTorusAction J (-1) z).val.1 at hs
  rw [(hτ (φ z)).1, (hτ (φ z)).2, (hτ z).1, (hτ z).2, hφ] at hs
  apply Subtype.ext
  apply Prod.ext (hφ z)
  apply (mul_left_cancel₀ h2)
  linear_combination hs

public theorem coordAut_ext_of_first (h2 : (2 : E) ≠ 0)
    (φ ψ : MulAut (hermitianUnipotentCoord J))
    (hfirst : ∀ z, (φ z).val.1 = (ψ z).val.1)
    (hφneg : ∀ z, φ (hermitianTorusAction J (-1) z) = hermitianTorusAction J (-1) (φ z))
    (hψneg : ∀ z, ψ (hermitianTorusAction J (-1) z) = hermitianTorusAction J (-1) (ψ z)) :
    φ = ψ := by
  have hinv (z : hermitianUnipotentCoord J) :
      ψ.symm (hermitianTorusAction J (-1) z) = hermitianTorusAction J (-1) (ψ.symm z) := by
    apply ψ.injective
    rw [ψ.apply_symm_apply, hψneg, ψ.apply_symm_apply]
  have hh := coordAut_eq_one_of_first_fixed J h2 (φ.trans ψ.symm) (fun z => by
    have he := coordAut_first_eq J h2 ψ.symm (φ z) (ψ z) (hfirst z)
    simpa using he) (fun z => by
      change ψ.symm (φ (hermitianTorusAction J (-1) z)) = _
      rw [hφneg, hinv]
      rfl)
  apply MulEquiv.ext
  intro z
  have hz := congrArg (fun f : MulAut (hermitianUnipotentCoord J) => ψ (f z)) hh
  simpa using hz



variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

public noncomputable def rootCoordinateAut
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hb : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ) :
    MulAut (hermitianUnipotentCoord J) :=
  let e := MonoidHom.ofInjective (root_injective J hJ)
  e.trans (((b.subgroupMap (rootGroup J hJ)).trans (MulEquiv.subgroupCongr hb)).trans e.symm)

public theorem rootCoordinateAut_spec
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hb : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (z : hermitianUnipotentCoord J) :
    root J hJ (rootCoordinateAut J hJ b hb z) = b (root J hJ z) := by
  exact MonoidHom.apply_ofInjective_symm (root_injective J hJ) _

public noncomputable def oppositeCoordinateAut
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hb : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ) :
    MulAut (hermitianUnipotentCoord J) :=
  let e := MonoidHom.ofInjective (oppositeRoot_injective J hJ)
  e.trans (((b.subgroupMap (oppositeRootGroup J hJ)).trans (MulEquiv.subgroupCongr hb)).trans e.symm)

public theorem oppositeCoordinateAut_spec
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hb : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ)
    (z : hermitianUnipotentCoord J) :
    oppositeRoot J hJ (oppositeCoordinateAut J hJ b hb z) = b (oppositeRoot J hJ z) := by
  exact MonoidHom.apply_ofInjective_symm (oppositeRoot_injective J hJ) _

public theorem rootCoordinateAut_neg_equivariant
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hb : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (ht : b (hermitianTorusPSU J hJ (-1)) = hermitianTorusPSU J hJ (-1))
    (z : hermitianUnipotentCoord J) :
    rootCoordinateAut J hJ b hb (hermitianTorusAction J (-1) z) =
      hermitianTorusAction J (-1) (rootCoordinateAut J hJ b hb z) := by
  apply root_injective J hJ
  apply mul_right_cancel (b := hermitianTorusPSU J hJ (-1))
  rw [rootCoordinateAut_spec, ← hermitianTorusPSU_mul_unipotent,
    rootCoordinateAut_spec, ← ht, ← map_mul]
  simpa only [map_mul] using congrArg b
    (hermitianTorusPSU_mul_unipotent J hJ (-1) z).symm

@[expose] public def rootTorus : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (hermitianTorusPSU J hJ).range

public theorem torus_neg_mul_opposite (z : hermitianUnipotentCoord J) :
    hermitianTorusPSU J hJ (-1) * oppositeRoot J hJ z =
      oppositeRoot J hJ (hermitianTorusAction J (-1) z) * hermitianTorusPSU J hJ (-1) := by
  have hc := hermitianTorusPSU_commute_weyl_of_conj_eq_inv J hJ (-1) (by simp)
  have hf : (MulAut.conj (weyl J hJ)) (hermitianTorusPSU J hJ (-1)) =
      hermitianTorusPSU J hJ (-1) := by
    change weyl J hJ * _ * (weyl J hJ)⁻¹ = _
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  simpa only [map_mul, hf, oppositeRoot, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj (weyl J hJ))
    (hermitianTorusPSU_mul_unipotent J hJ (-1) z)

public theorem oppositeCoordinateAut_neg_equivariant
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hb : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ)
    (ht : b (hermitianTorusPSU J hJ (-1)) = hermitianTorusPSU J hJ (-1))
    (z : hermitianUnipotentCoord J) :
    oppositeCoordinateAut J hJ b hb (hermitianTorusAction J (-1) z) =
      hermitianTorusAction J (-1) (oppositeCoordinateAut J hJ b hb z) := by
  apply oppositeRoot_injective J hJ
  apply mul_right_cancel (b := hermitianTorusPSU J hJ (-1))
  rw [oppositeCoordinateAut_spec, ← torus_neg_mul_opposite,
    oppositeCoordinateAut_spec, ← ht, ← map_mul]
  simpa only [map_mul] using congrArg b (torus_neg_mul_opposite J hJ z).symm

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
