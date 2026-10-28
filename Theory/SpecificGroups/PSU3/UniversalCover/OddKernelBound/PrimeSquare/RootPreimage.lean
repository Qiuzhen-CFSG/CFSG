module
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeField
import all Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeField

/-!
# The lifted Hermitian root group and its fixed-field scalars

In odd characteristic the centered roots generate the entire root group:
every central root is a commutator of centered roots. The sign torus inverts
each centered root and fixes the central layer. Partial inversion then
makes the full preimage of that layer central in every central covering.
Thus the first coordinate of the lifted root group has central kernel.

Conjugation descends through the covering kernel and gives the actual
fixed-field scalar action on this first coordinate. The action fixes the
original covering kernel pointwise. These are the local inputs to the
scalar norm and central transfer proof at q = p².

The intentional `import all` of `PrimeField` reuses its internal centered
coordinate lemmas while preserving its public boundary. Generation here
uses all centered roots, and does not require the root group to have two
generators.

Source: Huppert II.10.12 for the literal root and torus coordinates;
Aschbacher–Smith I.1.3–4, PDF pp.418–419, and GLS3 §6.1 for the multiplier
application.
-/

open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open scoped commutatorElement
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.PrimeSquare
open OddPrimeSylow.NormalizedOuter.Coverage
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

private theorem centered_generate (htwo : (2 : F) ≠ 0) :
    closure (Set.range (centered J)) = ⊤ := by
  let C := closure (Set.range (centered J))
  have hm (a : F) : centered J a ∈ C := subset_closure ⟨a, rfl⟩
  have hz (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) : z ∈ C := by
    have hconj : J.conj z.val.2 = -z.val.2 := by
      have hh := z.property
      rw [hz, zero_mul, add_zero] at hh
      exact eq_neg_of_add_eq_zero_right hh
    have h8 : (8 : F) ≠ 0 := by
      have : (8 : F) = 2 * 2 * 2 := by ring
      rw [this]
      exact mul_ne_zero (mul_ne_zero htwo htwo) htwo
    have he : ⁅centered J 1, centered J (z.val.2 / 8)⁆ = z := by
      rw [hermitianUnipotent_commutator]
      apply Subtype.ext
      apply Prod.ext
      · exact hz.symm
      · change 2 * (z.val.2 / 8) * J.conj (2 * 1) -
          2 * 1 * J.conj (2 * (z.val.2 / 8)) = z.val.2
        simp only [map_mul, map_div₀, map_ofNat, map_one, hconj]
        field_simp
        ring
    rw [← he]
    exact C.mul_mem (C.mul_mem (C.mul_mem (hm 1) (hm _)) (C.inv_mem (hm 1)))
      (C.inv_mem (hm _))
  apply top_unique
  intro z _
  have hd : z * (centered J (z.val.1 / 2))⁻¹ ∈ C := by
    apply hz
    change z.val.1 + -(2 * (z.val.1 / 2)) = 0
    field_simp
    ring
  simpa only [inv_mul_cancel_right] using C.mul_mem hd (hm (z.val.1 / 2))


@[expose] public def rootPreimage
    {E : Type*} [Group E] (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Subgroup E := (rootGroup J hJ).comap f.toMonoidHom

variable {E : Type*} [Group E] (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J))

/-- The literal covering projection, expressed in Hermitian root coordinates. -/
public noncomputable def rootProjection :
    rootPreimage J hJ f →* hermitianUnipotentCoord J :=
  (MonoidHom.ofInjective (root_injective J hJ)).symm.toMonoidHom.comp
    ((f.toMonoidHom.comp (rootPreimage J hJ f).subtype).codRestrict _
      (fun x => x.property))

public theorem rootProjection_spec (x : rootPreimage J hJ f) :
    root J hJ (rootProjection J hJ f x) = f.toMonoidHom x := by
  exact congrArg Subtype.val
    ((MonoidHom.ofInjective (root_injective J hJ)).apply_symm_apply
      (⟨f.toMonoidHom x, x.property⟩ : rootGroup J hJ))

public theorem rootProjection_surjective : Function.Surjective (rootProjection J hJ f) := by
  intro z
  obtain ⟨x, hx⟩ := f.surjective (root J hJ z)
  have hxR : x ∈ rootPreimage J hJ f := by
    change f.toMonoidHom x ∈ (root J hJ).range
    exact ⟨z, hx.symm⟩
  refine ⟨⟨x, hxR⟩, (root_injective J hJ) ?_⟩
  exact (rootProjection_spec J hJ f _).trans hx

public theorem rootProjection_ker_le_center :
    (rootProjection J hJ f).ker ≤ center (rootPreimage J hJ f) := by
  intro x hx
  have hfx : f.toMonoidHom x = 1 := by
    rw [← rootProjection_spec J hJ f x, MonoidHom.mem_ker.mp hx, map_one]
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (mem_center_iff.mp (f.ker_le_center hfx) y)

/-- The additive first coordinate on the full root preimage. -/
@[expose] public noncomputable def coordinate : rootPreimage J hJ f →* Multiplicative F :=
  ({ toFun := fun z : hermitianUnipotentCoord J => Multiplicative.ofAdd z.val.1
     map_one' := rfl
     map_mul' := fun _ _ => rfl } : hermitianUnipotentCoord J →* Multiplicative F).comp
    (rootProjection J hJ f)

public theorem coordinate_surjective (htwo : (2 : F) ≠ 0) :
    Function.Surjective (coordinate J hJ f) := by
  intro a
  obtain ⟨x, hx⟩ := rootProjection_surjective J hJ f (centered J (a.toAdd / 2))
  refine ⟨x, ?_⟩
  change Multiplicative.ofAdd (rootProjection J hJ f x).val.1 = a
  rw [hx]
  change Multiplicative.ofAdd (2 * (a.toAdd / 2)) = a
  field_simp
  rfl

/-- Partial inversion makes the whole preimage of the central root layer central.
The generation argument uses all centered roots, not two generators. -/
public theorem coordinate_ker_le_center {p : ℕ} [Fact p.Prime] [CharP F p]
    (hodd : p ≠ 2) : (coordinate J hJ f).ker ≤ center (rootPreimage J hJ f) := by
  have hp : p.Prime := Fact.out
  have htwo : (2 : F) ≠ 0 := by
    intro hz
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff F p 2).mp hz))
  have hcop : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (fun h => hodd
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
  intro z hz
  have hz0 : (rootProjection J hJ f z).val.1 = 0 := hz
  let C := centralizer ({z} : Set (rootPreimage J hJ f))
  have hC : C.map (rootProjection J hJ f) = ⊤ := by
    apply top_unique
    rw [← centered_generate J htwo]
    apply (closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := rootProjection_surjective J hJ f (centered J a)
    refine ⟨x, ?_, hx⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hxroot : f.toMonoidHom x = root J hJ (centered J a) :=
      (rootProjection_spec J hJ f x).symm.trans (congrArg (root J hJ) hx)
    have hzroot := (rootProjection_spec J hJ f z).symm
    have hcomm := CentralExtension.commute_lifts_of_partial_inversion
      f.toMonoidHom f.surjective f.ker_le_center
      (root J hJ (centered J a)) (root J hJ (rootProjection J hJ f z))
      (hermitianTorusPSU J hJ (-1)) hcop
      (by rw [← map_pow, centered_prime_pow, map_one])
      ((show Commute (centered J a) (rootProjection J hJ f z) from
        mem_center_iff.mp (zero_first_central J _ hz0) _).map (root J hJ))
      (by rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right,
        centered_inverted, map_inv])
      (by
        change hermitianTorusPSU J hJ (-1) * root J hJ (rootProjection J hJ f z) = _
        rw [hermitianTorusPSU_mul_unipotent, zero_first_fixed J _ hz0])
      (x : E) (z : E) hxroot hzroot
    exact hcomm.eq
  have hker : (rootProjection J hJ f).ker ≤ C :=
    (rootProjection_ker_le_center J hJ f).trans (center_le_centralizer _)
  have he : C = ⊤ := by
    have h := comap_map_eq_self hker
    rw [hC, comap_top] at h
    exact h.symm
  apply mem_center_iff.mpr
  intro y
  have hy : y ∈ C := he ▸ mem_top y
  exact mem_centralizer_singleton_iff.mp hy

/-- The lifted root group has nilpotency class at most two. -/
public theorem rootPreimage_classTwo {p : ℕ} [Fact p.Prime] [CharP F p]
    (hodd : p ≠ 2) :
    _root_.commutator (rootPreimage J hJ f) ≤ center (rootPreimage J hJ f) := by
  apply le_trans _ (coordinate_ker_le_center J hJ f hodd)
  exact Abelianization.commutator_subset_ker (coordinate J hJ f)

/-- The field fixed by the stored Hermitian involution. -/
public abbrev fixedField := FixedBy.subfield F J.conj

private noncomputable def baseConjugation :
    ProjectiveSpecialUnitaryMatrixGroup J →* MulAut E :=
  f.toMonoidHom.liftOfSurjective f.surjective ⟨MulAut.conj, by
    intro x hx
    change MulAut.conj x = 1
    ext y
    change x * y * x⁻¹ = y
    rw [← mem_center_iff.mp (f.ker_le_center hx) y, mul_inv_cancel_right]⟩

private theorem baseConjugation_image (x : E) :
    baseConjugation J f (f.toMonoidHom x) = MulAut.conj x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem baseConjugation_projection (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (x : E) : f.toMonoidHom (baseConjugation J f g x) =
      g * f.toMonoidHom x * g⁻¹ := by
  obtain ⟨y, rfl⟩ := f.surjective g
  rw [baseConjugation_image]
  simp only [MulAut.conj_apply, map_mul, map_inv]

private def scalarUnit : (fixedField J)ˣ →* Fˣ where
  toFun t := Units.map (fixedField J).subtype.toMonoidHom t⁻¹
  map_one' := by simp
  map_mul' t s := by simp [mul_comm]

private theorem scalarUnit_val (t : (fixedField J)ˣ) :
    (scalarUnit J t : F) = ((t : fixedField J) : F)⁻¹ := by
  simp [scalarUnit]

private theorem scalarUnit_conj (t : (fixedField J)ˣ) :
    J.conj (scalarUnit J t : F) = (scalarUnit J t : F) := by
  rw [scalarUnit_val, map_inv₀]
  exact congrArg Inv.inv (t : fixedField J).property

private def scalarTorus : (fixedField J)ˣ →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (hermitianTorusPSU J hJ).comp (scalarUnit J)

private theorem torus_preserves_rootPreimage (t : (fixedField J)ˣ)
    (x : rootPreimage J hJ f) :
    baseConjugation J f (scalarTorus J hJ t) x ∈ rootPreimage J hJ f := by
  change f.toMonoidHom (baseConjugation J f (scalarTorus J hJ t) x) ∈ (root J hJ).range
  rw [baseConjugation_projection, ← rootProjection_spec J hJ f x]
  exact ⟨hermitianTorusAction J (scalarUnit J t) (rootProjection J hJ f x), by
    change root J hJ _ = hermitianTorusPSU J hJ (scalarUnit J t) * _ * _
    simp only [scalarTorus, MonoidHom.comp_apply]
    rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right]⟩

/-- Fixed-field scalars act on the full root preimage by lifted conjugation. -/
public noncomputable def scalarAction :
    (fixedField J)ˣ →* MulAut (rootPreimage J hJ f) where
  toFun t := {
    toFun x := ⟨baseConjugation J f (scalarTorus J hJ t) x,
      torus_preserves_rootPreimage J hJ f t x⟩
    invFun x := ⟨baseConjugation J f (scalarTorus J hJ t⁻¹) x,
      torus_preserves_rootPreimage J hJ f t⁻¹ x⟩
    left_inv x := by
      apply Subtype.ext
      change ((baseConjugation J f (scalarTorus J hJ t⁻¹)) *
        (baseConjugation J f (scalarTorus J hJ t))) x = x
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
      rfl
    right_inv x := by
      apply Subtype.ext
      change ((baseConjugation J f (scalarTorus J hJ t)) *
        (baseConjugation J f (scalarTorus J hJ t⁻¹))) x = x
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
      rfl
    map_mul' x y := Subtype.ext (map_mul _ _ _) }
  map_one' := by
    ext x
    change baseConjugation J f (scalarTorus J hJ 1) x = x
    simp
  map_mul' t s := by
    ext x
    change baseConjugation J f (scalarTorus J hJ (t*s)) x =
      baseConjugation J f (scalarTorus J hJ t)
        (baseConjugation J f (scalarTorus J hJ s) x)
    rw [map_mul, map_mul]
    rfl

/-- The scalar action fixes the original central covering kernel pointwise. -/
public theorem scalarAction_kernel (t : (fixedField J)ˣ)
    (x : rootPreimage J hJ f) (hx : f.toMonoidHom x = 1) :
    scalarAction J hJ f t x = x := by
  apply Subtype.ext
  change baseConjugation J f (scalarTorus J hJ t) x = x
  obtain ⟨y, hy⟩ := f.surjective (scalarTorus J hJ t)
  rw [← hy, baseConjugation_image]
  change y * (x : E) * y⁻¹ = x
  rw [mem_center_iff.mp (f.ker_le_center hx) y, mul_inv_cancel_right]

/-- On first coordinates this action is exactly scalar multiplication. -/
public theorem coordinate_scalarAction (t : (fixedField J)ˣ)
    (x : rootPreimage J hJ f) :
    coordinate J hJ f (scalarAction J hJ f t x) =
      Multiplicative.ofAdd ((t : fixedField J) • (coordinate J hJ f x).toAdd) := by
  have he : rootProjection J hJ f (scalarAction J hJ f t x) =
      hermitianTorusAction J (scalarUnit J t) (rootProjection J hJ f x) := by
    apply root_injective J hJ
    rw [rootProjection_spec]
    change f.toMonoidHom (baseConjugation J f (scalarTorus J hJ t) x) = _
    rw [baseConjugation_projection, ← rootProjection_spec J hJ f x]
    change hermitianTorusPSU J hJ (scalarUnit J t) * _ * _ = _
    simp only [scalarTorus, MonoidHom.comp_apply]
    rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right]
  change Multiplicative.ofAdd (rootProjection J hJ f (scalarAction J hJ f t x)).val.1 = _
  rw [he, hermitianTorusAction_fst, scalarUnit_conj, scalarUnit_val]
  change Multiplicative.ofAdd (_ * _⁻¹ * (_⁻¹)⁻¹ ^ 2) =
    Multiplicative.ofAdd (((t : fixedField J) : F) * (rootProjection J hJ f x).val.1)
  congr 1
  have ht : ((t : fixedField J) : F) ≠ 0 := by
    exact_mod_cast t.ne_zero
  field_simp

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.PrimeSquare
