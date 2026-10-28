module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourRoots
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourFixed
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneGeometry

/-!
# Pointwise simple-root rigidity in PSU₄

The native plane diagonal scales the short-root parameter by a², and the
split diagonal scales the long-root parameter by b². Both square maps are
surjective in the finite fields of characteristic two. An automorphism
fixing the full diagonal Cartan and preserving either root group therefore
acts there by one scalar. If its square is one, that scalar is one.

This is the pointwise rigidity step for the direct Cartan route of
Aschbacher–Smith F.4.10,16–17, printed pp.279,282–283. It includes fixed
field four and does not impose odd order on an extension's full Borel.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourRootRigidity
open UnitaryFourFlag UnitaryFourGeneration UnitaryFourSylow UnitaryFourPointLocal
open UnitaryFourPointQuotient FourRoots
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "K" => FixedField F σ
local notation "π" => project F J

def shortTorus (a : Fˣ) : SU F J :=
  UnitaryFourPlaneGeometry.planeScale F σ hσ a a.ne_zero

omit [Finite F] in
theorem shortTorus_val (a : Fˣ) : (shortTorus F σ hσ a).val.val =
    Matrix.diagonal ![σ a,(σ a)⁻¹,(a:F),(a:F)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shortTorus,UnitaryFourPlaneGeometry.planeScale,
      UnitaryFourPlaneRadical.leviSU,UnitaryFourPlaneRadical.leviMatrix,hσ (a:F)]

omit [Finite F] in
private theorem shortTorus_diagonal (a : Fˣ) :
    FourDiagonal.IsDiagonal F σ hσ (shortTorus F σ hσ a) :=
  ⟨_,shortTorus_val F σ hσ a⟩

omit [Finite F] in
private theorem shortTorus_root (a : Fˣ) (x : F) :
    shortTorus F σ hσ a*shortRoot F σ hσ x*(shortTorus F σ hσ a)⁻¹=
      shortRoot F σ hσ ((a:F)^2*x) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  change (shortTorus F σ hσ a).val.val*(shortRoot F σ hσ x).val.val=
    (shortRoot F σ hσ ((a:F)^2*x)).val.val*(shortTorus F σ hσ a).val.val
  rw [shortTorus_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shortRoot,radicalElement,radicalMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal,
      map_mul,pow_two,a.ne_zero,mul_assoc,mul_comm]

omit [CharP F 2] in
private theorem longTorus_diagonal (a : Kˣ) :
    FourDiagonal.IsDiagonal F σ hσ (FourFixed.torus F σ hσ 1 a).val :=
  ⟨_,FourFixed.torus_val F σ hσ 1 a⟩

private theorem longTorus_root (a : Kˣ) (x : K) :
    (FourFixed.torus F σ hσ 1 a).val*longRoot F σ hσ x*
      (FourFixed.torus F σ hσ 1 a).val⁻¹=longRoot F σ hσ ((a:K)^2*x) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  change (FourFixed.torus F σ hσ 1 a).val.val.val*
    (leviSL F σ hσ _).val.val.val=(leviSL F σ hσ _).val.val.val*
      (FourFixed.torus F σ hσ 1 a).val.val.val
  rw [FourFixed.torus_val,leviSL_val,leviSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMatrix,SpecialLinearGroup.upperUnipotentHom,SpecialLinearGroup.transvection_coe,
      Matrix.diagonal_mul,Matrix.mul_diagonal,pow_two,mul_assoc,mul_comm]

private theorem short_injective : Function.Injective (fun x : F => π (shortRoot F σ hσ x)) := by
  intro x y he
  have h := congrArg (fun g : SU F J => g.val.val 2 3) ((project_injective F J) he)
  exact h

private theorem long_injective : Function.Injective (fun x : K => π (longRoot F σ hσ x)) := by
  intro x y he
  apply Subtype.ext
  have h := congrArg (fun g : SU F J => g.val.val 1 2) ((project_injective F J) he)
  simpa [longRoot,leviSL_val,leviMatrix,SpecialLinearGroup.upperUnipotentHom,
    SpecialLinearGroup.transvection_coe] using h

omit [Finite F] in
private theorem short_zero : shortRoot F σ hσ 0=1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shortRoot,radicalElement,radicalMatrix]

omit [Finite F] in
private theorem long_zero : longRoot F σ hσ 0=1 := by
  change (leviSL F σ hσ (SpecialLinearGroup.upperUnipotentHom K 1)).val=1
  rw [map_one,map_one]
  rfl

private theorem scalar_involution_fixed {k B : Type*} [Field k] [Finite k] [CharP k 2]
    [Group B] (r : k → B) (hr : Function.Injective r) (hz : r 0=1)
    (a : MulAut B) (ha : a^2=1) (hy : ∃ y, a (r 1)=r y)
    (ht : ∀ u : kˣ, ∃ t : B, a t=t ∧ ∀ x, t*r x*t⁻¹=r ((u:k)^2*x)) :
    ∀ x, a (r x)=r x := by
  obtain ⟨y,hy⟩ := hy
  have scalar (x : k) : a (r x)=r (x*y) := by
    by_cases hx : x=0
    · simp [hx,hz]
    obtain ⟨v,hv⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R:=k))) x
    have hv0 : v ≠ 0 := by intro h; simp [h] at hv; exact hx hv.symm
    let u : kˣ := Units.mk0 v hv0
    obtain ⟨t,hat,ht⟩ := ht u
    have h1 : t*r 1*t⁻¹=r x := by simpa only [u,Units.val_mk0,hv,mul_one] using ht 1
    rw [←h1,map_mul,map_mul,map_inv,hat,hy,ht]
    simp only [u,Units.val_mk0,hv]
  have hy2 : y^2=1 := by
    apply hr
    have hh := DFunLike.congr_fun ha (r 1)
    change a (a (r 1))=r 1 at hh
    rw [hy,scalar] at hh
    simpa only [pow_two] using hh
  have hy1 : y=1 := CharTwo.sq_injective (hy2.trans (one_pow 2).symm)
  intro x
  simpa only [hy1,mul_one] using scalar x

/-- The full diagonal Cartan and the involution relation turn setwise
simple-root invariance into pointwise fixation, including fixed field four. -/
theorem fixes_simpleRoots (a : MulAut (PSU F J)) (ha : a^2=1)
    (hC : ∀ g : SU F J, FourDiagonal.IsDiagonal F σ hσ g → a (π g)=π g)
    (hshort : ∀ x : F, ∃ y, a (π (shortRoot F σ hσ x))=π (shortRoot F σ hσ y))
    (hlong : ∀ x : K, ∃ y, a (π (longRoot F σ hσ x))=π (longRoot F σ hσ y)) :
    (∀ x : F, a (π (shortRoot F σ hσ x))=π (shortRoot F σ hσ x)) ∧
    (∀ x : K, a (π (longRoot F σ hσ x))=π (longRoot F σ hσ x)) := by
  constructor
  · apply scalar_involution_fixed (fun x => π (shortRoot F σ hσ x))
      (short_injective F σ hσ) (by rw [short_zero,map_one]) a ha (hshort 1)
    intro u
    refine ⟨π (shortTorus F σ hσ u),hC _ (shortTorus_diagonal F σ hσ u),?_⟩
    intro x
    simpa only [map_mul,map_inv] using congrArg π (shortTorus_root F σ hσ u x)
  · apply scalar_involution_fixed (fun x => π (longRoot F σ hσ x))
      (long_injective F σ hσ) (by rw [long_zero,map_one]) a ha (hlong 1)
    intro u
    refine ⟨π (FourFixed.torus F σ hσ 1 u).val,hC _ (longTorus_diagonal F σ hσ u),?_⟩
    intro x
    simpa only [map_mul,map_inv] using congrArg π (longTorus_root F σ hσ u x)
end Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourRootRigidity
