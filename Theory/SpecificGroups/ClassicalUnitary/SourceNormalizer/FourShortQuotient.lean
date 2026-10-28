module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Long-root representatives in the nonbinary orthogonal quotient

A symmetric Hermitian matrix has diagonal coordinates a,c over the fixed
field K. Square roots of a,c complete to a determinant-one matrix over K;
its long-root conjugate has the same diagonal. The difference is in the
entire off-diagonal short-root line. This proves transitivity on nonzero
vectors after killing that line, for every finite field of characteristic
two. The conjugator lies in the genuine prime-to-two residual.

Source: Aschbacher–Smith F.4.42, printed p.295 of `refs/quasithin.pdf`.
These calculations supply the vector-orbit premise for I.8.5 on the
normalizer quotient. Ambient unique fixed cosets remain a separate step.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
local notation "L" => localFactor F (form F σ hσ)
local notation "C" => shortCentralizer F σ hσ

/-- Every symmetric vector is in the short-root line or differs from a
long-root conjugate by an element of that entire line. -/
theorem orthogonal_cases (X : hermitianMatrices F σ)
    (hX : X ∈ fixedHermitian F σ) :
    (∃ b : K, X = lineParameter F σ b) ∨
      ∃ A : fixedSL F σ, ∃ b : K,
        X = hermitianCongruence F σ hσ A.val (longParameter F σ) +
          lineParameter F σ b := by
  let p := fixedHermitianEquiv F σ ⟨X,hX⟩
  have hcoord : X = symmetric F σ p.1 p.2.1 p.2.2 :=
    (congrArg Subtype.val ((fixedHermitianEquiv F σ).symm_apply_apply ⟨X,hX⟩)).symm
  by_cases hz : p.1 = 0 ∧ p.2.2 = 0
  · left
    refine ⟨p.2.1,?_⟩
    calc
      X = symmetric F σ p.1 p.2.1 p.2.2 := hcoord
      _ = lineParameter F σ p.2.1 := by rw [hz.1,hz.2]; rfl
  obtain ⟨r,hr⟩ := (frobeniusEquiv K 2).surjective p.1
  obtain ⟨s,hs⟩ := (frobeniusEquiv K 2).surjective p.2.2
  have hr2 : r^2 = p.1 := hr
  have hs2 : s^2 = p.2.2 := hs
  have hrs : (![r,s] : Fin 2 → K) ≠ 0 := by
    intro he
    apply hz
    have hr0 : r = 0 := congrFun he 0
    have hs0 : s = 0 := congrFun he 1
    exact ⟨by rw [←hr2,hr0]; simp, by rw [←hs2,hs0]; simp⟩
  obtain ⟨B,hB⟩ := Matrix.SL2.exists_mulVec_eq K ![1,0] ![r,s]
    (by intro he; exact one_ne_zero (congrFun he 0)) hrs
  have hb0 : B.val 0 0 = r := by
    simpa [mulVec,dotProduct,Fin.sum_univ_two] using congrFun hB 0
  have hb1 : B.val 1 0 = s := by
    simpa [mulVec,dotProduct,Fin.sum_univ_two] using congrFun hB 1
  let A := SpecialLinearGroup.map (FixedBy.subfield F σ).subtype B
  have ha : A ∈ fixedSL F σ := ⟨B,rfl⟩
  have ha0 : A.val 0 0 = (r:F) := congrArg Subtype.val hb0
  have ha1 : A.val 1 0 = (s:F) := congrArg Subtype.val hb1
  right
  have hrfixed : σ (r:F) = (r:F) := r.property
  have hsfixed : σ (s:F) = (s:F) := s.property
  have hlong : hermitianCongruence F σ hσ A (longParameter F σ) =
      symmetric F σ (r^2) (r*s) (s^2) := by
    apply Subtype.ext
    change A.val * !![1,0;0,0] * adjoint σ A.val = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adjoint,mul_apply,Fin.sum_univ_two,ha0,ha1,hrfixed,hsfixed,
        symmetric,fixedHermitianEquiv] <;> ring
  have hcoords :
      symmetric F σ p.1 p.2.1 p.2.2 =
        hermitianCongruence F σ hσ A (longParameter F σ) +
          lineParameter F σ (p.2.1-r*s) := by
    rw [hlong,hr2,hs2]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetric,lineParameter,fixedHermitianEquiv]
  refine ⟨⟨A,ha⟩,p.2.1-r*s,?_⟩
  exact hcoord.trans hcoords

/-- A homomorphism killing the whole short-root line sends every nonzero
orthogonal vector to a long-root conjugate by a fixed-field Levi element. -/
theorem orthogonal_image_fusion {H : Type*} [Group H] (f : C →* H)
    (hU : (shortLine F σ hσ).subgroupOf C ≤ f.ker)
    {v : H} (hv : v ∈ ((orthogonalRadical F σ hσ).subgroupOf C).map f)
    (hv1 : v ≠ 1) :
    ∃ A : fixedSL F σ,
      f (fixedLevi F σ hσ A) * f (longMark F σ hσ) *
        (f (fixedLevi F σ hσ A))⁻¹ = v := by
  have hmap : (fixedHermitian F σ).toSubgroup.map (radicalIntoCentralizer F σ hσ) =
      (orthogonalRadical F σ hσ).subgroupOf C := radicalIntoCentralizer_map F σ hσ
  rw [←hmap, Subgroup.map_map] at hv
  obtain ⟨X,hX,rfl⟩ := hv
  obtain ⟨b,hb⟩ | ⟨A,b,hb⟩ := orthogonal_cases F σ hσ X.toAdd hX
  · exfalso
    apply hv1
    have hline : radicalIntoCentralizer F σ hσ
        (Multiplicative.ofAdd (lineParameter F σ b)) ∈ (shortLine F σ hσ).subgroupOf C := by
      change radicalHom F σ hσ (Multiplicative.ofAdd (lineParameter F σ b)) ∈
        (lineHom F σ hσ).range
      exact ⟨Multiplicative.ofAdd b,rfl⟩
    have hkill : f (radicalIntoCentralizer F σ hσ
        (Multiplicative.ofAdd (lineParameter F σ b))) = 1 :=
      MonoidHom.mem_ker.mp (hU hline)
    have hx : radicalIntoCentralizer F σ hσ X =
        radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd (lineParameter F σ b)) := by
      apply Subtype.ext
      exact congrArg (radicalHom F σ hσ) (congrArg Multiplicative.ofAdd hb)
    exact (congrArg f hx).trans hkill
  · refine ⟨A,?_⟩
    have hline : radicalIntoCentralizer F σ hσ
        (Multiplicative.ofAdd (lineParameter F σ b)) ∈ (shortLine F σ hσ).subgroupOf C := by
      change radicalHom F σ hσ (Multiplicative.ofAdd (lineParameter F σ b)) ∈
        (lineHom F σ hσ).range
      exact ⟨Multiplicative.ofAdd b,rfl⟩
    have hbkill : f (radicalIntoCentralizer F σ hσ
        (Multiplicative.ofAdd (lineParameter F σ b))) = 1 := MonoidHom.mem_ker.mp (hU hline)
    rw [←map_inv,←map_mul,←map_mul]
    change f ((fixedLevi F σ hσ A) * radicalIntoCentralizer F σ hσ
      (Multiplicative.ofAdd (longParameter F σ)) * (fixedLevi F σ hσ A)⁻¹) = _
    rw [radicalIntoCentralizer_conj]
    simp only [fixedLevi,factorRestriction_levi,toAdd_ofAdd]
    have hx : X = Multiplicative.ofAdd (hermitianCongruence F σ hσ A.val (longParameter F σ)) *
        Multiplicative.ofAdd (lineParameter F σ b) := congrArg Multiplicative.ofAdd hb
    change _ = f (radicalIntoCentralizer F σ hσ X)
    rw [hx,map_mul,map_mul,hbkill,mul_one]

/-- The conjugator belongs to the actual prime-to-two residual. -/
theorem orthogonal_image_residual_fusion {H : Type*} [Group H] (f : C →* H)
    (hU : (shortLine F σ hσ).subgroupOf C ≤ f.ker)
    {v : H} (hv : v ∈ ((orthogonalRadical F σ hσ).subgroupOf C).map f)
    (hv1 : v ≠ 1) :
    ∃ a ∈ primeToResidual 2 C, f a * f (longMark F σ hσ) * (f a)⁻¹ = v := by
  obtain ⟨A,he⟩ := orthogonal_image_fusion F σ hσ f hU hv hv1
  obtain ⟨B,hB⟩ := A.property
  have heq : fixedLeviHom F σ hσ B = fixedLevi F σ hσ A := by
    apply Subtype.ext
    change levi F σ hσ (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype B) =
      levi F σ hσ A.val
    rw [hB]
  refine ⟨fixedLevi F σ hσ A,?_,he⟩
  rw [←heq]
  exact Matrix.SL2.map_mem_primeToResidual 2 (fixedLeviHom F σ hσ) B

instance shortLine_normal : ((shortLine F σ hσ).subgroupOf C).Normal := by
  constructor
  intro x hx g
  have he := mem_center_iff.mp (shortLine_le_center F σ hσ hx) g
  simpa only [he,mul_inv_cancel_right] using hx

/-- The actual quotient by the full central short-root line has one
conjugacy class of nonidentity vectors from the orthogonal module. -/
theorem orthogonal_quotient_fusion
    {v : C ⧸ (shortLine F σ hσ).subgroupOf C}
    (hv : v ∈ ((orthogonalRadical F σ hσ).subgroupOf C).map
      (QuotientGroup.mk' ((shortLine F σ hσ).subgroupOf C)))
    (hv1 : v ≠ 1) :
    IsConj (QuotientGroup.mk' ((shortLine F σ hσ).subgroupOf C)
      (longMark F σ hσ)) v := by
  let f := QuotientGroup.mk' ((shortLine F σ hσ).subgroupOf C)
  have hU : (shortLine F σ hσ).subgroupOf C ≤ f.ker := by
    rw [QuotientGroup.ker_mk']
  obtain ⟨a,ha,he⟩ := orthogonal_image_residual_fusion F σ hσ f hU hv hv1
  apply isConj_iff.mpr
  refine ⟨f a,?_⟩
  simpa only [f,map_mul,map_inv] using he

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
