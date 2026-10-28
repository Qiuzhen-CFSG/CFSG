module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourAction
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourPointField
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCenter
public import Mathlib.Algebra.CharP.Reduced

/-!
# The original U₄ point-center kernel

An automorphism of the point residual that is trivial on its SL₂ quotient
acts by a fixed-field scalar on the center of the Heisenberg radical.
The horizontal action commutes with SL₂; the trace identity A+A⁻¹=tr(A)I
makes it linear over the fixed field. The radical square map then forces
the central action to be scalar. A two-power-order scalar is trivial in
characteristic two.

Transport through the same original selected residual shows that O₂(RS)
centralizes Z(R). The proved normalized-Borel factorization
S=O₂(RS)(T∩L) extends this to all of the original S. This is a kernel
restriction toward the degree-two U₄ extension, not that degree bound or
the full original amalgam comparison. No equality S=T or R=O²(H) is used.

The private horizontal-coordinate calculations adapt the proofs in
`Theory/SpecificGroups/ClassicalUnitary/SourceNormalizer/FourPointField.lean`;
the local-center inclusion is the calculation from `FourCenter.lean`.
Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6--7,
pp.650--651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour.CenterKernel
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "L" => localSU F (form F σ hσ)
local notation "K" => FixedBy.subfield F σ
local notation "κ" => coordinatesOfRadical F σ hσ

private theorem coord_mul (r s : R) :
    (κ (r*s)).x = (κ r).x + (κ s).x ∧
    (κ (r*s)).y = (κ r).y + (κ s).y ∧
    (κ (r*s)).z = (κ r).z + (κ s).z + σ (κ r).y * (κ s).x +
      σ (κ r).x * (κ s).y := by
  obtain ⟨r,rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective r
  obtain ⟨s,rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective s
  exact radical_mul_coordinates F σ hσ r s

private def horizontal : R →* Multiplicative (F × F) where
  toFun r := Multiplicative.ofAdd ((κ r).x,(κ r).y)
  map_one' := rfl
  map_mul' r s := congrArg Multiplicative.ofAdd
    (Prod.ext (coord_mul F σ hσ r s).1 (coord_mul F σ hσ r s).2.1)

private theorem horizontal_surjective : Function.Surjective (horizontal F σ hσ) := by
  intro v
  refine ⟨radicalOfCoordinates F σ hσ ⟨v.toAdd.1,v.toAdd.2,
    v.toAdd.1*σ v.toAdd.2,?_⟩,rfl⟩
  rw [map_mul,hσ]
  ring

private theorem horizontal_ker (hnt : ∃ x, σ x ≠ x) :
    (horizontal F σ hσ).ker = center R := by
  ext x
  rw [mem_center_radical_iff F σ hσ hnt]
  exact Prod.ext_iff

private theorem coord_square (r : R) :
    (κ (r^2)).z=σ (κ r).y*(κ r).x+σ (κ r).x*(κ r).y := by
  rw [pow_two,(coord_mul F σ hσ r r).2.2,CharTwo.add_self_eq_zero,zero_add]

private def conjugate (g : L) (r : R) : R :=
  ⟨g*r.val*g⁻¹,(radical_normal F σ hσ).conj_mem _ r.property g⟩

private theorem horizontal_conjugate (g : L) (r : R) :
    (κ (conjugate F σ hσ g r)).x =
      ((middleSL F σ hσ g).val 0 0 : F)*(κ r).x+
      ((middleSL F σ hσ g).val 0 1 : F)*(κ r).y ∧
    (κ (conjugate F σ hσ g r)).y =
      ((middleSL F σ hσ g).val 1 0 : F)*(κ r).x+
      ((middleSL F σ hσ g).val 1 1 : F)*(κ r).y := by
  let A := middleSL F σ hσ g
  let l := leviSL F σ hσ A
  have hk : g*l⁻¹ ∈ radical F σ hσ := by
    rw [←middleSU_ker]
    change middleSU F σ hσ (g*l⁻¹)=1
    apply (middleEquivSL F σ hσ).injective
    change middleSL F σ hσ (g*l⁻¹)=middleEquivSL F σ hσ 1
    rw [map_mul,map_inv,middleSL_leviSL,map_one,mul_inv_cancel]
  let k : R := ⟨g*l⁻¹,hk⟩
  have he : conjugate F σ hσ g r=k*conjugate F σ hσ l r*k⁻¹ := by
    apply Subtype.ext
    change g*r.val*g⁻¹=(g*l⁻¹)*(l*r.val*l⁻¹)*(g*l⁻¹)⁻¹
    group
  have hh := congrArg (horizontal F σ hσ) he
  rw [map_mul,map_mul,map_inv,mul_comm (horizontal F σ hσ k),mul_inv_cancel_right] at hh
  have hl := leviSL_conjugation_coordinates F σ hσ A (κ r)
  have hr : radicalOfCoordinates F σ hσ (κ r)=r :=
    (radicalCoordinatesEquiv F σ hσ).apply_symm_apply r
  change (κ (conjugate F σ hσ l (radicalOfCoordinates F σ hσ (κ r)))).x = _ ∧
    (κ (conjugate F σ hσ l (radicalOfCoordinates F σ hσ (κ r)))).y = _ ∧ _ at hl
  rw [hr] at hl
  exact ⟨(congrArg (fun z => z.toAdd.1) hh).trans hl.1,
    (congrArg (fun z => z.toAdd.2) hh).trans hl.2.1⟩

private def act (A : SpecialLinearGroup (Fin 2) K) (v : F × F) : F × F :=
  (((A.val 0 0 : F)*v.1+(A.val 0 1 : F)*v.2),
    ((A.val 1 0 : F)*v.1+(A.val 1 1 : F)*v.2))

private theorem act_add_inv (A : SpecialLinearGroup (Fin 2) K) (v : F × F) :
    act F σ A v+act F σ A⁻¹ v=(A.val.trace : K) • v := by
  apply Prod.ext <;>
    simp [act,Matrix.adjugate_fin_two,
      Matrix.trace,Matrix.diag,Fin.sum_univ_two,CharTwo.neg_eq,
      Subfield.smul_def,smul_eq_mul] <;> ring_nf <;>
    simp [show (2:F)=0 from CharP.cast_eq_zero F 2]

private def norm (v : F × F) : F := σ v.2*v.1+σ v.1*v.2

omit [CharP F 2] in
private theorem norm_smul (a : K) (v : F × F) :
    norm F σ (a • v)=(a:F)^2*norm F σ v := by
  change σ ((a:F)*v.2)*((a:F)*v.1)+σ ((a:F)*v.1)*((a:F)*v.2)=_
  have ha : σ (a:F)=a := a.property
  rw [map_mul,map_mul,ha]
  dsimp [norm]
  ring

private theorem horizontal_conjugate_eq (g : L) (r : R) :
    (horizontal F σ hσ (conjugate F σ hσ g r)).toAdd=
      act F σ (middleSL F σ hσ g) (horizontal F σ hσ r).toAdd :=
  Prod.ext (horizontal_conjugate F σ hσ g r).1 (horizontal_conjugate F σ hσ g r).2

private def horizontalEquiv (hnt : ∃ x, σ x ≠ x) :
    (R ⧸ center R) ≃* Multiplicative (F × F) :=
  (QuotientGroup.quotientMulEquivOfEq (horizontal_ker F σ hσ hnt).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (horizontal F σ hσ)
      (horizontal_surjective F σ hσ))

private theorem horizontalEquiv_mk (hnt : ∃ x, σ x ≠ x) (r : R) :
    horizontalEquiv F σ hσ hnt (QuotientGroup.mk r)=horizontal F σ hσ r := rfl

private def horizontalAut (hnt : ∃ x, σ x ≠ x) (b : MulAut R) :
    MulAut (Multiplicative (F × F)) :=
  MulAut.congr (horizontalEquiv F σ hσ hnt) (quotientAut (center R) b)

private theorem horizontalAut_apply (hnt : ∃ x, σ x ≠ x) (b : MulAut R) (r : R) :
    horizontalAut F σ hσ hnt b (horizontal F σ hσ r)=horizontal F σ hσ (b r) := by
  change horizontalEquiv F σ hσ hnt
    ((quotientAut (center R) b) ((horizontalEquiv F σ hσ hnt).symm (horizontal F σ hσ r)))=_
  let e := horizontalEquiv F σ hσ hnt
  have hpre : e.symm (horizontal F σ hσ r)=QuotientGroup.mk' (center R) r :=
    (congrArg e.symm (horizontalEquiv_mk F σ hσ hnt r).symm).trans (e.symm_apply_apply _)
  exact (congrArg (fun x => e ((quotientAut (center R) b) x)) hpre).trans
    ((congrArg e (quotientAut_apply_mk (center R) b r)).trans
      (horizontalEquiv_mk F σ hσ hnt (b r)))

private def normFixed (v : F × F) : K := ⟨norm F σ v, by
  change σ (σ v.2*v.1+σ v.1*v.2)=σ v.2*v.1+σ v.1*v.2
  rw [map_add,map_mul,map_mul,hσ,hσ]
  ring⟩

omit [CharP F 2] in
private theorem normFixed_smul (a : K) (v : F × F) :
    normFixed F σ hσ (a • v) = a^2 * normFixed F σ hσ v :=
  Subtype.ext (norm_smul F σ a v)

private theorem scalar_of_norm [Finite F] (hnt : ∃ x, σ x ≠ x)
    (E : (F × F) ≃+ (F × F)) (f : MulAut (Multiplicative K))
    (hlin : ∀ (a : K) (v : F × F), E (a • v)=a • E v)
    (hnorm : ∀ v : F × F,
      (f (Multiplicative.ofAdd (normFixed F σ hσ v))).toAdd = normFixed F σ hσ (E v)) :
    ∃ c : K, ∀ t : K, (f (Multiplicative.ofAdd t)).toAdd = c*t := by
  obtain ⟨x,hx⟩ := hnt
  let v : F × F := (1,x)
  have hn : normFixed F σ hσ v ≠ 0 := by
    intro he
    have hh := congrArg Subtype.val he
    change σ x*1+σ 1*x=0 at hh
    simp only [mul_one,map_one,one_mul,CharTwo.add_eq_zero] at hh
    exact hx hh
  have hscale (a : K) :
      (f (Multiplicative.ofAdd (a^2 * normFixed F σ hσ v))).toAdd =
        a^2 * (f (Multiplicative.ofAdd (normFixed F σ hσ v))).toAdd := by
    rw [←normFixed_smul,hnorm,hlin,normFixed_smul,hnorm]
  let c : K := (f (Multiplicative.ofAdd (normFixed F σ hσ v))).toAdd / normFixed F σ hσ v
  refine ⟨c,?_⟩
  intro t
  obtain ⟨a,ha⟩ := (frobeniusEquiv K 2).surjective (t / normFixed F σ hσ v)
  have ha2 : a^2=t / normFixed F σ hσ v := ha
  have hat : a^2*normFixed F σ hσ v=t := by rw [ha2,div_mul_cancel₀ _ hn]
  calc
    (f (Multiplicative.ofAdd t)).toAdd =
        a^2 * (f (Multiplicative.ofAdd (normFixed F σ hσ v))).toAdd := by
      rw [←hat, hscale]
    _ = c*t := by rw [ha2]; dsimp only [c]; ring

/-- The point quotient kernel has only scalar action on the central root. -/
theorem quotient_kernel_center_scalar [Finite F] (hnt : ∃ x, σ x ≠ x)
    (β : MulAut L) (b : MulAut R) (hb : ∀ r : R, (b r).val=β r.val)
    (hβ : ∀ g : L, middleSL F σ hσ (β g)=middleSL F σ hσ g) :
    ∃ c : K, ∀ z : center R,
      ((centerEquivFixedField F σ hσ hnt) ((MulAut.characteristic (center R) b) z)).toAdd =
        c * ((centerEquivFixedField F σ hσ hnt) z).toAdd := by
  let q := horizontal F σ hσ
  let k := horizontalAut F σ hσ hnt b
  let E : (F × F) ≃+ (F × F) :=
    { toFun v := (k (Multiplicative.ofAdd v)).toAdd
      invFun v := (k.symm (Multiplicative.ofAdd v)).toAdd
      left_inv v := congrArg Multiplicative.toAdd (k.symm_apply_apply (Multiplicative.ofAdd v))
      right_inv v := congrArg Multiplicative.toAdd (k.apply_symm_apply (Multiplicative.ofAdd v))
      map_add' v w := congrArg Multiplicative.toAdd (k.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  have hEq (r : R) : E (q r).toAdd=(q (b r)).toAdd :=
    congrArg Multiplicative.toAdd (horizontalAut_apply F σ hσ hnt b r)
  have hconj (g : L) (r : R) :
      b (conjugate F σ hσ g r)=conjugate F σ hσ (β g) (b r) := by
    apply Subtype.ext
    rw [hb]
    change β (g*r.val*g⁻¹)=β g*(b r).val*(β g)⁻¹
    rw [map_mul,map_mul,map_inv,hb]
  have hact (A : SpecialLinearGroup (Fin 2) K) (v : F × F) :
      E (act F σ A v)=act F σ A (E v) := by
    obtain ⟨r,hr⟩ := horizontal_surjective F σ hσ (Multiplicative.ofAdd v)
    have hv : (q r).toAdd=v := congrArg Multiplicative.toAdd hr
    rw [←hv,←middleSL_leviSL F σ hσ A,←horizontal_conjugate_eq,hEq,hconj,
      horizontal_conjugate_eq,hβ,middleSL_leviSL,hEq]
  have hlin (a : K) (v : F × F) : E (a • v)=a • E v := by
    let A : SpecialLinearGroup (Fin 2) K := ⟨!![a,1;1,0],by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩
    have htr : A.val.trace=a := by simp [A,Matrix.trace,Matrix.diag,Fin.sum_univ_two]
    calc
      E (a • v) = E (act F σ A v+act F σ A⁻¹ v) := by rw [act_add_inv,htr]
      _ = act F σ A (E v)+act F σ A⁻¹ (E v) := by rw [map_add,hact,hact]
      _ = a • E v := by rw [act_add_inv,htr]
  let e := centerEquivFixedField F σ hσ hnt
  let f := MulAut.congr e (MulAut.characteristic (center R) b)
  have hnorm (v : F × F) :
      (f (Multiplicative.ofAdd (normFixed F σ hσ v))).toAdd = normFixed F σ hσ (E v) := by
    obtain ⟨r,hr⟩ := horizontal_surjective F σ hσ (Multiplicative.ofAdd v)
    have hv : (q r).toAdd=v := congrArg Multiplicative.toAdd hr
    rw [←hv,hEq]
    let z : center R := ⟨r^2,radical_square_mem_center F σ hσ r⟩
    have hz : e z=Multiplicative.ofAdd (normFixed F σ hσ (q r).toAdd) := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact coord_square F σ hσ r
    rw [←hz]
    change (e ((MulAut.characteristic (center R) b) (e.symm (e z)))).toAdd = _
    rw [e.symm_apply_apply]
    apply Subtype.ext
    change (κ (b (r^2))).z = _
    rw [map_pow,coord_square]
    rfl
  obtain ⟨c,hc⟩ := scalar_of_norm F σ hσ hnt E f hlin hnorm
  refine ⟨c, fun z => ?_⟩
  have hfz : f (e z) = e ((MulAut.characteristic (center R) b) z) :=
    congrArg (fun w => e ((MulAut.characteristic (center R) b) w)) (e.symm_apply_apply z)
  exact (congrArg Multiplicative.toAdd hfz).symm.trans (hc (e z).toAdd)


private theorem scalar_twoPower_fixed {kF : Type*} [Field kF] [CharP kF 2]
    (f : MulAut (Multiplicative kF)) (c : kF)
    (hf : ∀ t : kF, (f (Multiplicative.ofAdd t)).toAdd=c*t)
    (k : ℕ) (hfk : f^(2^k)=1) : c=1 := by
  have hpow (j : ℕ) (t : kF) : ((f^j) (Multiplicative.ofAdd t)).toAdd=c^j*t := by
    induction j with
    | zero => simp
    | succ j hj =>
      rw [pow_succ',MulAut.mul_apply]
      change (f (Multiplicative.ofAdd (((f^j) (Multiplicative.ofAdd t)).toAdd))).toAdd = _
      rw [hf,hj,pow_succ']
      exact mul_assoc _ _ _ |>.symm
  have hcPow : c^(2^k)=1 := by
    have hh := hpow (2^k) 1
    rw [hfk,MulAut.one_apply,mul_one] at hh
    exact hh.symm
  simpa only [mul_one,pow_one] using
    (ExpChar.pow_prime_pow_mul_eq_one_iff 2 k 1 c).mp (by simpa only [mul_one] using hcPow)

/-- A two-power-order point-quotient kernel fixes the entire central root. -/
theorem quotient_kernel_center_fixed [Finite F] (hnt : ∃ x, σ x ≠ x)
    (β : MulAut L) (b : MulAut R) (hb : ∀ r : R, (b r).val=β r.val)
    (hβ : ∀ g : L, middleSL F σ hσ (β g)=middleSL F σ hσ g)
    (k : ℕ) (hk : b^(2^k)=1) : ∀ z ∈ center R, b z=z := by
  obtain ⟨c,hc⟩ := quotient_kernel_center_scalar F σ hσ hnt β b hb hβ
  let e := centerEquivFixedField F σ hσ hnt
  let f := MulAut.congr e (MulAut.characteristic (center R) b)
  have hf (t : K) : (f (Multiplicative.ofAdd t)).toAdd=c*t := by
    change (e ((MulAut.characteristic (center R) b) (e.symm (Multiplicative.ofAdd t)))).toAdd = c*t
    have hh := hc (e.symm (Multiplicative.ofAdd t))
    change _ = c * (e (e.symm (Multiplicative.ofAdd t))).toAdd at hh
    rw [e.apply_symm_apply] at hh
    exact hh
  have hfk : f^(2^k)=1 := by
    have hb' : (MulAut.characteristic (center R) b)^(2^k)=1 := by
      rw [← map_pow, hk, map_one]
    calc
      f^(2^k) = MulAut.congr e ((MulAut.characteristic (center R) b)^(2^k)) :=
        (map_pow (MulAut.congr e) _ _).symm
      _ = 1 := (congrArg (MulAut.congr e) hb').trans (map_one (MulAut.congr e))
  have hc1 := scalar_twoPower_fixed f c hf k hfk
  intro z hz
  have hh : e ((MulAut.characteristic (center R) b) ⟨z,hz⟩) = e ⟨z,hz⟩ := by
    apply Multiplicative.toAdd.injective
    simpa only [hc1,one_mul] using hc ⟨z,hz⟩
  exact congrArg Subtype.val (e.injective hh)


private theorem center_local_to_radical [Finite F] (x : L) (hx : x ∈ center L) :
    ∃ r : R, r.val = x ∧ r ∈ center R := by
  have hxr : x.val ∈ UnitaryFourConverse.PointParabolic.ambientRadical F σ hσ := by
    apply UnitaryFourConverse.PointParabolic.centralizer_ambientRadical_le F σ hσ
    rintro _ ⟨r,hr,rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hx r)
  obtain ⟨r,hr,he⟩ := hxr
  have hrx : r = x := Subtype.ext he
  refine ⟨⟨r,hr⟩,hrx,mem_center_iff.mpr fun a => ?_⟩
  apply Subtype.ext
  change a.val * r = r * a.val
  rw [hrx]
  exact mem_center_iff.mp hx a.val

/-- The literal quotient kernel fixes the center of the point residual,
transported through any specified residual coordinates. -/
theorem residual_center_fixed [Finite F] (hnt : ∃ x, σ x ≠ x)
    (hcore : radical F σ hσ = pCore 2 L)
    {N : Type*} [Group N] (e : N ≃* L) (a : MulAut N)
    (ha : quotientAut (pCore 2 N) a=1) (k : ℕ) (hk : a^(2^k)=1) :
    ∀ z ∈ center N, a z=z := by
  let β := MulAut.congr e a
  let c : R ≃* pCore 2 L := MulEquiv.subgroupCongr hcore
  let b : MulAut R := MulAut.congr c.symm (MulAut.characteristic (pCore 2 L) β)
  have hb (r : R) : (b r).val=β r.val := rfl
  have hβ (g : L) : middleSL F σ hσ (β g)=middleSL F σ hσ g := by
    let q := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      ((QuotientGroup.quotientMulEquivOfEq hcore.symm).trans (quotientEquivSL F σ hσ))
    have hh := congrArg q (DFunLike.congr_fun ha (QuotientGroup.mk' (pCore 2 N) (e.symm g)))
    rw [quotientAut_apply_mk] at hh
    change middleSL F σ hσ (e (a (e.symm g))) = middleSL F σ hσ (e (e.symm g)) at hh
    rwa [e.apply_symm_apply] at hh
  have hβk : β^(2^k)=1 := by
    rw [←map_pow,hk,map_one]
  have hbk : b^(2^k)=1 := by
    have hc' : (MulAut.characteristic (pCore 2 L) β)^(2^k)=1 := by
      rw [←map_pow,hβk,map_one]
    calc
      b^(2^k) = MulAut.congr c.symm ((MulAut.characteristic (pCore 2 L) β)^(2^k)) :=
        (map_pow (MulAut.congr c.symm) _ _).symm
      _ = 1 := (congrArg (MulAut.congr c.symm) hc').trans (map_one (MulAut.congr c.symm))
  intro z hz
  have hez : e z ∈ center L := (centerCongr e ⟨z,hz⟩).property
  obtain ⟨r,hr,hrc⟩ := center_local_to_radical F σ hσ (e z) hez
  have hbr := quotient_kernel_center_fixed F σ hσ hnt β b hb hβ k hbk r hrc
  have hh := congrArg Subtype.val hbr
  rw [hb,hr] at hh
  apply e.injective
  change e (a (e.symm (e z)))=e z at hh
  simpa only [e.symm_apply_apply] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour.CenterKernel

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
namespace Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (e : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
include d h hTH hp e

/-- The original enlarged right core fixes the whole center of the selected
point residual, before the outer degree is bounded. -/
theorem original_unitaryFour_core_centralizes_center :
    (R ⊔ sourceS L H).pCoreIn 2 ≤ centralizer ((center R).map R.subtype : Set G) := by
  obtain ⟨_,_,⟨b₀⟩,_⟩ := d.original_unitaryFour_factors h hTH hp m hm point e
  let b := b₀.trans (PointLocal.localEquiv m hm).symm
  let M := R ⊔ sourceS L H
  let f : M →* MulAut R := R.normalizerMonoidHom.comp
    (inclusion (sup_le R.le_normalizer d.S_normalizes_right))
  rintro x ⟨g,hg,rfl⟩ z ⟨z,hz,rfl⟩
  have hq : quotientAut (pCore 2 R) (f g)=1 :=
    pCore_le_pCoreJoinAction_kernel 2 d.S_normalizes_right hg
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := M)).exists_pow_pow_eq_one ⟨g,hg⟩
  have hgk : g^(2^k)=1 := congrArg Subtype.val hk
  have hfk : (f g)^(2^k)=1 := by rw [←map_pow,hgk,map_one]
  have hfix := OriginalUnitaryFour.CenterKernel.residual_center_fixed
    (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
    (PointLocal.fieldConj_nontrivial m hm) (PointLocal.radical_eq_twoCore m hm)
    b (f g) hq k hfk z hz
  have hh := congrArg Subtype.val hfix
  change g.val*z.val*g.val⁻¹=z.val at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Normalized right-Borel factorization makes every original S element
fix the same entire point-residual center, including the possible graph actor. -/
theorem original_unitaryFour_source_centralizes_center :
    sourceS L H ≤ centralizer ((center R).map R.subtype : Set G) := by
  rw [d.original_unitaryFour_source_factorization h hTH hp m hm point e]
  apply sup_le (d.original_unitaryFour_core_centralizes_center h hTH hp m hm point e)
  intro x hx z hz
  have hxR : x ∈ R :=
    ((d.original_unitaryFour_intersections h hTH hp m hm point e).le
      (d.left_intersection.ge hx)).2
  obtain ⟨z,hz,rfl⟩ := hz
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hxR⟩).symm

end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
