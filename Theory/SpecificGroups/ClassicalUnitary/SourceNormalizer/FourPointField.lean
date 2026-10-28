module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointRadicalSpecial
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# The field coefficient detected by the unitary point center

The Heisenberg radical modulo its center has the literal horizontal
coordinates F², acted on naturally by SL₂ of the stored fixed field K.
For A in SL₂(K), A+A⁻¹=tr(A)I. This identity makes every compatible additive
intertwiner semilinear with the same field coefficient as the quotient
actor. Squares in the radical give a nonzero K-valued quadratic form.
An automorphism fixing the center preserves that form, so its coefficient
fixes every element of K and its quotient action is inner.

The prepared ordinary U₄ consumer uses the actual radical restriction and
quotient map. This detects right-quotient field actors without identifying
an arbitrary involution with a pure graph automorphism.
Source: Aschbacher–Smith F.4.29(2,7), F.4.37–38, printed pp.289–294,
with the point radical of F.1.12(I)(6), pp.263–264, refs/quasithin.pdf.
-/

open Subgroup Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourPointField
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
    simp [act,SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.trace,Matrix.diag,Fin.sum_univ_two,CharTwo.neg_eq,
      Subfield.smul_def,smul_eq_mul] <;> ring_nf <;>
    simp [show (2:F)=0 from CharP.cast_eq_zero F 2]

omit [CharP F 2] in
private theorem trace_inner_field (g A : SpecialLinearGroup (Fin 2) K) (τ : K ≃+* K) :
    (g*Theory.PSL2.sl2FieldAut τ A*g⁻¹).val.trace=τ A.val.trace := by
  let c : SpecialLinearGroup (Fin 2) K →* Matrix (Fin 2) (Fin 2) K := SpecialLinearGroup.coeMonoidHom
  change Matrix.trace (c (g*Theory.PSL2.sl2FieldAut τ A*g⁻¹))=_
  rw [map_mul,map_mul,Matrix.trace_mul_cycle,←map_mul,inv_mul_cancel,map_one,one_mul]
  simp only [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  change (τ (A.val 0 0)+τ (A.val 1 1))=τ (A.val 0 0+A.val 1 1)
  rw [map_add]

private def norm (v : F × F) : F := σ v.2*v.1+σ v.1*v.2

omit [CharP F 2] in
private theorem norm_smul (a : K) (v : F × F) :
    norm F σ (a • v)=(a:F)^2*norm F σ v := by
  change σ ((a:F)*v.2)*((a:F)*v.1)+σ ((a:F)*v.1)*((a:F)*v.2)=_
  have ha : σ (a:F)=a := a.property
  rw [map_mul,map_mul,ha]
  dsimp [norm]
  ring

/-- The Heisenberg square form detects the entire coefficient of a
compatible automorphism of its fixed-field SL₂ quotient. -/
private theorem inner_of_square_preserving [Finite F] (hnt : ∃ x, σ x ≠ x)
    (α : MulAut (SpecialLinearGroup (Fin 2) K)) (E : (F × F) ≃+ (F × F))
    (hE : ∀ A v, E (act F σ A v)=act F σ (α A) (E v))
    (hN : ∀ v, norm F σ (E v)=norm F σ v) :
    ∃ g, α=MulAut.conj g := by
  obtain ⟨g,τ,hα⟩ := Theory.PSL2.sl2_semilinear_coverage α
  have hsemi (a : K) (v : F × F) : E (a • v)=τ a • E v := by
    let A : SpecialLinearGroup (Fin 2) K := ⟨!![a,1;1,0],by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩
    have htr : A.val.trace=a := by simp [A,Matrix.trace,Matrix.diag,Fin.sum_univ_two]
    have htr' : (α A).val.trace=τ a := by
      rw [hα]
      exact (trace_inner_field F σ g A τ).trans (congrArg τ htr)
    calc
      E (a • v) = E (act F σ A v+act F σ A⁻¹ v) := by rw [act_add_inv,htr]
      _ = act F σ (α A) (E v)+act F σ (α A)⁻¹ (E v) := by rw [map_add,hE,hE,map_inv]
      _ = τ a • E v := by rw [act_add_inv,htr']
  obtain ⟨x,hx⟩ := hnt
  let v : F × F := (1,x)
  have hn : norm F σ v ≠ 0 := by
    dsimp [norm,v]
    simpa only [mul_one,map_one,one_mul,CharTwo.add_eq_zero] using hx
  have hτ (a : K) : τ a=a := by
    have hh := hN (a • v)
    rw [hsemi,norm_smul,norm_smul,hN] at hh
    have hs : (τ a : F)^2=(a:F)^2 := (mul_right_cancel₀ hn hh)
    apply Subtype.ext
    exact frobenius_inj F 2 hs
  have he : τ=RingEquiv.refl K := RingEquiv.ext hτ
  refine ⟨g,?_⟩
  rw [hα,he]
  ext A i j
  rfl


private theorem horizontal_conjugate_eq (g : L) (r : R) :
    (horizontal F σ hσ (conjugate F σ hσ g r)).toAdd=
      act F σ (middleSL F σ hσ g) (horizontal F σ hσ r).toAdd :=
  Prod.ext (horizontal_conjugate F σ hσ g r).1 (horizontal_conjugate F σ hσ g r).2

private theorem central_mem_local_center (hnt : ∃ x, σ x ≠ x) (r : R)
    (hr : r ∈ center R) : r.val ∈ center L := by
  obtain ⟨hx,hy⟩ := (mem_center_radical_iff F σ hσ hnt r).mp hr
  apply mem_center_iff.mpr
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have hmat : r.val.val.val.val=radicalMatrix F σ (κ r) :=
    congrArg (fun x : R => x.val.val.val.val)
      ((radicalCoordinatesEquiv F σ hσ).apply_symm_apply r).symm
  have hg := (mem_localSU F _ g.val).mp g.property
  have hl := last_row F σ hσ g.val g.property
  change g.val.val.val*r.val.val.val.val=r.val.val.val.val*g.val.val.val
  rw [hmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalMatrix,hx,hy,Matrix.mul_apply,Fin.sum_univ_succ,
      hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,hl.2.1,hl.2.2.1,hl.2.2.2,add_comm]

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

/-- A genuine automorphism of the point residual fixing its center induces
an inner automorphism on its actual SL₂ quotient. The radical restriction
and quotient action retain their literal commuting maps. -/
theorem inner_quotient_of_center_fixed [Finite F] (hnt : ∃ x, σ x ≠ x)
    (β : MulAut L) (b : MulAut R) (hb : ∀ r : R, (b r).val=β r.val)
    (α : MulAut (SpecialLinearGroup (Fin 2) K))
    (hα : ∀ g : L, middleSL F σ hσ (β g)=α (middleSL F σ hσ g))
    (hfix : ∀ z ∈ center L, β z=z) :
    ∃ g, α=MulAut.conj g := by
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
  apply inner_of_square_preserving F σ hnt α E
  · intro A v
    obtain ⟨r,hr⟩ := horizontal_surjective F σ hσ (Multiplicative.ofAdd v)
    have hv : (q r).toAdd=v := congrArg Multiplicative.toAdd hr
    rw [←hv,←middleSL_leviSL F σ hσ A,←horizontal_conjugate_eq,hEq,hconj,
      horizontal_conjugate_eq,hα,middleSL_leviSL,hEq]
  · intro v
    obtain ⟨r,hr⟩ := horizontal_surjective F σ hσ (Multiplicative.ofAdd v)
    have hv : (q r).toAdd=v := congrArg Multiplicative.toAdd hr
    rw [←hv,hEq]
    have hs : (b r)^2=r^2 := by
      rw [←map_pow]
      apply Subtype.ext
      rw [hb]
      exact hfix _ (central_mem_local_center F σ hσ hnt _ (radical_square_mem_center F σ hσ r))
    have hz := congrArg (fun s : R => (κ s).z) hs
    rw [coord_square,coord_square] at hz
    exact hz

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourPointField
