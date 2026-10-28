module
public import Theory.Representation.BinaryCubicPairs.Normalization
public import Theory.Representation.BinaryCubicPairs.FixedCount
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorAction

/-!
# Singular vectors fixed by independent commuting cubics

A cubic with natural fixed dimension two can be put in the literal rank-two
normal form by the existing verified normalization. Its centralizer has six
binary coordinates. A finite calculation proves that a singular exterior
vector in its moving space cannot be fixed by an independent commuting cubic.
The result is transported back through the genuine compound matrices, with
the right-row inverse convention used by endpoint induction.
-/
public noncomputable section
open Matrix Atlas.Order20160A8.Bivectors
open scoped MatrixGroups
namespace Representation.BinaryParabolicExteriorSquare.SingularCubicObstruction
private def A : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0,1,0,0;1,1,0,0;0,0,1,0;0,0,0,1]
private def block (t : Fin 6 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![t 0,t 1,0,0;t 1,t 0+t 1,0,0;0,0,t 2,t 3;0,0,t 4,t 5]
private theorem shape (m : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hc : A*m=m*A) :
    m=block ![m 0 0,m 0 1,m 2 2,m 2 3,m 3 2,m 3 3] := by
  have h (i j : Fin 4) := congrArg (fun n : Matrix (Fin 4) (Fin 4) (ZMod 2) => n i j) hc
  simp only [A, Matrix.mul_apply, Fin.sum_univ_succ] at h
  simp at h
  have h02 : m 0 2=0 := by simpa using h 1 2
  have h03 : m 0 3=0 := by simpa using h 1 3
  have h12 : m 1 2=0 := by simpa [h02] using h 0 2
  have h13 : m 1 3=0 := by simpa [h03] using h 0 3
  have h20 : m 2 0=0 := by simpa using (h 2 1).symm
  have h30 : m 3 0=0 := by simpa using (h 3 1).symm
  have h21 : m 2 1=0 := by simpa [h20] using (h 2 0).symm
  have h31 : m 3 1=0 := by simpa [h30] using (h 3 0).symm
  have h10 : m 1 0=m 0 1 := by simpa using h 0 0
  have h11 : m 1 1=m 0 0+m 0 1 := by simpa using h 0 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block,h02,h03,h12,h13,h20,h21,h30,h31,h10,h11]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
private theorem finite_check : ∀ (t : Fin 6 → ZMod 2),
    block t * block t * block t=1 → block t≠1 → block t≠A → block t≠A*A →
    ∀ x : Fin 6 → ZMod 2, pfaffian x=0 →
      x + x ᵥ* compound A + x ᵥ* compound (A*A)=0 →
      x ᵥ* compound (block t)=x → x=0 := by
  decide +kernel

private def standard : SL(4,ZMod 2) := ⟨A,by decide⟩

private theorem standard_normalization (a : SL(4,ZMod 2)) (ha : a^3=1)
    (hf : Module.finrank (ZMod 2) (BinaryCubicPairs.fixedKernel a.val)=2) :
    ∃ g : SL(4,ZMod 2), MulAut.conj g a=standard := by
  let m := BinaryCubicPairs.Packed.pack a.val
  have hm : BinaryCubicPairs.Packed.toMat m=a.val := BinaryCubicPairs.Packed.toMat_pack _
  have hp : BinaryCubicPairs.Packed.mm (BinaryCubicPairs.Packed.mm m m) m=
      BinaryCubicPairs.Packed.ident := by
    apply BinaryCubicPairs.Packed.toMat_injective
    rw [BinaryCubicPairs.Packed.toMat_mm,BinaryCubicPairs.Packed.toMat_mm,hm]
    have he := congrArg (fun b : SL(4,ZMod 2) => b.val) ha
    simpa only [pow_succ,pow_zero,one_mul,SpecialLinearGroup.coe_mul,SpecialLinearGroup.coe_one,BinaryCubicPairs.Packed.ident,
      BinaryCubicPairs.Packed.toMat_one] using he
  have hc : BinaryCubicPairs.Packed.cubicB m=true := by
    have hh := BinaryCubicPairs.fixed_count_four m (by rw [hm]; exact hf)
    simp only [BinaryCubicPairs.Packed.cubicB,hp,hh,beq_self_eq_true,Bool.and_self]
  obtain ⟨g₀,h₀,hgh,hhg,hconj⟩ := BinaryCubicPairs.Packed.exists_normalization m hc
  let g := BinaryCubicPairs.Packed.toMat g₀
  let h := BinaryCubicPairs.Packed.toMat h₀
  have hgh' : g*h=1 := by
    simpa only [BinaryCubicPairs.Packed.toMat_mm,BinaryCubicPairs.Packed.ident,
      BinaryCubicPairs.Packed.toMat_one] using congrArg BinaryCubicPairs.Packed.toMat hgh
  have hd : g.det=1 := by
    have he : g.det*h.det=1 := by rw [←Matrix.det_mul,hgh',Matrix.det_one]
    exact (by decide : ∀ x y : ZMod 2, x*y=1 → x=1) _ _ he
  let s : SL(4,ZMod 2) := ⟨g,hd⟩
  have hi : s⁻¹.val=h := by
    have hs : s⁻¹.val*g=1 := congrArg (fun t : SL(4,ZMod 2) => t.val) (inv_mul_cancel s)
    calc
      s⁻¹.val = s⁻¹.val*(g*h) := by rw [hgh',mul_one]
      _ = h := by rw [←mul_assoc,hs,one_mul]
  refine ⟨s,?_⟩
  apply Subtype.ext
  change g*a.val*s⁻¹.val=A
  rw [hi]
  have he := congrArg BinaryCubicPairs.Packed.toMat hconj
  have hs : BinaryCubicPairs.Packed.toMat BinaryCubicPairs.Packed.cubic=A := by decide +kernel
  simpa only [BinaryCubicPairs.Packed.toMat_mm,hm,hs] using he

private theorem compound_one : compound (1 : Matrix (Fin 4) (Fin 4) (ZMod 2))=1 := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_one]
  exact exteriorMap_one (F := ZMod 2)

private theorem compound_mul (g h : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    compound (g*h)=compound g*compound h := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_mul]
  exact exteriorMap_mul g h

private theorem compound_transpose (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    compound g.transpose=(compound g).transpose := by
  ext i j
  simp only [compound,Matrix.transpose_apply]
  ring

private def row (g : SL(4,ZMod 2)) : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  (compound g.val).vecMulLinear

private theorem row_mul (g h : SL(4,ZMod 2)) (x : Fin 6 → ZMod 2) :
    row h (row g x)=row (g*h) x := by
  change (x ᵥ* compound g.val) ᵥ* compound h.val=x ᵥ* compound (g.val*h.val)
  rw [Matrix.vecMul_vecMul,compound_mul]

private theorem row_one (x : Fin 6 → ZMod 2) : row 1 x=x := by
  change x ᵥ* compound 1=x
  rw [compound_one,Matrix.vecMul_one]

private theorem row_injective (g : SL(4,ZMod 2)) : Function.Injective (row g) := by
  intro x y he
  have hh := congrArg (row g⁻¹) he
  simpa only [row_mul,mul_inv_cancel,row_one] using hh

private theorem row_conj (g a : SL(4,ZMod 2)) (x : Fin 6 → ZMod 2) :
    row (MulAut.conj g a) (row g⁻¹ x)=row g⁻¹ (row a x) := by
  rw [row_mul,row_mul]
  have he : g⁻¹ * MulAut.conj g a=a*g⁻¹ := by simp [MulAut.conj_apply,mul_assoc]
  rw [he]

private theorem pfaffian_row (g : SL(4,ZMod 2)) (x : Fin 6 → ZMod 2) :
    pfaffian (row g x)=pfaffian x := by
  change pfaffian (x ᵥ* compound g.val)=pfaffian x
  rw [←Matrix.mulVec_transpose,←compound_transpose]
  exact (pfaffian_exteriorMap g.val.transpose x).trans (by rw [Matrix.det_transpose,g.property,one_mul])

private theorem normalized_obstruction (v : SL(4,ZMod 2)) (hv : v^3=1)
    (hc : Commute standard v) (hv0 : v≠1) (hv1 : v≠standard) (hv2 : v≠standard^2)
    (x : Fin 6 → ZMod 2) (hx : pfaffian x=0)
    (hm : x+row standard x+row (standard^2) x=0) (hf : row v x=x) : x=0 := by
  let t := ![v.val 0 0,v.val 0 1,v.val 2 2,v.val 2 3,v.val 3 2,v.val 3 3]
  have hs : v.val=block t := shape v.val (congrArg (fun g : SL(4,ZMod 2) => g.val) hc.eq)
  have hs2 : (standard^2).val=A*A := by rw [pow_two,SpecialLinearGroup.coe_mul]; rfl
  apply finite_check t
  · rw [←hs]
    exact congrArg (fun g : SL(4,ZMod 2) => g.val) (by simpa only [pow_succ,pow_zero,one_mul] using hv)
  · intro he
    exact hv0 (Subtype.ext (hs.trans he))
  · intro he
    exact hv1 (Subtype.ext (hs.trans he))
  · intro he
    exact hv2 (Subtype.ext ((hs.trans he).trans hs2.symm))
  · exact hx
  · change x+x ᵥ* compound standard.val+x ᵥ* compound (standard^2).val=0 at hm
    rw [hs2] at hm
    exact hm
  · rwa [←hs]

private theorem direct_obstruction (a v : SL(4,ZMod 2)) (ha : a^3=1) (hv : v^3=1)
    (hafix : Module.finrank (ZMod 2) (BinaryCubicPairs.fixedKernel a.val)=2)
    (hc : Commute a v) (hv0 : v≠1) (hv1 : v≠a) (hv2 : v≠a^2)
    (x : Fin 6 → ZMod 2) (hx : pfaffian x=0)
    (hm : x+row a x+row (a^2) x=0) (hf : row v x=x) : x=0 := by
  obtain ⟨g,hg⟩ := standard_normalization a ha hafix
  let b := MulAut.conj g v
  let y := row g⁻¹ x
  have hbp : b^3=1 := by rw [←map_pow,hv,map_one]
  have hbc : Commute standard b := hg ▸ hc.map (MulAut.conj g).toMonoidHom
  have hb0 : b≠1 := by
    intro h
    apply hv0
    exact (MulAut.conj g).injective (h.trans (map_one _).symm)
  have hb1 : b≠standard := by
    intro h
    exact hv1 ((MulAut.conj g).injective (h.trans hg.symm))
  have hb2 : b≠standard^2 := by
    intro h
    apply hv2
    apply (MulAut.conj g).injective
    simpa only [map_pow,hg] using h
  have hy : pfaffian y=0 := (pfaffian_row g⁻¹ x).trans hx
  have hym : y+row standard y+row (standard^2) y=0 := by
    rw [←hg,←map_pow,row_conj,row_conj]
    change row g⁻¹ x+row g⁻¹ (row a x)+row g⁻¹ (row (a^2) x)=0
    rw [←map_add,←map_add,hm,map_zero]
  have hyf : row b y=y := by
    rw [row_conj,hf]
  have hz := normalized_obstruction b hbp hbc hb0 hb1 hb2 y hy hym hyf
  exact row_injective g⁻¹ (hz.trans (map_zero _).symm)

/-- In the exact right-row inverse exterior action, an independent commuting
cubic fixes no nonzero singular vector in the rank-two cubic's moving space,
expressed by its trace-zero equation. -/
theorem singular_eq_zero_of_commuting_cubic_trace
    (a v : SL(4,ZMod 2)) (ha : a^3=1) (hv : v^3=1)
    (hafix : Module.finrank (ZMod 2) (BinaryCubicPairs.fixedKernel a.val)=2)
    (hc : Commute a v) (hv0 : v≠1) (hv1 : v≠a) (hv2 : v≠a^2)
    (x : Fin 6 → ZMod 2) (hx : pfaffian x=0)
    (hm : x+x ᵥ* compound a⁻¹.val+x ᵥ* compound (a^2)⁻¹.val=0)
    (hf : x ᵥ* compound v⁻¹.val=x) : x=0 := by
  have ha2 : a^2=a⁻¹ := by
    apply mul_right_cancel (b := a)
    simpa only [←pow_succ,inv_mul_cancel] using ha
  have ha22 : (a^2)⁻¹=a := by rw [ha2,inv_inv]
  have hm' : x+row a x+row (a^2) x=0 := by
    change x+row a⁻¹ x+row (a^2)⁻¹ x=0 at hm
    rw [←ha2,ha22] at hm
    simpa only [add_assoc,add_comm (row a x) (row (a^2) x)] using hm
  have hf' : row v x=x := by
    have hh := congrArg (row v) hf
    change row v (row v⁻¹ x)=row v x at hh
    rw [row_mul,inv_mul_cancel,row_one] at hh
    exact hh.symm
  exact direct_obstruction a v ha hv hafix hc hv0 hv1 hv2 x hx hm' hf'

/-- The same obstruction with literal membership in the displacement range
of the original right-row inverse actor, rather than a trace equation. -/
theorem singular_eq_zero_of_commuting_cubic_moving
    (a v : SL(4,ZMod 2)) (ha : a^3=1) (hv : v^3=1)
    (hafix : Module.finrank (ZMod 2) (BinaryCubicPairs.fixedKernel a.val)=2)
    (hc : Commute a v) (hv0 : v≠1) (hv1 : v≠a) (hv2 : v≠a^2)
    (x : Fin 6 → ZMod 2) (hx : pfaffian x=0)
    (hm : x ∈ ((compound a⁻¹.val).vecMulLinear-LinearMap.id).range)
    (hf : x ᵥ* compound v⁻¹.val=x) : x=0 := by
  apply singular_eq_zero_of_commuting_cubic_trace a v ha hv hafix hc hv0 hv1 hv2 x hx _ hf
  obtain ⟨y,hy⟩ := hm
  change row a⁻¹ y-y=x at hy
  rw [←hy]
  change (row a⁻¹ y-y)+row a⁻¹ (row a⁻¹ y-y)+row (a^2)⁻¹ (row a⁻¹ y-y)=0
  rw [map_sub,map_sub,row_mul,row_mul]
  have hs : a⁻¹*a⁻¹=(a^2)⁻¹ := by rw [pow_two,_root_.mul_inv_rev]
  have ht : a⁻¹*(a^2)⁻¹=1 := by rw [←_root_.mul_inv_rev,←pow_succ,ha,inv_one]
  rw [hs,ht,row_one]
  abel

end Representation.BinaryParabolicExteriorSquare.SingularCubicObstruction
