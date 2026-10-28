module
public import Theory.Mathieu.M12.ExceptionalParabolics.SourceRecognitionCoreAlgebra
public import Theory.Mathieu.M12.ExceptionalParabolics.SourceRecognitionCoreExtension

/-!
# Correction of the source opposite-endpoint lifts

The source supplies a cubic actor cycling a marked core triple and an
order-four lift fixing its first generator. The action of the lift on the
central four leaves two possible shifts on the remaining generators; an
inner-action calculation excludes the other two shifts. Multiplying the lift
by the first generator removes that defect. Its product with the cubic actor
then squares into a fixed line of the central four; one central correction
removes this final defect. Both corrections preserve the generated group.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the
split-extension calculation in the last paragraph of (6.12), printed p.406.
-/

public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- The literal source lift data, prior to its two central corrections. -/
structure CoreExtensionRawRelations (x y z a b T C : G) : Prop extends
    ThreeInvolutionFourCommutators.Relations x y z a b where
  T_sq : T^2=a*b
  C_cube : C^3=1
  Tx : T*x*T⁻¹=x
  Cx : C*x*C⁻¹=y
  Cy : C*y*C⁻¹=z
  Cz : C*z*C⁻¹=x
  Ta : T*a*T⁻¹=b
  Tb : T*b*T⁻¹=a
  Ty_mem : T*y*T⁻¹ ∈ closure ({x,y,z}:Set G)
  TC_sq_mem : (T*C)^2 ∈ closure ({x,y,z}:Set G)

private theorem conj_product (u v w : G) :
    MulAut.conj (u*v) w = MulAut.conj u (MulAut.conj v w) := by
  simp only [MulAut.conj_apply,mul_inv_rev,mul_assoc]

private theorem conj_square (u w : G) :
    MulAut.conj (u^2) w = MulAut.conj u (MulAut.conj u w) := by
  rw [pow_two,conj_product]

private theorem square_product (u v : G) : (u*v)^2=u*MulAut.conj v u*v^2 := by
  simp only [pow_two,MulAut.conj_apply,mul_assoc,inv_mul_cancel_left]

variable {x y z a b T C : G}

private theorem raw_central_actions (r : CoreExtensionRawRelations x y z a b T C) :
    MulAut.conj C a=a*b ∧ MulAut.conj C b=a := by
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two,r.a_order] using pow_orderOf_eq_one a)
  constructor
  · calc
      MulAut.conj C a = MulAut.conj C ⁅x,y⁆ := congrArg (MulAut.conj C) r.xy.symm
      _ = ⁅MulAut.conj C x,MulAut.conj C y⁆ := map_commutatorElement _ _ _
      _ = a*b := by change ⁅C*x*C⁻¹,C*y*C⁻¹⁆=a*b; rw [r.Cx,r.Cy,r.yz]
  · rw [← r.xz,map_commutatorElement]
    change ⁅C*x*C⁻¹,C*z*C⁻¹⁆=a
    rw [r.Cx,r.Cz,← commutatorElement_inv,r.xy,hai]

/-- Correcting the lift preserves its coset modulo the generated core. -/
theorem CoreExtensionRawRelations.normalize
    (r : CoreExtensionRawRelations x y z a b T C) :
    ∃ U : G, CoreExtensionRelations x y z a b U C ∧
      ∃ q ∈ closure ({x,y,z}:Set G), U=q*T := by
  let Q := closure ({x,y,z}:Set G)
  have hx : x ∈ Q := subset_closure (by simp)
  have hy : y ∈ Q := subset_closure (by simp)
  have hz : z ∈ Q := subset_closure (by simp)
  have ha : a ∈ Q := r.xy ▸ Q.mul_mem
    (Q.mul_mem (Q.mul_mem hx hy) (Q.inv_mem hx)) (Q.inv_mem hy)
  have hb : b ∈ Q := r.xz ▸ Q.mul_mem
    (Q.mul_mem (Q.mul_mem hx hz) (Q.inv_mem hx)) (Q.inv_mem hz)
  have haa : a*a=1 := by simpa only [pow_two,r.a_order] using pow_orderOf_eq_one a
  have hbb : b*b=1 := by simpa only [pow_two,r.b_order] using pow_orderOf_eq_one b
  have hxx : x*x=1 := by simpa only [pow_two] using r.x_sq
  obtain ⟨hax,hay,haz,hab⟩ := core_first_commutator_central r.toRelations
  have hba : b*a=a*b := hab.symm.eq
  have haba : (a*b)*a=b := by rw [mul_assoc,hba,← mul_assoc,haa,one_mul]
  have habb : (a*b)*b=a := by rw [mul_assoc,hbb,mul_one]
  have habab : (a*b)*(a*b)=1 := by rw [← mul_assoc,haba,hbb]
  have habx : Commute (a*b) x := hax.mul_left r.bx
  have haby : Commute (a*b) y := hay.mul_left r.by_
  have habz : Commute (a*b) z := haz.mul_left r.bz
  have hbne : b ≠ 1 := by
    intro he
    have ho := r.b_order
    simp [he] at ho
  have hCa := (raw_central_actions r).1
  have hCb := (raw_central_actions r).2
  have hCx : MulAut.conj C x=y := r.Cx
  have hCy : MulAut.conj C y=z := r.Cy
  have hCz : MulAut.conj C z=x := r.Cz
  have finish (S : G) (hSsq : S^2=a*b)
      (hSx : MulAut.conj S x=x) (hSy : MulAut.conj S y=z) (hSz : MulAut.conj S z=y)
      (hSq : (S*C)^2 ∈ Q) (q : G) (hq : q ∈ Q) (hS : S=q*T) :
      ∃ U : G, CoreExtensionRelations x y z a b U C ∧ ∃ q ∈ Q, U=q*T := by
    have hSa : MulAut.conj S a=b := by
      rw [← r.xy,map_commutatorElement,hSx,hSy,r.xz]
    have hSb : MulAut.conj S b=a := by
      rw [← r.xz,map_commutatorElement,hSx,hSz,r.xy]
    have hSCx : MulAut.conj (S*C) x=z := by rw [conj_product,hCx,hSy]
    have hSCy : MulAut.conj (S*C) y=y := by rw [conj_product,hCy,hSz]
    have hSCz : MulAut.conj (S*C) z=x := by rw [conj_product,hCz,hSx]
    have hSCa : MulAut.conj (S*C) a=a*b := by rw [conj_product,hCa,map_mul,hSa,hSb,hba]
    have hSCb : MulAut.conj (S*C) b=b := by rw [conj_product,hCb,hSa]
    have hcomm (w : G) (hw : MulAut.conj ((S*C)^2) w=w) : Commute ((S*C)^2) w :=
      mul_inv_eq_iff_eq_mul.mp hw
    have hqx : Commute ((S*C)^2) x := hcomm x (by rw [conj_square,hSCx,hSCz])
    have hqy : Commute ((S*C)^2) y := hcomm y (by rw [conj_square,hSCy,hSCy])
    have hqz : Commute ((S*C)^2) z := hcomm z (by rw [conj_square,hSCz,hSCx])
    have hfix : MulAut.conj (S*C) ((S*C)^2)=(S*C)^2 := by
      change (S*C)*((S*C)^2)*(S*C)⁻¹=(S*C)^2
      rw [((Commute.refl (S*C)).pow_right 2).eq,mul_inv_cancel_right]
    have hcases : (S*C)^2=1 ∨ (S*C)^2=b := by
      rcases core_centralizer_eq_four r.toRelations hSq hqx hqy hqz with he|he|he|he
      · exact Or.inl he
      · rw [he,hSCa] at hfix
        exact (hbne (mul_left_cancel (hfix.trans (mul_one a).symm))).elim
      · exact Or.inr he
      · rw [he,map_mul,hSCa,hSCb,habb] at hfix
        exact (hbne (mul_left_cancel ((mul_one a).trans hfix)).symm).elim
    rcases hcases with he|he
    · refine ⟨S, ?_, q,hq,hS⟩
      exact {
        toRelations := r.toRelations
        T_sq := hSsq
        C_cube := r.C_cube
        TC_sq := he
        Tx := hSx
        Ty := hSy
        Tz := hSz
        Cx := r.Cx
        Cy := r.Cy
        Cz := r.Cz }
    · let U := (a*b)*S
      have hUsq : U^2=a*b := by
        dsimp only [U]
        rw [square_product,map_mul,hSa,hSb,hba,habab,one_mul,hSsq]
      have hUx : MulAut.conj U x=x := by
        rw [show U=(a*b)*S from rfl,conj_product,hSx]
        change (a*b)*x*(a*b)⁻¹=x
        rw [habx.eq,mul_inv_cancel_right]
      have hUy : MulAut.conj U y=z := by
        rw [show U=(a*b)*S from rfl,conj_product,hSy]
        change (a*b)*z*(a*b)⁻¹=z
        rw [habz.eq,mul_inv_cancel_right]
      have hUz : MulAut.conj U z=y := by
        rw [show U=(a*b)*S from rfl,conj_product,hSz]
        change (a*b)*y*(a*b)⁻¹=y
        rw [haby.eq,mul_inv_cancel_right]
      have hUC : (U*C)^2=1 := by
        change ((a*b)*S*C)^2=1
        rw [mul_assoc,square_product,map_mul,hSCa,hSCb,habb,he,haba,hbb]
      refine ⟨U, ?_, (a*b)*q, Q.mul_mem (Q.mul_mem ha hb) hq, ?_⟩
      · exact {
          toRelations := r.toRelations
          T_sq := hUsq
          C_cube := r.C_cube
          TC_sq := hUC
          Tx := hUx
          Ty := hUy
          Tz := hUz
          Cx := r.Cx
          Cy := r.Cy
          Cz := r.Cz }
      · dsimp only [U]
        simp only [hS,mul_assoc]
  let α := MulAut.conj T
  have hTx : α x=x := r.Tx
  have hTa : α a=b := r.Ta
  have hTb : α b=a := r.Tb
  have hTyy : α (α y)=y := by
    change MulAut.conj T (MulAut.conj T y)=y
    rw [← conj_square,r.T_sq]
    change (a*b)*y*(a*b)⁻¹=y
    rw [haby.eq,mul_inv_cancel_right]
  have hTy2 : (α y)^2=1 := by rw [← map_pow,r.y_sq,map_one]
  have hTcomm : ⁅x,α y⁆=b := by rw [← hTx,← map_commutatorElement,r.xy,hTa]
  have hdefect : α y=z ∨ α y=z*a ∨ α y=z*b ∨ α y=z*(a*b) :=
    core_involution_commutator_eq_four r.toRelations r.Ty_mem hTy2 hTcomm
  have hδ (w : G) : MulAut.conj ((T*C)^2) w=α (MulAut.conj C (α (MulAut.conj C w))) := by
    rw [conj_square,conj_product,conj_product]
  rcases hdefect with he|he|he|he
  · have hz' : α z=y := by simpa only [he] using hTyy
    exact finish T r.T_sq hTx he hz' r.TC_sq_mem 1 Q.one_mem (one_mul T).symm
  · have hz' : α z=y*b := by
      have hh : α z*b=y := by simpa only [he,map_mul,hTa] using hTyy
      calc α z=(α z*b)*b := by rw [mul_assoc,hbb,mul_one]
           _=y*b := by rw [hh]
    exfalso
    apply core_not_inner_shift_one r.toRelations r.TC_sq_mem
    refine ⟨?_,?_,?_⟩
    · change MulAut.conj ((T*C)^2) x=x*(a*b)
      simp only [hδ,hCx,he,map_mul,hCz,hCa,hTx,hTa,hTb,hba]
    · change MulAut.conj ((T*C)^2) y=y
      simp only [hδ,hCy,hz',map_mul,hCb,hTa,mul_assoc,hbb,mul_one]
    · change MulAut.conj ((T*C)^2) z=z*a
      rw [hδ,hCz,hTx,hCx,he]
  · have hz' : α z=y*a := by
      have hh : α z*a=y := by simpa only [he,map_mul,hTb] using hTyy
      calc α z=(α z*a)*a := by rw [mul_assoc,haa,mul_one]
           _=y*a := by rw [hh]
    have hxy : MulAut.conj x y=a*y := by rw [conj_eq_commutatorElement_mul,r.xy]
    have hxz : MulAut.conj x z=b*z := by rw [conj_eq_commutatorElement_mul,r.xz]
    have hxa : MulAut.conj x a=a := by change x*a*x⁻¹=a; rw [hax.symm.eq,mul_inv_cancel_right]
    have hxb : MulAut.conj x b=b := by change x*b*x⁻¹=b; rw [r.bx.symm.eq,mul_inv_cancel_right]
    have hSsq : (x*T)^2=a*b := by rw [square_product,hTx,hxx,one_mul,r.T_sq]
    have hSx : MulAut.conj (x*T) x=x := by rw [conj_product,hTx]; simp
    have hSy : MulAut.conj (x*T) y=z := by
      rw [conj_product,he,map_mul,hxz,hxb,r.bz.eq,mul_assoc,hbb,mul_one]
    have hSz : MulAut.conj (x*T) z=y := by
      rw [conj_product,hz',map_mul,hxy,hxa,hay.eq,mul_assoc,haa,mul_one]
    have hSq : ((x*T)*C)^2 ∈ Q := by
      rw [mul_assoc,square_product,conj_product,hCx,he]
      exact Q.mul_mem (Q.mul_mem hx (Q.mul_mem hz hb)) r.TC_sq_mem
    exact finish (x*T) hSsq hSx hSy hSz hSq x hx rfl
  · have hz' : α z=y*(a*b) := by
      have hh : α z*(a*b)=y := by simpa only [he,map_mul,hTa,hTb,hba] using hTyy
      calc α z=(α z*(a*b))*(a*b) := by rw [mul_assoc,habab,mul_one]
           _=y*(a*b) := by rw [hh]
    exfalso
    apply core_not_inner_shift_two r.toRelations r.TC_sq_mem
    refine ⟨?_,?_,?_⟩
    · change MulAut.conj ((T*C)^2) x=x*a
      simp only [hδ,hCx,he,map_mul,hCz,hCa,hCb,haba,hTx,hTb]
    · change MulAut.conj ((T*C)^2) y=y*b
      simp only [hδ,hCy,hz',map_mul,hCa,hCb,haba,hTb,mul_assoc]
    · change MulAut.conj ((T*C)^2) z=z*(a*b)
      rw [hδ,hCz,hTx,hCx,he]

/-- Raw source lifts determine the actual second parabolic after the two
explicit core corrections. -/
theorem secondParabolic_equiv_of_raw_coreExtension_relations [Finite G]
    (x y z a b T C : G) (r : CoreExtensionRawRelations x y z a b T C)
    (hgen : closure ({x,y,z,T,C}:Set G)=⊤) (hcard : 192 ≤ Nat.card G) :
    Nonempty (G ≃* secondParabolic) := by
  obtain ⟨U,hU,q,hq,hUq⟩ := r.normalize
  have hgenU : closure ({x,y,z,U,C}:Set G)=⊤ := by
    let K := closure ({x,y,z,U,C}:Set G)
    have hQ : closure ({x,y,z}:Set G) ≤ K := by
      apply Subgroup.closure_mono
      intro w hw
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw ⊢
      tauto
    have hT : T ∈ K := by
      have hh := K.mul_mem (K.inv_mem (hQ hq)) (subset_closure (by simp : U∈({x,y,z,U,C}:Set G)))
      simpa only [hUq,inv_mul_cancel_left] using hh
    apply top_unique
    rw [← hgen]
    apply (closure_le _).mpr
    rintro w (rfl|rfl|rfl|rfl|rfl)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact hT
    · exact subset_closure (by simp)
  exact secondParabolic_equiv_of_coreExtension_relations x y z a b U C hU hgenU hcard

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
