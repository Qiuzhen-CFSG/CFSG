module
public import Theory.Representation.PSL3Two.RankTwoOuterRecognition
public import Theory.Representation.BinaryOffender.PerfectMoved
public import Theory.Representation.FrattiniAction
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The outer-automorphism obstruction to a single cubic factor

Two conjugate cubics generate the actual binary SL₃. Their displacement
spaces bound a fully moved module by twice the cubic fixed codimension.
At codimension two this gives dimension at most four, whereas an implemented
outer automorphism forces the natural–dual six-space. Perfectness applies
this obstruction to the moved submodule without any splitting assumption.

For an action on a two-group, a moving cubic remains moving on the Frattini
quotient, and the fixed index cannot increase. We descend through the full
specified actor kernel and apply the linear obstruction. The normal-supplement
lemma supplies that kernel from the original local join in the Chapter12
application; it is not replaced by the kernel on a chosen submodule.

Source: Aschbacher–Smith, final paragraph proving 7.7.3, printed p.709,
refs/quasithin.pdf. This gives an alternative to composition-factor bookkeeping
on Q/W, retaining the full quotient and its original outer action.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Matrix Matrix.PSL3Two
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeOuter
open BinaryLinearThree

private def c : SL := ⟨!![1,0,0;0,0,1;0,1,1], by decide⟩
private def d : SL := ⟨!![1,1,0;1,0,0;0,0,1], by decide⟩
private def s : SL := ⟨!![0,0,1;0,1,0;1,0,0], by decide⟩
private theorem order_c : orderOf c = 3 :=
  orderOf_eq_prime (by decide : c ^ 3 = 1) (by decide : c ≠ 1)
private theorem d_conj : d = s * c * s⁻¹ := by decide

private def x : SL := ⟨!![1,1,0;0,1,0;0,0,1], by decide⟩
private def y : SL := ⟨!![1,0,0;0,1,1;0,0,1], by decide⟩
private def z : SL := ⟨!![1,0,0;0,1,0;1,0,1], by decide⟩

private theorem cubic_generators : closure ({c,d} : Set SL) = ⊤ := by
  let H := closure ({c,d} : Set SL)
  have hc : c ∈ H := subset_closure (by simp)
  have hd : d ∈ H := subset_closure (by simp)
  have hx : x ∈ H := by
    have he : x = d*c*d*c*c*d*c := by decide
    rw [he]
    repeat first | exact hc | exact hd | apply H.mul_mem
  have hy : y ∈ H := by
    have he : y = d*c*d*d*c*d*c := by decide
    rw [he]
    repeat first | exact hc | exact hd | apply H.mul_mem
  have hz : z ∈ H := by
    have he : z = c*d*d*c*d*c*c*d := by decide
    rw [he]
    repeat first | exact hc | exact hd | apply H.mul_mem
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g ∈ H) ?_ (fun _ _ => H.mul_mem) g
  intro i j hij a
  have he : ∀ (i j : Fin 3) (hij : i ≠ j) (a : ZMod 2),
      SpecialLinearGroup.transvection hij a = 1 ∨
      SpecialLinearGroup.transvection hij a = x ∨
      SpecialLinearGroup.transvection hij a = y ∨
      SpecialLinearGroup.transvection hij a = z ∨
      SpecialLinearGroup.transvection hij a = x*y*x*y ∨
      SpecialLinearGroup.transvection hij a = y*z*y*z ∨
      SpecialLinearGroup.transvection hij a = z*x*z*x := by decide
  rcases he i j hij a with h | h | h | h | h | h | h <;> rw [h]
  · exact H.one_mem
  · exact hx
  · exact hy
  · exact hz
  · exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) hx) hy
  · exact H.mul_mem (H.mul_mem (H.mul_mem hy hz) hy) hz
  · exact H.mul_mem (H.mul_mem (H.mul_mem hz hx) hz) hx

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M]

private theorem canonical_cubic_bound (ρ : Representation (ZMod 2) SL M)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) :
    Module.finrank (ZMod 2) M ≤ 2 * fixedCodim ρ (zpowers c) := by
  let D (g : SL) := LinearMap.range (ρ g - LinearMap.id)
  let U := D c ⊔ D d
  let H : Subgroup SL := {
    carrier := {g | ∀ v, ρ g v - v ∈ U}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro g h hg hh v
      have hm := U.add_mem (hg (ρ h v)) (hh v)
      simpa only [map_mul,Module.End.mul_apply,sub_add_sub_cancel] using hm
    inv_mem' := by
      intro g hg v
      have hm := U.neg_mem (hg (ρ g⁻¹ v))
      simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
        Module.End.one_apply,neg_sub] using hm }
  have hH : H = ⊤ := by
    apply top_unique
    rw [←cubic_generators]
    apply (closure_le _).mpr
    rintro g (rfl | rfl) v
    · exact (show D c ≤ U from le_sup_left) (show ρ c v - v ∈ D c from ⟨v,rfl⟩)
    · exact (show D d ≤ U from le_sup_right) (show ρ d v - v ∈ D d from ⟨v,rfl⟩)
  have hU : U = ⊤ := by
    apply top_unique
    rw [←hfull]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    exact (show g ∈ H from hH ▸ mem_top g) v
  have hb := Submodule.finrank_sup_add_finrank_inf_eq (D c) (D d)
  have hd : fixedCodim ρ (zpowers d) = fixedCodim ρ (zpowers c) := by
    rw [d_conj,fixedCodim_zpowers_conj]
  rw [←fixedCodim_zpowers_eq_displacement_rank,
    ←fixedCodim_zpowers_eq_displacement_rank,hd] at hb
  change Module.finrank (ZMod 2) U + _ = _ at hb
  rw [hU,finrank_top] at hb
  omega

/-- Two conjugate cubics generate SL₃(2), bounding every fully moved module. -/
theorem cubic_dimension_bound (ρ : Representation (ZMod 2) SL M)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (A : Subgroup SL) (hA : Nat.card A = 3) :
    Module.finrank (ZMod 2) M ≤ 2 * fixedCodim ρ A := by
  have syl (B : Subgroup SL) (hB : Nat.card B = 3) : ∃ P : Sylow 3 SL, P = B := by
    have hp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hB)
    have hi : B.index = 56 := by
      have hh := B.card_mul_index
      rw [hB,card_SL] at hh
      omega
    exact ⟨hp.toSylow (by rw [hi]; decide),rfl⟩
  obtain ⟨P,hP⟩ := syl (zpowers c) ((Nat.card_zpowers c).trans order_c)
  obtain ⟨Q,hQ⟩ := syl A hA
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL P Q
  have hm : (zpowers c).map (MulAut.conj g).toMonoidHom = A := by
    have hh := congrArg Sylow.toSubgroup hg
    change (P : Subgroup SL).map (MulAut.conj g).toMonoidHom = (Q : Subgroup SL) at hh
    rwa [hP,hQ] at hh
  have hc := fixedCodim_map_conj ρ (zpowers c) g
  rw [hm] at hc
  exact (canonical_cubic_bound ρ hfull).trans_eq (congrArg (2 * ·) hc.symm)

/-- A nonzero fully moved module with one cubic factor cannot implement an outer automorphism. -/
theorem no_outer_small_cubic [Nontrivial M]
    (ρ : Representation (ZMod 2) SL M) (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (A : Subgroup SL) (hA : Nat.card A = 3) (hsmall : fixedCodim ρ A ≤ 2)
    (α : MulAut SL) (hα : α ∉ MulAut.innerSubgroup SL)
    (f : M ≃ₗ[ZMod 2] M) (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v)) : False := by
  have hb := cubic_dimension_bound ρ hfull A hA
  obtain ⟨e⟩ := RankTwoOuterRecognition.equiv_natural_dual_of_finrank_le_six
    ρ hfull (by omega) α hα f hf
  have hd := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod,Subspace.dual_finrank_eq] at hd
  norm_num [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector] at hd
  omega


/-- The same obstruction applies before removing fixed vectors or extensions. -/
theorem no_outer_cubic_module
    (ρ : Representation (ZMod 2) SL M) (hne : ρ ≠ 1)
    (A : Subgroup SL) (hA : Nat.card A = 3) (hsmall : fixedCodim ρ A ≤ 2)
    (α : MulAut SL) (hα : α ∉ MulAut.innerSubgroup SL)
    (f : M ≃ₗ[ZMod 2] M) (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v)) : False := by
  let : _root_.Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
  let I := subspaceCommutator ρ ⊤ ⊤
  let C : Subrepresentation ρ := ⟨I,fun g v hv =>
    ((subspaceCommutator_invariant ρ ⊤ ⊤) (mem_top g) v).2 hv⟩
  have hI : I ≠ ⊥ := by
    intro hz
    apply hne
    ext g v
    exact ((subspaceCommutator_eq_bot_iff ρ ⊤ ⊤).mp hz)
      Submodule.mem_top ⟨g,mem_top g⟩
  let : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hI
  have hfull : subspaceCommutator C.toRepresentation ⊤ ⊤ = ⊤ := by
    apply Submodule.map_injective_of_injective I.subtype_injective
    have hm := subspaceCommutator_map_embedding ρ C.toRepresentation (MonoidHom.id SL)
      I.subtype (fun _ _ => rfl) ⊤ ⊤
    simp only [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id] at hm
    simpa only [Submodule.map_top,Submodule.range_subtype] using
      hm.symm.trans (subspaceCommutator_idempotent_of_perfect ρ ⊤)
  have hi : I.map f.toLinearMap = I := by
    have hm := subspaceCommutator_map_embedding ρ ρ α.symm.toMonoidHom
      f.toLinearMap (fun g v => by
        change ρ g (f v) = f (ρ (α.symm g) v)
        rw [hf,α.apply_symm_apply]) ⊤ ⊤
    rw [Subgroup.map_top_of_surjective _ α.symm.surjective,
      Submodule.map_top,LinearMap.range_eq_top.mpr f.surjective] at hm
    exact hm.symm
  let F := f.ofSubmodules I I hi
  exact no_outer_small_cubic C.toRepresentation hfull A hA
    ((fixedCodim_subrepresentation_le ρ C A).trans hsmall) α hα F
    (fun g v => Subtype.ext (hf g v))


/-- The full automorphism group cannot act nontrivially through an inner cubic of codimension two. -/
theorem no_automorphism_cubic_module
    (τ : Representation (ZMod 2) (MulAut SL) M)
    (g : SL) (hg : orderOf g = 3) (hm : τ (MulAut.conj g) ≠ 1)
    (hsmall : fixedCodim τ (zpowers (MulAut.conj g)) ≤ 2) : False := by
  let ρ := τ.comp (MulAut.conj : SL →* MulAut SL)
  have hne : ρ ≠ 1 := by
    intro he
    exact hm (congrArg (fun σ : Representation (ZMod 2) SL M => σ g) he)
  let α := AutomorphismAction.graph
  let f := LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom α)
  have hf (a : SL) (v : M) : f (ρ a v) = ρ (α a) (f v) := by
    change τ α (τ (MulAut.conj a) v) = τ (MulAut.conj (α a)) (τ α v)
    have he : α * MulAut.conj a = MulAut.conj (α a) * α := by
      ext k
      simp only [MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv]
    rw [←Module.End.mul_apply,←map_mul,he,map_mul,Module.End.mul_apply]
  have hb : fixedCodim ρ (zpowers g) ≤ 2 := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,MonoidHom.map_zpowers]
    exact hsmall
  exact no_outer_cubic_module ρ hne (zpowers g) ((Nat.card_zpowers g).trans hg)
    hb α AutomorphismAction.graph_not_inner f hf

section GroupAction
variable {J X B : Type*} [_root_.Group J] [_root_.Group X] [Finite X]
  [_root_.Group B] [MulDistribMulAction B X]

/-- Frattini descent excludes fixed index at most four for a moving cubic,
when the original action descends to the full binary-three automorphism group. -/
theorem no_cubic_four_action (hX : IsPGroup 2 X)
    (a : J →* MulAut X) (q : J →* MulAut SL) (hq : Function.Surjective q)
    (hker : q.ker ≤ ((frattini X).quotientAut.comp a).ker)
    (c : J) (ho : orderOf c = 3) (hc : a c ≠ 1)
    (g : SL) (hg : orderOf g = 3) (hqg : q c = MulAut.conj g)
    (k : B →* J) (z : B) (hz : zpowers z = ⊤) (hk : k z = c)
    (hacts : ∀ r, MulDistribMulAction.toMulAut B X r = a (k r))
    (hi : (FixedPoints.subgroup B X).index ≤ 4) : False := by
  let Y := X ⧸ frattini X
  let : Fact (IsPGroup 2 X) := ⟨hX⟩
  let : IsElementaryAbelian 2 Y := isElementaryAbelian_quotient_frattini
  let b : J →* MulAut Y := (frattini X).quotientAut.comp a
  let β : MulAut SL →* MulAut Y := q.liftOfSurjective hq ⟨b,hker⟩
  have hb (l : J) : β (q l) = b l :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let ρ := FrattiniAction.ofAutomorphismHom β
  have hm : ρ (MulAut.conj g) ≠ 1 := by
    intro he
    apply FrattiniAction.quotientAut_cubic_ne_one hX a c ho hc
    change b c = 1
    rw [←hb,hqg]
    ext v
    exact Additive.ofMul.injective (LinearMap.congr_fun he (Additive.ofMul v))
  let D := zpowers (q c)
  let r : B →* MulAut SL := q.comp k
  have hr : r.range = D := by
    rw [MonoidHom.range_eq_map,←hz,MonoidHom.map_zpowers]
    exact congrArg zpowers (congrArg q hk)
  let r' := r.codRestrict D (fun x => hr ▸ (show r x ∈ r.range from ⟨x,rfl⟩))
  have hrs : Function.Surjective r' := by
    rintro ⟨x,hx⟩
    obtain ⟨v,hv⟩ := (show x ∈ r.range from hr.symm ▸ hx)
    exact ⟨v,Subtype.ext hv⟩
  let τ := ρ.comp D.subtype
  let := BinaryFixedPoints.action (τ.comp r')
  let F : X →* Multiplicative (Additive Y) := {
    toFun x := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (frattini X) x))
    map_one' := by change QuotientGroup.mk' (frattini X) 1 = 1; exact map_one _
    map_mul' x y := (QuotientGroup.mk' (frattini X)).map_mul x y }
  have heq (r : B) (x : X) : F (r • x) = r • F x := by
    change QuotientGroup.mk' (frattini X) (MulDistribMulAction.toMulAut B X r x) =
      β (q (k r)) (QuotientGroup.mk' (frattini X) x)
    rw [hb]
    change _ = (frattini X).quotientAut (a (k r)) (QuotientGroup.mk' (frattini X) x)
    rw [Subgroup.quotientAut_apply_mk,hacts]
  have hi' : BinaryFixedPoints.fixedIndex (τ.comp r') ≤ 4 :=
    (fixedPoints_index_le_of_surjective_equivariant F
      (QuotientGroup.mk'_surjective (frattini X)) heq).trans hi
  have ht := BinaryFixedPoints.fixedIndex_eq_of_equivariant τ r' hrs
    (MulEquiv.refl _) (by intros; rfl)
  change BinaryFixedPoints.fixedIndex (τ.comp r') = BinaryFixedPoints.fixedIndex τ at ht
  rw [ht,FrattiniAction.fixedIndex_eq_two_pow_fixedCodim ρ D] at hi'
  have hd : fixedCodim ρ (zpowers (MulAut.conj g)) ≤ 2 := by
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (show 2 ^ fixedCodim ρ D ≤ 2 ^ 2 from hi')
    simpa only [D,hqg] using hh
  exact no_automorphism_cubic_module ρ g hg hm hd
end GroupAction


/-- A kernel which is a two-group on a normal supplement remains a two-group
after adjoining the original two-group. -/
theorem kernel_two_of_normal_supplement
    {J F : Type*} [_root_.Group J] [_root_.Group F]
    (q : J →* F) (K S : Subgroup J) [K.Normal]
    (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤)
    (hk : IsPGroup 2 (q.ker.subgroupOf K)) : IsPGroup 2 q.ker := by
  have hquot := isPGroup_quotient_of_sup_eq_top K S hS hgen
  let r := (QuotientGroup.mk' K).comp q.ker.subtype
  let j : r.ker →* q.ker.subgroupOf K := {
    toFun x := ⟨⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩,x.val.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : q.ker.subgroupOf K => z.val.val) he))
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup r (hk.of_injective j hj)
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeOuter
