module
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.Elementary
public import Theory.Representation.SL2NaturalOffenders.FixedField.ActorAlignment
public import Theory.Representation.SL2.BinarySmallInvolution.Hermitian

/-!
# Fixed spaces of actual outer Hermitian involutions

Hilbert–90 aligns an outer involution of SL₂ with its quadratic field
conjugation. The same inner change of coordinates aligns its additive
Hermitian lift: scalar rigidity and the involution identity remove the
remaining scalar. Thus the actual lift fixes exactly a hyperplane of
order q³. A nontrivial inner two-group fixes at most q² vectors, by the
existing involution displacement calculation.

These are the native module inputs for the full fixed-centralizer step
of Aschbacher–Smith F.4.37, printed p.293 of refs/quasithin.pdf. They do
not replace the full centralizer by the graph-fixed source Sylow.
-/

public noncomputable section
open scoped IsMulCommutative
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOuterFixed
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne.AmbientActions
variable (m : ℕ) [NeZero m]
local instance : Algebra (ZMod 2) (fixedField m) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space m) :=
  Module.compHom (Space m) (algebraMap (ZMod 2) (fixedField m))

private theorem field_involution_eq (σ : Field m ≃+* Field m)
    (hs : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl _) : σ=conjugation m := by
  classical
  let : IsCyclic (Field m ≃+* Field m) := Representation.SL2NaturalOffenders.binaryFieldAut_isCyclic
  let : Finite (Field m ≃+* Field m) := Finite.of_injective
    (fun e : Field m ≃+* Field m => (e : Field m → Field m)) DFunLike.coe_injective
  let := Fintype.ofFinite (Field m ≃+* Field m)
  have hσ : σ^2=1 := by ext x; exact hs x
  have hconj2 : conjugation m ^ 2 = 1 := by ext x; exact conjugation_involutive m x
  have hconjne : conjugation m ≠ 1 := by
    obtain ⟨x,hx⟩ := exists_conjugation_ne m
    exact fun he => hx (DFunLike.congr_fun he x)
  by_contra hh
  have hle : ({1,σ,conjugation m} : Finset (Field m ≃+* Field m)) ⊆
      Finset.univ.filter (fun a => a^2=1) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [hσ,hconj2]
  have hne1 : σ ≠ 1 := hne
  have hc : ({1,σ,conjugation m} : Finset (Field m ≃+* Field m)).card = 3 := by
    simp [hh,Ne.symm hne1,Ne.symm hconjne]
  have hb := IsCyclic.card_pow_eq_one_le (α := Field m ≃+* Field m) (n := 2) (by decide)
  have hbound := Finset.card_le_card hle
  rw [hc] at hbound
  omega

/-- The same inner change of coordinates makes the entire outer Hermitian
involution the canonical quadratic conjugation. -/
theorem outer_lift_conjugation
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) (Field m))) (hα : α^2=1)
    (hout : ¬ ∃ g, α=MulAut.conj g)
    (E : Space m ≃+ Space m) (hE2 : Function.Involutive E)
    (hE : ∀ g x, E (action m g x) = action m (α g) (E x)) :
    ∃ c : Matrix.SpecialLinearGroup (Fin 2) (Field m),
      ∀ x, E (action m c x)=action m c (Representation.OrthogonalFourMinus.HermitianEquiv.conjugationLinear m x) := by
  obtain ⟨σ,hσ,hs,c,hc⟩ := Representation.SL2NaturalOffenders.outer_involution_actor_alignment α hα hout
  have heq := field_involution_eq m σ hs hσ
  subst σ
  let a := (LinearMap.GeneralLinearGroup.toLinearEquiv ((action m).asGroupHom c)).toAddEquiv
  let D := a.trans (E.trans a.symm)
  have hD2 : Function.Involutive D := by
    intro x
    change a.symm (E (a (a.symm (E (a x)))))=x
    rw [a.apply_symm_apply,hE2,a.symm_apply_apply]
  have hconj (g : Matrix.SpecialLinearGroup (Fin 2) (Field m)) :
      α (c*g*c⁻¹) = c*Theory.PSL2.sl2FieldAut (conjugation m) g*c⁻¹ := by
    have hh := hc (c*g*c⁻¹)
    change c⁻¹*α (c*g*c⁻¹)*(c⁻¹)⁻¹ = _ at hh
    have hcancel : (MulAut.conj c⁻¹) (c*g*c⁻¹)=g := by
      change c⁻¹*(c*g*c⁻¹)*(c⁻¹)⁻¹=g
      group
    rw [hcancel] at hh
    calc
      _ = c*(c⁻¹*α (c*g*c⁻¹)*(c⁻¹)⁻¹)*c⁻¹ := by group
      _ = _ := by rw [hh]
  have hD (g : Matrix.SpecialLinearGroup (Fin 2) (Field m)) (x : Space m) :
      D (action m g x) = action m (Matrix.SpecialLinearGroup.map (conjugation m).toRingHom g) (D x) := by
    apply a.injective
    change a (a.symm (E (a (action m g x)))) = a (action m _ (a.symm (E (a x))))
    rw [a.apply_symm_apply]
    have hcact : a (action m g x)=action m (c*g*c⁻¹) (a x) := by
      change action m c (action m g x)=action m (c*g*c⁻¹) (action m c x)
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
    rw [hcact,hE,hconj]
    change action m (c*Theory.PSL2.sl2FieldAut (conjugation m) g*c⁻¹) (E (a x)) =
      action m c (action m (Theory.PSL2.sl2FieldAut (conjugation m) g) (a.symm (E (a x))))
    have hcback : E (a x)=action m c (a.symm (E (a x))) := (a.apply_symm_apply _).symm
    conv_lhs => rw [hcback]
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  have hcanonical := involutive_field_lift_eq_conjugation m D.toAddMonoidHom hD2 hD
  refine ⟨c,fun x => ?_⟩
  have hh := congrArg a (hcanonical x)
  change a (a.symm (E (a x))) = a _ at hh
  rwa [a.apply_symm_apply] at hh

/-- Every actual outer involution fixes exactly a hyperplane of order q³. -/
theorem outer_fixed_card
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) (Field m))) (hα : α^2=1)
    (hout : ¬ ∃ g, α=MulAut.conj g)
    (E : Space m ≃+ Space m) (hE2 : Function.Involutive E)
    (hE : ∀ g x, E (action m g x) = action m (α g) (E x)) :
    Nat.card {x : Space m // E x=x} = (2^m)^3 := by
  obtain ⟨c,hc⟩ := outer_lift_conjugation m α hα hout E hE2 hE
  let a := LinearMap.GeneralLinearGroup.toLinearEquiv ((action m).asGroupHom c)
  let V := ((Representation.OrthogonalFourMinus.HermitianEquiv.conjugationLinear m).toLinearMap - LinearMap.id).ker
  have he (x : Space m) : x ∈ V ↔ E (a x)=a x := by
    change Representation.OrthogonalFourMinus.HermitianEquiv.conjugationLinear m x-x=0 ↔ _
    have hh : E (a x) = a (Representation.OrthogonalFourMinus.HermitianEquiv.conjugationLinear m x) := hc x
    rw [sub_eq_zero,hh]
    exact a.injective.eq_iff.symm
  let e : V ≃ {x : Space m // E x=x} :=
    { toFun x := ⟨a x,(he x).mp x.property⟩
      invFun x := ⟨a.symm x,(he _).mpr (by rw [a.apply_symm_apply]; exact x.property)⟩
      left_inv x := Subtype.ext (a.symm_apply_apply x)
      right_inv x := Subtype.ext (a.apply_symm_apply x) }
  have hr := ((Representation.OrthogonalFourMinus.HermitianEquiv.conjugationLinear m).toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
  rw [Representation.OrthogonalFourMinus.RankOne.conjugation_moved_finrank,finrank_space] at hr
  change 1 + Module.finrank (fixedField m) V = 4 at hr
  have hd : Module.finrank (fixedField m) V=3 := by omega
  rw [←Nat.card_congr e,Module.natCard_eq_pow_finrank (K := fixedField m),hd,card_fixedField]

/-- A nontrivial inner two-group fixes at most q² Hermitian vectors. -/
theorem inner_two_group_fixed_card
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field m)))
    (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    Nat.card {x : Space m // ∀ g : P, action m g.val x=x} ≤ (2^m)^2 := by
  have hd : 2 ∣ Nat.card P := hP.card_eq_or_dvd.resolve_left
    (fun hh => hne (Subgroup.card_eq_one.mp hh))
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' 2 hd
  have hg2 : orderOf g.val=2 := (Subgroup.orderOf_coe g).trans hg
  let a := ((action m g.val).toAddMonoidHom.toZModLinearMap 2)-LinearMap.id
  have hr := Representation.SL2.BinarySmall.HermitianInvolution.rank_ge m g.val hg2
  have hadd := a.finrank_range_add_finrank_ker
  change 2*m ≤ Module.finrank (ZMod 2) (LinearMap.range a) at hr
  have hdim : Module.finrank (ZMod 2) (Space m) = 4*m := by
    have hb := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space m)
    have hk := Module.natCard_eq_pow_finrank (K := fixedField m) (V := Space m)
    rw [Nat.card_zmod] at hb
    rw [card_fixedField,finrank_space,←pow_mul] at hk
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact hb.symm.trans (hk.trans (by rw [Nat.mul_comm]))
  rw [hdim] at hadd
  have hk : Module.finrank (ZMod 2) a.ker ≤ 2*m := by omega
  let j : {x : Space m // ∀ g : P, action m g.val x=x} → a.ker :=
    fun x => ⟨x.val,sub_eq_zero.mpr (x.property g)⟩
  have hj : Function.Injective j := fun x y hh => Subtype.ext
    (congrArg (fun z : a.ker => z.val) hh)
  calc
    _ ≤ Nat.card a.ker := Nat.card_le_card_of_injective j hj
    _ = 2^(Module.finrank (ZMod 2) a.ker) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    _ ≤ 2^(2*m) := Nat.pow_le_pow_right (by decide) hk
    _ = (2^m)^2 := by rw [←pow_mul,Nat.mul_comm m 2]

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOuterFixed
