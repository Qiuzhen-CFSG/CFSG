module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.FieldExtraction.TraceField
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.NormalClosure
public import Theory.GroupTheory.InvolutionOddProduct

/-!
# Odd products and internal fusion of actual symplectic transvections

A symplectic element centralizing a rank-one unipotent fixes its displacement
line pointwise in characteristic two. For a noncommuting pair, the two centers
span a nondegenerate plane; a central power of their product therefore fixes
that plane and its orthogonal complement. The half-order involution argument
shows that the product has odd order.

If two transvections were not conjugate in an irreducible subgroup, the second
would commute with every conjugate of the first. It would then fix the orbit
span of a nonzero center vector, hence the entire natural module. Applying
this to the already irreducible normal closure gives fusion inside that same
closure, as required by Aschbacher--Smith G.4.5--6, printed pp.339--340.
-/

public noncomputable section
open Subgroup Module
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2]

private theorem form_symm (x y : Vector F) : form F x y=form F y x := by
  simpa only [CharTwo.neg_eq] using TwoLocalCover.form_alternating.neg_eq x y

omit [CharP F 2] in
theorem rank_one_formula (t : Sp F) (ht : IsB1 t) :
    ∃ (u : Vector F) (c : F), u≠0 ∧ c≠0 ∧
      ∀ x, t • x=x+(c*form F u x) • u := by
  let ρ : Representation F (Sp F) (Vector F) := Representation.symplecticNatural 2
  obtain ⟨u,l,hu,hl,hN⟩ := Representation.TraceFieldDescent.exists_smulRight_of_rank_one
    (ρ t-1) ht.2
  obtain ⟨c,hc,hcl⟩ := Representation.TraceFieldDescent.functional_eq_form
    ρ t u hu l hl hN (form F) TwoLocalCover.form_alternating
    TwoLocalCover.form_nondegenerate (preserves_form t)
  refine ⟨u,c,hu,hc,fun x => ?_⟩
  have h := LinearMap.congr_fun hN x
  change t • x-x=l x • u at h
  rw [hcl] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem fixes_center_of_commute (t g : Sp F) (u : Vector F) (c : F)
    (hu : u≠0) (hc : c≠0)
    (ht : ∀ x, t • x=x+(c*form F u x) • u) (hcomm : Commute g t) :
    g • u=u := by
  obtain ⟨x,hx⟩ : ∃ x, form F u x≠0 := by
    by_contra! hn
    exact hu (TwoLocalCover.form_nondegenerate.1 u hn)
  have he (y : Vector F) :
      (c*form F u y) • (g • u)=(c*form F u (g • y)) • u := by
    have h := congrArg (fun a : Sp F => a • y) hcomm.eq
    rw [mul_smul,mul_smul] at h
    rw [ht,ht,show g • (y+(c*form F u y) • u)=
      g • y+g • ((c*form F u y) • u) from (toLinear g).map_add _ _] at h
    rw [show g • ((c*form F u y) • u)=(c*form F u y) • (g • u) from
      (toLinear g).map_smul _ _] at h
    exact add_left_cancel h
  let k := form F u (g • x) / form F u x
  have hgu : g • u=k • u := by
    apply (smul_right_injective _ (mul_ne_zero hc hx))
    change (c*form F u x) • (g • u)=(c*form F u x) • (k • u)
    rw [he,smul_smul]
    congr 1
    dsimp [k]
    field_simp
  have hk (y : Vector F) : form F u (g • y)=k*form F u y := by
    have h := he y
    rw [hgu,smul_smul] at h
    have hh := (smul_left_injective F hu) h
    exact (mul_left_cancel₀ hc (by simpa only [mul_assoc,mul_comm k] using hh)).symm
  have hk2 : k^2=1 := by
    have h := preserves_form g u x
    rw [hgu,LinearMap.map_smul,LinearMap.smul_apply,smul_eq_mul,hk] at h
    apply (mul_right_cancel₀ hx)
    simpa only [pow_two,mul_assoc,one_mul] using h
  have hk1 : k=1 := CharTwo.sq_injective (hk2.trans (one_pow 2).symm)
  simpa only [hk1,one_smul] using hgu

private theorem commute_of_zero_pairing (a b : Sp F) (u v : Vector F) (c d : F)
    (ha : ∀ x, a • x=x+(c*form F u x) • u)
    (hb : ∀ x, b • x=x+(d*form F v x) • v)
    (huv : form F u v=0) : Commute a b := by
  have hvu : form F v u=0 := (form_symm v u).trans huv
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Vector F)
  intro x
  change (a*b) • x=(b*a) • x
  rw [mul_smul,mul_smul]
  rw [ha,hb,hb,ha]
  simp only [map_add,map_smul,smul_eq_mul,huv,hvu,mul_zero,add_zero]
  abel

private theorem power_eq_one_of_commute (a b : Sp F) (u v : Vector F) (c d : F)
    (hu : u≠0) (hv : v≠0) (hc : c≠0) (hd : d≠0)
    (ha : ∀ x, a • x=x+(c*form F u x) • u)
    (hb : ∀ x, b • x=x+(d*form F v x) • v)
    (huv : form F u v≠0) (n : ℕ)
    (hza : Commute ((a*b)^n) a) (hzb : Commute ((a*b)^n) b) :
    (a*b)^n=1 := by
  let z := (a*b)^n
  have hzu : z • u=u := fixes_center_of_commute a z u c hu hc ha hza
  have hzv : z • v=v := fixes_center_of_commute b z v d hv hd hb hzb
  have hvu : form F v u≠0 := by rwa [form_symm]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Vector F)
  intro x
  let α := form F v x / form F v u
  let β := form F u x / form F u v
  let w := x-α • u-β • v
  have huw : form F u w=0 := by
    simp only [w,map_sub,map_smul,smul_eq_mul,TwoLocalCover.form_alternating.self_eq_zero,
      mul_zero,sub_zero,β,div_mul_cancel₀ _ huv,sub_self]
  have hvw : form F v w=0 := by
    simp only [w,map_sub,map_smul,smul_eq_mul,TwoLocalCover.form_alternating.self_eq_zero,
      mul_zero,α,div_mul_cancel₀ _ hvu,sub_self]
  have haw : a • w=w := by rw [ha,huw,mul_zero,zero_smul,add_zero]
  have hbw : b • w=w := by rw [hb,hvw,mul_zero,zero_smul,add_zero]
  have hrw : (a*b) • w=w := by rw [mul_smul,hbw,haw]
  have hpw : ∀ m : ℕ, (a*b)^m • w=w := by
    intro m
    induction m with
    | zero => simp
    | succ m hm => rw [pow_succ,mul_smul,hrw,hm]
  have hzw : z • w=w := hpw n
  have hx : x=w+α • u+β • v := by dsimp [w]; abel
  rw [one_smul]
  change z • x=x
  conv_lhs => rw [hx]
  rw [show z • (w+α • u+β • v)=z • w+α • (z • u)+β • (z • v) from by
    change toLinear z (w+α • u+β • v)=_
    rw [map_add,map_add,map_smul,map_smul]
    rfl]
  rw [hzw,hzu,hzv,←hx]

private theorem commute_power_of_square_one {G : Type*} [Group G]
    (a b : G) (ha : a^2=1) (hb : b^2=1) (n : ℕ)
    (hz : ((a*b)^n)^2=1) : Commute ((a*b)^n) a ∧ Commute ((a*b)^n) b := by
  have hai : a⁻¹=a := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using ha)
  have hbi : b⁻¹=b := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hb)
  have hzi : ((a*b)^n)⁻¹=(a*b)^n := inv_eq_iff_mul_eq_one.mpr
    (by simpa only [pow_two] using hz)
  have hea : SemiconjBy a (a*b) (a*b)⁻¹ := by
    change a*(a*b)=(a*b)⁻¹*a
    rw [mul_inv_rev,hai,hbi]
    calc
      a*(a*b)=b := by rw [←mul_assoc,←pow_two,ha,one_mul]
      _ = (b*a)*a := by rw [mul_assoc,←pow_two,ha,mul_one]
  have heb : SemiconjBy b (a*b) (a*b)⁻¹ := by
    change b*(a*b)=(a*b)⁻¹*b
    rw [mul_inv_rev,hai,hbi,mul_assoc]
  constructor
  · have h := (hea.pow_right n).eq
    rw [inv_pow,hzi] at h
    exact h.symm
  · have h := (heb.pow_right n).eq
    rw [inv_pow,hzi] at h
    exact h.symm

/-- Noncommuting symplectic transvections have product of odd order. -/
theorem odd_order_product_of_isB1 [Finite F] (a b : Sp F)
    (ha : IsB1 a) (hb : IsB1 b) (hnc : ¬Commute a b) : Odd (orderOf (a*b)) := by
  obtain ⟨u,c,hu,hc,haform⟩ := rank_one_formula a ha
  obtain ⟨v,d,hv,hd,hbform⟩ := rank_one_formula b hb
  have huv : form F u v≠0 := fun hz => hnc
    (commute_of_zero_pairing a b u v c d haform hbform hz)
  by_contra hodd
  have htwo : 2∣orderOf (a*b) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  let n := orderOf (a*b)/2
  have ho : orderOf ((a*b)^n)=2 := orderOf_pow_orderOf_div (orderOf_pos (a*b)).ne' htwo
  have hz : ((a*b)^n)^2=1 := by simpa only [ho] using pow_orderOf_eq_one ((a*b)^n)
  have has : a^2=1 := by simpa only [ha.1] using pow_orderOf_eq_one a
  have hbs : b^2=1 := by simpa only [hb.1] using pow_orderOf_eq_one b
  obtain ⟨hza,hzb⟩ := commute_power_of_square_one a b has hbs n hz
  have he := power_eq_one_of_commute a b u v c d hu hv hc hd haform hbform huv n hza hzb
  rw [he,orderOf_one] at ho
  omega

/-- In an F-irreducible symplectic subgroup, all actual transvections are
conjugate by elements of that same subgroup. -/
theorem isConj_isB1_of_faithful_irreducible [Finite F]
    {H : Type*} [Group H] (ι : H →* Sp F) (hι : Function.Injective ι)
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp ι))
    (a b : H) (ha : IsB1 (ι a)) (hb : IsB1 (ι b)) : IsConj a b := by
  let ρ : Representation F H (Vector F) := (Representation.symplecticNatural 2).comp ι
  let : ρ.IsIrreducible := hi
  by_contra hnot
  have hcomm (h : H) : Commute b (h*a*h⁻¹) := by
    by_contra hn
    have hat : IsB1 (ι (h*a*h⁻¹)) := by
      simpa only [map_mul,map_inv] using (isB1_conj_iff (ι h) (ι a)).mpr ha
    have ho : Odd (orderOf (b*(h*a*h⁻¹))) := by
      rw [←orderOf_injective ι hι,map_mul]
      apply odd_order_product_of_isB1 _ _ hb hat
      intro he
      exact hn (hι (by simpa only [map_mul] using he.eq))
    have hs (x : H) (hx : IsB1 (ι x)) : x^2=1 := by
      apply hι
      simpa only [map_pow,map_one,hx.1] using pow_orderOf_eq_one (ι x)
    have hbc := isConj_of_involutions_odd_product b (h*a*h⁻¹) (hs b hb) (hs _ hat) ho
    exact hnot ((isConj_iff.mpr ⟨h,rfl⟩).trans hbc.symm)
  obtain ⟨u,c,hu,hc,haform⟩ := rank_one_formula (ι a) ha
  have hfix (h : H) : (ι b) • (ρ h u)=ρ h u := by
    change (ι b) • ((ι h) • u)=(ι h) • u
    have hh : Commute (h⁻¹*b*h) a := by
      have hm := (hcomm h).map (MulAut.conj h⁻¹).toMonoidHom
      simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,
        inv_mul_cancel,mul_inv_cancel,inv_mul_cancel_left,one_mul,mul_one] using hm
    have hf := fixes_center_of_commute (ι a) (ι (h⁻¹*b*h))
      u c hu hc haform (hh.map ι)
    have he := congrArg (fun x : Vector F => (ι h) • x) hf
    simpa only [map_mul,map_inv,mul_smul,smul_inv_smul,inv_smul_smul]
      using he
  have hspan := Representation.TraceFieldDescent.span_orbit_eq_top ρ u hu
  have hall (x : Vector F) : (ι b) • x=x := by
    have hx : x ∈ Submodule.span F (Set.range (fun h => ρ h u)) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨h,rfl⟩ := hx; exact hfix h
    | zero => exact (toLinear (ι b)).map_zero
    | add x y _ _ hx hy =>
      change toLinear (ι b) (x+y)=x+y
      rw [map_add,toLinear_apply,toLinear_apply,hx,hy]
    | smul c x _ hx =>
      change toLinear (ι b) (c • x)=c • x
      rw [map_smul,toLinear_apply,hx]
  have hb1 : (ι b)=1 := FaithfulSMul.eq_of_smul_eq_smul (α := Vector F)
    (fun x => (hall x).trans (one_smul _ _).symm)
  have ho := hb.1
  rw [hb1,orderOf_one] at ho
  omega

/-- Literal-subgroup version, retaining internal conjugacy. -/
theorem isConj_isB1_of_irreducible [Finite F] (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp H.subtype))
    (a b : H) (ha : IsB1 (a : Sp F)) (hb : IsB1 (b : Sp F)) : IsConj a b :=
  isConj_isB1_of_faithful_irreducible H.subtype H.subtype_injective hi a b ha hb

/-- Fusion inside the actual normal transvection closure, not merely in its
ambient pair. -/
theorem transvectionClosure_isConj [Finite F] (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible (((Representation.symplecticNatural 2).comp H.subtype).comp
      (transvectionClosure H).subtype))
    (a b : transvectionClosure H)
    (ha : IsB1 ((a : H) : Sp F)) (hb : IsB1 ((b : H) : Sp F)) : IsConj a b :=
  isConj_isB1_of_faithful_irreducible (H.subtype.comp (transvectionClosure H).subtype)
    (H.subtype_injective.comp (transvectionClosure H).subtype_injective) hi a b ha hb

/-- The same closure-fusion conclusion on the genuine moving-actor pair. -/
theorem moving_pair_transvectionClosure_isConj [Finite F]
    (hq : 2<Nat.card F) (a : EvenBorelTorus.ActorReduction.stabilizer (F:=F))
    (ha : ¬DiagramAutomorphisms.PreservesDiagram a.val)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hV : V.map a.val.toMonoidHom=V)
    (hc : V≤(center (unipotent (F:=F))).map (unipotent (F:=F)).subtype)
    (hr : 2<Nat.card V) (hex : ∃ h∈TwoConjugate.oppositePair V, IsB1 h)
    (s t : transvectionClosure (TwoConjugate.oppositePair V))
    (hs : IsB1 ((s : TwoConjugate.oppositePair V) : Sp F))
    (ht : IsB1 ((t : TwoConjugate.oppositePair V) : Sp F)) : IsConj s t :=
  transvectionClosure_isConj _
    (moving_pair_transvectionClosure_irreducible hq a ha V hV hc hr hex) s t hs ht

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
