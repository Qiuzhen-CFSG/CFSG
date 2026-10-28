module
public import Theory.GroupTheory.ExtraspecialSquare
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# Lifting the square-form comparison to extraspecial groups

Form the pullback of the two groups over the identified central quotients.
The square-form equality puts every square in its diagonal center. Quotient
by that diagonal center is therefore elementary abelian. A complement to
the remaining central kernel lifts to the graph of a group isomorphism.
The resulting isomorphism induces the prescribed quadratic isometry.

This supplies the extraspecial lifting step needed in Aschbacher–Segev,
Invent. Math. 105 (1991), (8.3), p.606. A quotient-trivial cubic correction
makes the lift equivariant for an actual order-three actor. Full normalizer equivariance still requires the
separate matching-actor and correction arguments.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison.QuadraticLift
open Subgroup ExtraspecialSquare
open scoped IsMulCommutative Pointwise
variable {Q R : Type*} [Group Q] [Group R] [IsExtraspecial 2 Q] [IsExtraspecial 2 R]
variable (v : Space Q ≃ₗ[ZMod 2] Space R)
variable (hv : ∀ x, form R (v x) = form Q x)

private def quotientEquiv : (Q ⧸ center Q) ≃* (R ⧸ center R) :=
  v.toAddEquiv.toMultiplicative

private def pullback : Subgroup (Q × R) where
  carrier := {p | quotientEquiv v (QuotientGroup.mk' (center Q) p.1) =
    QuotientGroup.mk' (center R) p.2}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change quotientEquiv v (QuotientGroup.mk' (center Q) (a.1*b.1)) =
      QuotientGroup.mk' (center R) (a.2*b.2)
    rw [map_mul,map_mul,map_mul,ha,hb]
  inv_mem' {a} ha := by
    change quotientEquiv v (QuotientGroup.mk' (center Q) a.1⁻¹) =
      QuotientGroup.mk' (center R) a.2⁻¹
    rw [map_inv,map_inv,map_inv,ha]

private def fstHom : pullback v →* Q := (MonoidHom.fst Q R).comp (pullback v).subtype
private def sndHom : pullback v →* R := (MonoidHom.snd Q R).comp (pullback v).subtype

private theorem fst_surjective : Function.Surjective (fstHom v) := by
  intro x
  obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (center R)
    (quotientEquiv v (QuotientGroup.mk' (center Q) x))
  exact ⟨⟨(x,y),hy.symm⟩,rfl⟩

private noncomputable def centerEquiv : center Q ≃* center R :=
  (centerCoordinate Q).trans (centerCoordinate R).symm

private noncomputable def diagonalHom : center Q →* pullback v where
  toFun c := ⟨(c.val,(centerEquiv (Q := Q) (R := R) c).val),by
    change quotientEquiv v (QuotientGroup.mk c.val) = QuotientGroup.mk _
    rw [(QuotientGroup.eq_one_iff _).mpr c.property,map_one,
      (QuotientGroup.eq_one_iff _).mpr (centerEquiv (Q := Q) (R := R) c).property]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

private noncomputable abbrev diagonal : Subgroup (pullback v) := (diagonalHom v).range

private theorem diagonal_central : diagonal v ≤ center (pullback v) := by
  rintro _ ⟨c,rfl⟩
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact Prod.ext (mem_center_iff.mp c.property x.val.1)
    (mem_center_iff.mp (centerEquiv (Q := Q) (R := R) c).property x.val.2)

private instance diagonal_normal : (diagonal v).Normal :=
  ⟨fun x hx g => by
    rw [mem_center_iff.mp (diagonal_central v hx) g,mul_inv_cancel_right]
    exact hx⟩

include hv in
private theorem square_diagonal (x : pullback v) : x^2 ∈ diagonal v := by
  let c : center Q := ⟨x.val.1^2,IsExtraspecial.square_mem_center _⟩
  refine ⟨c,Subtype.ext (Prod.ext rfl ?_)⟩
  have he := hv (Additive.ofMul (QuotientGroup.mk' (center Q) x.val.1))
  have hx : v (Additive.ofMul (QuotientGroup.mk' (center Q) x.val.1)) =
    Additive.ofMul (QuotientGroup.mk' (center R) x.val.2) := x.property
  rw [hx,form_mk,form_mk] at he
  have he' : centerCoordinate R ⟨x.val.2^2,IsExtraspecial.square_mem_center _⟩ =
      centerCoordinate Q c := congrArg Multiplicative.ofAdd he
  have hc : centerEquiv (Q := Q) (R := R) c =
      ⟨x.val.2^2,IsExtraspecial.square_mem_center _⟩ := by
    apply (centerCoordinate R).injective
    exact ((centerCoordinate R).apply_symm_apply _).trans he'.symm
  exact congrArg Subtype.val hc

include hv in
private theorem quotient_elementary : IsElementaryAbelian 2 (pullback v ⧸ diagonal v) := by
  have hs : ∀ x : pullback v ⧸ diagonal v, x^2=1 := by
    intro x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (diagonal v) x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (square_diagonal v hv x)
  exact {
    toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

private theorem fst_ker_disjoint : Disjoint (fstHom v).ker (diagonal v) := by
  apply Subgroup.disjoint_def.mpr
  rintro x hx ⟨c,rfl⟩
  have hc : c = 1 := Subtype.ext hx
  rw [hc,map_one]

private theorem snd_ker_in_fst_diagonal (x : pullback v) (hx : sndHom v x = 1) :
    ∃ b ∈ (fstHom v).ker, ∃ d ∈ diagonal v, x = b*d := by
  have hc : x.val.1 ∈ center Q := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply (quotientEquiv v).injective
    rw [map_one]
    exact x.property.trans (by rw [show x.val.2 = 1 from hx]; rfl)
  let d := diagonalHom v ⟨x.val.1,hc⟩
  refine ⟨x*d⁻¹,?_,d,⟨_,rfl⟩,by group⟩
  change fstHom v (x*d⁻¹) = 1
  rw [map_mul,map_inv]
  exact mul_inv_cancel _

private theorem snd_diagonal_disjoint : Disjoint (sndHom v).ker (diagonal v) := by
  apply Subgroup.disjoint_def.mpr
  rintro x hx ⟨c,rfl⟩
  have hc : centerEquiv (Q := Q) (R := R) c = 1 := Subtype.ext hx
  have hc' : c = 1 := (centerEquiv (Q := Q) (R := R)).map_eq_one_iff.mp hc
  rw [hc',map_one]

include hv in
/-- An isometry of the square forms lifts to an isomorphism of the original
extraspecial groups, on their literal central quotients. -/
theorem exists_equiv [Finite Q] [Finite R] :
    ∃ e : Q ≃* R, ∀ x, Additive.ofMul (QuotientGroup.mk' (center R) (e x)) =
      v (Additive.ofMul (QuotientGroup.mk' (center Q) x)) := by
  let := quotient_elementary v hv
  let q := QuotientGroup.mk' (diagonal v)
  let B := (fstHom v).ker.map q
  obtain ⟨C,hC⟩ := IsElementaryAbelian.exists_isCompl 2 (pullback v ⧸ diagonal v) B
  let S := C.comap q
  let f := (fstHom v).comp S.subtype
  let g := (sndHom v).comp S.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hb : q x.val ∈ B := mem_map_of_mem q hx
    have hq : q x.val = 1 := Subgroup.disjoint_def.mp hC.disjoint hb x.property
    have hxd : x.val ∈ diagonal v := (QuotientGroup.eq_one_iff _).mp hq
    exact Subtype.ext (Subgroup.disjoint_def.mp (fst_ker_disjoint v) hx hxd)
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨r,hr⟩ := fst_surjective v x
    have ht : q r ∈ B ⊔ C := hC.sup_eq_top ▸ mem_top _
    obtain ⟨b,hb,c,hc,hbc⟩ := mem_sup_of_normal_left.mp ht
    obtain ⟨b,hb,rfl⟩ := hb
    have hs : b⁻¹*r ∈ S := by
      change q (b⁻¹*r) ∈ C
      rw [map_mul,map_inv,←hbc,inv_mul_cancel_left]
      exact hc
    refine ⟨⟨b⁻¹*r,hs⟩,?_⟩
    change fstHom v (b⁻¹*r) = x
    rw [map_mul,map_inv,show fstHom v b = 1 from hb,inv_one,one_mul,hr]
  have hg : Function.Injective g := by
    apply (injective_iff_map_eq_one g).mpr
    intro x hx
    obtain ⟨b,hb,d,hdd,hbd⟩ := snd_ker_in_fst_diagonal v x.val hx
    have hq : q x.val = q b := by
      rw [hbd,map_mul,show q d = 1 from (QuotientGroup.eq_one_iff _).mpr hdd,mul_one]
    have hbq : q x.val ∈ B := hq ▸ mem_map_of_mem q hb
    have he : q x.val = 1 := Subgroup.disjoint_def.mp hC.disjoint hbq x.property
    exact Subtype.ext (Subgroup.disjoint_def.mp (snd_diagonal_disjoint v) hx
      ((QuotientGroup.eq_one_iff _).mp he))
  have hcard : Nat.card Q = Nat.card R := by
    rw [←(center Q).card_mul_index,←(center R).card_mul_index,
      IsExtraspecial.center_order_p 2 Q,IsExtraspecial.center_order_p 2 R,
      index_eq_card,index_eq_card,Nat.card_congr (quotientEquiv v).toEquiv]
  let ef : S ≃* Q := MulEquiv.ofBijective f ⟨hf,hfs⟩
  have hgs : Function.Surjective g :=
    ((Nat.bijective_iff_injective_and_card g).mpr
      ⟨hg,(Nat.card_congr ef.toEquiv).trans hcard⟩).2
  let eg : S ≃* R := MulEquiv.ofBijective g ⟨hg,hgs⟩
  refine ⟨ef.symm.trans eg,fun x => ?_⟩
  have he := (ef.symm x).val.property
  have hf' : (ef.symm x).val.val.1 = x := ef.apply_symm_apply x
  change quotientEquiv v (QuotientGroup.mk' (center Q) (ef.symm x).val.val.1) =
    QuotientGroup.mk' (center R) (ef.symm x).val.val.2 at he
  rw [hf'] at he
  exact he.symm


private theorem automorphism_kernel_square {P : Type*} [Group P] [Finite P]
    [IsExtraspecial 2 P] (a : MulAut P) (ha : quotientAut (center P) a = 1) : a^2 = 1 := by
  obtain ⟨x,rfl⟩ := (IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 2)).le ha
  rw [← map_pow]
  apply MulEquiv.ext
  intro y
  change x^2*y*(x^2)⁻¹=y
  rw [← mem_center_iff.mp (IsExtraspecial.square_mem_center x) y,mul_inv_cancel_right]

private theorem cubic_kernel_conjugator {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hk : ∀ a, f a = 1 → a^2=1)
    (a b : A) (ha : a^3=1) (hb : b^3=1) (he : f a = f b) :
    f (a*b*a)=1 ∧ (a*b*a)*a*(a*b*a)⁻¹=b := by
  have hk' : f (a*b*a)=1 := by
    simpa only [map_mul,←he,pow_succ,pow_zero,one_mul,map_one] using congrArg f ha
  have hd := hk (a*b⁻¹) (by simp [he])
  have hh := hk _ hk'
  have hi : (a*b*a)⁻¹=a*b*a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hh)
  have hbi : b^2=b⁻¹ := by
    apply mul_right_cancel (b := b)
    simpa only [←pow_succ,inv_mul_cancel] using hb
  have hd' : a*b⁻¹*a=b := by
    apply mul_right_cancel (b := b⁻¹)
    simpa only [pow_two,mul_assoc,mul_inv_cancel] using hd
  refine ⟨hk',?_⟩
  calc
    _ = a*b*(a^3)*b*a := by rw [hi]; simp only [pow_succ,pow_zero,one_mul,mul_assoc]
    _ = a*(b^2)*a := by simp only [ha,mul_one,pow_two,mul_assoc]
    _ = b := by rw [hbi,hd']

include hv in
/-- The prescribed quadratic isometry lifts equivariantly for a pair of
matching cubic actors; the correction remains trivial on the central quotient. -/
theorem exists_equiv_cubic [Finite Q] [Finite R]
    (a : MulAut Q) (b : MulAut R) (ha : a^3=1) (hb : b^3=1)
    (he : ∀ x, v (linearAction Q a x) = linearAction R b (v x)) :
    ∃ e : Q ≃* R,
      (∀ x, Additive.ofMul (QuotientGroup.mk' (center R) (e x)) =
        v (Additive.ofMul (QuotientGroup.mk' (center Q) x))) ∧
      ∀ x, e (a x) = b (e x) := by
  obtain ⟨e,heq⟩ := exists_equiv v hv
  let a' := MulAut.congr e a
  let f := quotientAut (center R)
  have he' : f a' = f b := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center R) x
    obtain ⟨x,rfl⟩ := e.surjective x
    apply Additive.ofMul.injective
    rw [quotientAut_apply_mk,quotientAut_apply_mk]
    simp only [a',MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
    change Additive.ofMul (QuotientGroup.mk' (center R) (e (a x))) = _
    rw [heq]
    have hh := he (Additive.ofMul (QuotientGroup.mk' (center Q) x))
    rw [←heq] at hh
    simpa only [linearAction_apply,quotientAut_apply_mk] using hh
  have ha' : a'^3=1 := by change (MulAut.congr e a)^3=1; rw [←map_pow,ha,map_one]
  obtain ⟨hk,hconj⟩ := cubic_kernel_conjugator f (automorphism_kernel_square) a' b ha' hb he'
  let k := a'*b*a'
  refine ⟨e.trans k,?_,?_⟩
  · intro x
    have hh := MulEquiv.congr_fun hk (QuotientGroup.mk' (center R) (e x))
    rw [quotientAut_apply_mk] at hh
    exact (congrArg Additive.ofMul hh).trans (heq x)
  · intro x
    have hm : k*a'=b*k := (mul_inv_eq_iff_eq_mul).mp hconj
    have hh := MulEquiv.congr_fun hm (e x)
    simpa only [MulAut.mul_apply,a',MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hh

include hv in
/-- A prescribed square-form comparison lifts for an actual actor of order three. -/
theorem exists_equiv_threeAction [Finite Q] [Finite R]
    {A : Type*} [Group A] [Finite A] (hA : Nat.card A = 3)
    (ρ : A →* MulAut Q) (σ : A →* MulAut R)
    (he : ∀ a x, v (linearAction Q (ρ a) x) = linearAction R (σ a) (v x)) :
    ∃ e : Q ≃* R,
      (∀ x, Additive.ofMul (QuotientGroup.mk' (center R) (e x)) =
        v (Additive.ofMul (QuotientGroup.mk' (center Q) x))) ∧
      ∀ a x, e (ρ a x) = σ a (e x) := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a,ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic A)
  have ha3 : a^3=1 := hA ▸ pow_card_eq_one' (x := a)
  obtain ⟨e,heq,hec⟩ := exists_equiv_cubic v hv (ρ a) (σ a)
    (by rw [←map_pow,ha3,map_one]) (by rw [←map_pow,ha3,map_one]) (he a)
  have hec' : MulAut.congr e (ρ a) = σ a := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x,rfl⟩ := e.surjective x
    simpa only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hec x
  refine ⟨e,heq,fun b x => ?_⟩
  obtain ⟨n,rfl⟩ := ha.ge (mem_top b)
  have hpow : MulAut.congr e (ρ (a^n)) = σ (a^n) := by
    rw [map_zpow,map_zpow,hec',map_zpow]
  have hh := MulEquiv.congr_fun hpow (e x)
  simpa only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hh


/-- A quotient-trivial extraspecial automorphism commuting with an actor
having no nonzero fixed quotient vector is the identity. -/
theorem quotient_trivial_of_commute_fixedFree [Finite R]
    {A : Type*} (σ : A → MulAut R)
    (hfix : ∀ x : R ⧸ center R, (∀ a, quotientAut (center R) (σ a) x = x) → x = 1)
    (d : MulAut R) (hd : quotientAut (center R) d = 1)
    (hc : ∀ a, Commute d (σ a)) : d = 1 := by
  obtain ⟨r,rfl⟩ := (IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 2)).le hd
  have hr : r ∈ center R := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply hfix
    intro a
    have hh : MulAut.conj (σ a r) = MulAut.conj r := by
      apply MulEquiv.ext
      intro x
      have he := MulEquiv.congr_fun (hc a).eq ((σ a).symm x)
      simpa only [MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,
        MulEquiv.apply_symm_apply] using he.symm
    have h1 : MulAut.conj (σ a r * r⁻¹) = 1 := by
      rw [map_mul,map_inv,hh,mul_inv_cancel]
    have hz : σ a r * r⁻¹ ∈ center R := by
      apply mem_center_iff.mpr
      intro x
      have he := MulEquiv.congr_fun h1 x
      exact ((mul_inv_eq_iff_eq_mul).mp he).symm
    change quotientAut (center R) (σ a) (QuotientGroup.mk' (center R) r) =
      QuotientGroup.mk' (center R) r
    rw [quotientAut_apply_mk]
    apply mul_inv_eq_one.mp
    rw [←map_inv,←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hz
  apply MulEquiv.ext
  intro x
  change r*x*r⁻¹=x
  rw [←mem_center_iff.mp hr x,mul_inv_cancel_right]

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison.QuadraticLift
