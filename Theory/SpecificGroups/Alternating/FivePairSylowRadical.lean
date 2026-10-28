module
public import Theory.SpecificGroups.Alternating.FiveSylowRadical
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.Alternating.FivePairTorusAxes

/-!
# Normal two-actors preserving a Sylow subgroup of the A₅ pair

A marked order-nine torus in A₅ × A₅ has nontrivial cubic elements
supported on each coordinate. A normal two-actor cannot exchange the
coordinates: its commutator with one supported cubic would be a nontrivial
inner automorphism of order three. Restricting the acting group to its
factor-preserving subgroup then gives two actions preserving the actual
coordinate Sylow four-groups. In each factor the marked cubic and the
single-factor radical theorem force every normal two-actor to be inner.

The supported-cubic theorem exposes the precise local input. Its torus
consumer constructs that input using the two kernels of an injective
order-nine marking, preserving the original homomorphism throughout.
The source consumer is the literal Cartan/Sylow action in
Aschbacher--Smith, Lemma 9.3.2, printed p.733; its assembly supplies the
marking from the original component quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace Theory.SpecificGroups.Alternating.FivePairSylowRadical
local notation "A" => alternatingGroup (Fin 5)
local notation "Q" => A × A

private instance : IsQuasisimple A where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

private theorem center_pair : center Q = ⊥ := by
  have hA : center A = ⊥ := alternatingGroup.center_eq_bot (by norm_num)
  rw [Subgroup.center_prod,hA]
  ext x
  simp

private def base : (MulAut A × MulAut A) →* MulAut Q where
  toFun f := f.1.prodCongr f.2
  map_one' := by ext x <;> rfl
  map_mul' _ _ := rfl

private theorem base_injective : Function.Injective base := by
  intro f g h
  apply Prod.ext
  · apply MulEquiv.ext
    intro x
    exact congrArg Prod.fst (DFunLike.congr_fun h (x,1))
  · apply MulEquiv.ext
    intro x
    exact congrArg Prod.snd (DFunLike.congr_fun h (1,x))

private theorem inner_le_base : MulAut.innerSubgroup Q ≤ base.range := by
  rintro f ⟨x,rfl⟩
  exact ⟨(MulAut.conj x.1,MulAut.conj x.2),rfl⟩

private theorem inner_commutator (x : Q) (f : MulAut Q) :
    ⁅MulAut.conj x,f⁆ = MulAut.conj (x * (f x)⁻¹) := by
  apply MulEquiv.ext
  intro y
  change x * f (x⁻¹ * f⁻¹ y * x) * x⁻¹ =
    (x * (f x)⁻¹) * y * (x * (f x)⁻¹)⁻¹
  simp [map_mul,map_inv,mul_assoc]

private theorem pair_sylow_product (S : Sylow 2 Q) :
    ∃ S1 S2 : Sylow 2 A, (S : Subgroup Q) = (S1 : Subgroup A).prod (S2 : Subgroup A) := by
  let S1 := S.mapSurjective (f := MonoidHom.fst A A) (fun x => ⟨(x,1),rfl⟩)
  let S2 := S.mapSurjective (f := MonoidHom.snd A A) (fun x => ⟨(1,x),rfl⟩)
  have hp : IsPGroup 2 ((S1 : Subgroup A).prod (S2 : Subgroup A)) := by
    obtain ⟨n,hn⟩ := S1.isPGroup'.exists_card_eq
    obtain ⟨m,hm⟩ := S2.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := n+m) (by
      rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,hn,hm,pow_add])
  refine ⟨S1,S2,(S.is_maximal' hp ?_).symm⟩
  intro x hx
  exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩

variable {E : Type*} [Group E]

private theorem normal_two_preserves_factors (a : E →* MulAut Q) (R : Subgroup E) [R.Normal]
    (hR : IsPGroup 2 R) (d : E) (c : A) (hc : c ≠ 1) (hc3 : c^3=1)
    (hd : a d = MulAut.conj (c,1)) : R ≤ base.range.comap a := by
  intro r hr
  rcases AutomorphismSquare.normal_form (alternatingGroup.center_eq_bot (by simp)) (a r) with
    ⟨f,g,he⟩ | ⟨f,g,he⟩
  · exact ⟨(f,g),he.symm⟩
  · exfalso
    have hcommR : ⁅d,r⁆ ∈ R :=
      R.mul_mem ((inferInstance : R.Normal).conj_mem _ hr d) (R.inv_mem hr)
    have hcomm : a ⁅d,r⁆ = MulAut.conj (c,(g c)⁻¹) := by
      rw [map_commutatorElement,hd,inner_commutator,he]
      apply congrArg MulAut.conj
      change (c * (f 1)⁻¹,1 * (g c)⁻¹) = _
      simp
    have hthree : (a ⁅d,r⁆)^3=1 := by
      rw [hcomm,←map_pow]
      have hh : (c,(g c)⁻¹)^3=(1 : Q) := by
        apply Prod.ext
        · exact hc3
        · change ((g c)⁻¹)^3=1
          rw [inv_pow,←map_pow,hc3,map_one,inv_one]
      rw [hh,map_one]
    obtain ⟨n,hn⟩ := hR ⟨⁅d,r⁆,hcommR⟩
    have htwo : (a ⁅d,r⁆)^(2^n)=1 := by
      rw [←map_pow]
      exact (congrArg a (congrArg Subtype.val hn)).trans a.map_one
    have hone : a ⁅d,r⁆ = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow_left n)
        (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hthree))
    have hh : (c,(g c)⁻¹)=(1 : Q) := conj_injective_of_center_eq_bot center_pair
      ((hcomm.symm.trans hone).trans (map_one _).symm)
    exact hc (congrArg Prod.fst hh)

/-- Independently supported cubic inner actions exclude every outer normal two-actor. -/
theorem normal_two_action_inner_of_supported_cubics
    (S : Sylow 2 Q) (a : E →* MulAut Q)
    (hS : ∀ x, (S : Subgroup Q).map (a x).toMonoidHom = S)
    (D R : Subgroup E) [R.Normal] (hD : IsPPerfect 2 D) (hR : IsPGroup 2 R)
    (hi : ∀ d : D, a d ∈ MulAut.innerSubgroup Q)
    (d1 d2 : D) (c1 c2 : A) (hc1 : c1 ≠ 1) (hc2 : c2 ≠ 1) (hc3 : c1^3=1)
    (hd1 : a d1 = MulAut.conj (c1,1)) (hd2 : a d2 = MulAut.conj (1,c2)) :
    ∀ r : R, a r ∈ MulAut.innerSubgroup Q := by
  let E0 := base.range.comap a
  have hRE : R ≤ E0 := normal_two_preserves_factors a R hR d1 c1 hc1 hc3 hd1
  have hDE : D ≤ E0 := fun d hd => inner_le_base (hi ⟨d,hd⟩)
  let eqv := MonoidHom.ofInjective base_injective
  let a0 : E0 →* base.range := (a.comp E0.subtype).codRestrict _ (fun x => x.property)
  let b : E0 →* MulAut A × MulAut A := eqv.symm.toMonoidHom.comp a0
  let b1 := (MonoidHom.fst (MulAut A) (MulAut A)).comp b
  let b2 := (MonoidHom.snd (MulAut A) (MulAut A)).comp b
  have hb (x : E0) : (b1 x).prodCongr (b2 x) = a x :=
    congrArg Subtype.val (eqv.apply_symm_apply (a0 x))
  obtain ⟨S1,S2,hprod⟩ := pair_sylow_product S
  have hb1 (x : E0) : (S1 : Subgroup A).map (b1 x).toMonoidHom = S1 := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (b1 x).injective])
    rintro z ⟨y,hy,rfl⟩
    have hyS : (y,1) ∈ (S : Subgroup Q) := hprod ▸ ⟨hy,one_mem _⟩
    have hh := mem_map_of_mem (a x).toMonoidHom hyS
    rw [hS,hprod,←hb x] at hh
    exact hh.1
  have hb2 (x : E0) : (S2 : Subgroup A).map (b2 x).toMonoidHom = S2 := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (b2 x).injective])
    rintro z ⟨y,hy,rfl⟩
    have hyS : (1,y) ∈ (S : Subgroup Q) := hprod ▸ ⟨one_mem _,hy⟩
    have hh := mem_map_of_mem (a x).toMonoidHom hyS
    rw [hS,hprod,←hb x] at hh
    exact hh.2
  let D0 := D.subgroupOf E0
  let R0 := R.subgroupOf E0
  have hD0 : IsPPerfect 2 D0 := hD.of_surjective
    (subgroupOfEquivOfLe hDE).symm.toMonoidHom (subgroupOfEquivOfLe hDE).symm.surjective
  have hR0 : IsPGroup 2 R0 := hR.comap_subtype
  let x1 : D0 := ⟨⟨d1,hDE d1.property⟩,d1.property⟩
  let x2 : D0 := ⟨⟨d2,hDE d2.property⟩,d2.property⟩
  have hx1 : b1 x1 = MulAut.conj c1 := by
    apply MulEquiv.ext
    intro x
    have hh := DFunLike.congr_fun (hb x1) (x,1)
    rw [hd1] at hh
    exact congrArg Prod.fst hh
  have hx2 : b2 x2 = MulAut.conj c2 := by
    apply MulEquiv.ext
    intro x
    have hh := DFunLike.congr_fun (hb x2) (1,x)
    rw [hd2] at hh
    exact congrArg Prod.snd hh
  have hn1 : ∃ d : D0, b1 d ≠ 1 := by
    refine ⟨x1,fun hh => hc1 ?_⟩
    apply conj_injective_of_center_eq_bot (alternatingGroup.center_eq_bot (by simp))
    exact (hx1.symm.trans hh).trans (map_one _).symm
  have hn2 : ∃ d : D0, b2 d ≠ 1 := by
    refine ⟨x2,fun hh => hc2 ?_⟩
    apply conj_injective_of_center_eq_bot (alternatingGroup.center_eq_bot (by simp))
    exact (hx2.symm.trans hh).trans (map_one _).symm
  intro r
  let r0 : R0 := ⟨⟨r,hRE r.property⟩,r.property⟩
  obtain ⟨u,hu⟩ := FiveSylowRadical.normal_two_action_inner S1 b1 hb1 D0 R0 hD0 hR0 hn1 r0
  obtain ⟨v,hv⟩ := FiveSylowRadical.normal_two_action_inner S2 b2 hb2 D0 R0 hD0 hR0 hn2 r0
  refine ⟨(u,v),?_⟩
  rw [←hb r0,←hu,←hv]
  rfl

/-- A faithful marked order-nine torus supplies both supported cubic actions. -/
theorem normal_two_action_inner_of_marked_torus [Finite E]
    (S : Sylow 2 Q) (a : E →* MulAut Q)
    (hS : ∀ x, (S : Subgroup Q).map (a x).toMonoidHom = S)
    (D R : Subgroup E) [R.Normal] (hD : IsPGroup 3 D) (hD9 : Nat.card D = 9)
    (hR : IsPGroup 2 R) (q : D →* Q) (hq : Function.Injective q)
    (ha : ∀ d : D, a d = MulAut.conj (q d)) :
    ∀ r : R, a r ∈ MulAut.innerSubgroup Q := by
  let q1 := (MonoidHom.fst A A).comp q
  let q2 := (MonoidHom.snd A A).comp q
  obtain ⟨h1,h2,_,_⟩ := Theory.AlternatingFive.nine_torus_coordinate_kernels q hq hD hD9
  change Nat.card q1.ker = 3 at h1
  change Nat.card q2.ker = 3 at h2
  have hn1 : q1.ker ≠ ⊥ := by intro hh; rw [hh,card_bot] at h1; omega
  have hn2 : q2.ker ≠ ⊥ := by intro hh; rw [hh,card_bot] at h2; omega
  obtain ⟨d1,hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn2
  obtain ⟨d2,hd2⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn1
  have hc1 : (q d1).1 ≠ 1 := by
    intro hh
    apply hd1
    apply Subtype.ext
    apply hq
    change q (d1 : D) = q (1 : D)
    rw [map_one]
    exact Prod.ext hh d1.property
  have hc2 : (q d2).2 ≠ 1 := by
    intro hh
    apply hd2
    apply Subtype.ext
    apply hq
    change q (d2 : D) = q (1 : D)
    rw [map_one]
    exact Prod.ext d2.property hh
  have hc3 : (q d1).1 ^ 3 = 1 := by
    have hh : d1^3=1 := h2 ▸ pow_card_eq_one'
    have h := congrArg (fun x : q2.ker => (q x).1) hh
    simpa using h
  have hd1a : a (d1 : D) = MulAut.conj ((q d1).1,1) := by
    rw [ha]
    congr 1
    exact Prod.ext rfl d1.property
  have hd2a : a (d2 : D) = MulAut.conj (1,(q d2).2) := by
    rw [ha]
    congr 1
    exact Prod.ext d2.property rfl
  have hp : IsPPerfect 2 D := by
    intro N hn ht
    let := hn
    apply index_eq_one.mp
    change Nat.card (D ⧸ N) = 1
    apply ht.card_eq_or_dvd.resolve_right
    intro hd
    have hh := hd.trans N.card_quotient_dvd_card
    rw [hD9] at hh
    omega
  exact normal_two_action_inner_of_supported_cubics S a hS D R hp hR
    (fun d => ⟨q d,(ha d).symm⟩) d1 d2 (q d1).1 (q d2).2 hc1 hc2 hc3 hd1a hd2a

end Theory.SpecificGroups.Alternating.FivePairSylowRadical
