module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AmbientFusion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicTorus
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.PrimePowerCosetReplacement
public import Theory.GroupTheory.PrimePowerDecomposition

/-!
# Full four-group normalizer actions and the marked cubic torus rotation

Every pair of distinct commuting involutions a,b admits an ambient
conjugator fixing a and sending b to ab. Transport a to the marked central
involution. Inside H, multiplication by that involution preserves both the
noncentral quaternion-core class and the outside involution class. The
previous fusion results, proved from the actual marked H and M, supply
the desired conjugator in each case.

The resulting transpositions generate all six automorphisms of every
Klein four subgroup. For the original common cubic torus, its centralizer
has order prime to three: an element of order three centralizing the
outer involution has trivial action on both quaternion-axis triples,
hence lies in the order32 quaternion core, a contradiction. Thus the
three-cycle of the torus lifts to an actual element of order three,
with its action on the original marked involutions retained.

This proves the normalizer-action assertion of Fong–Wong §3A and the
three-power rotation used before §4A, specialized to q=3, and strengthens
the latter to an order-three rotation. Source: Nagoya Math. J.36 (1969),
pp.155,163; Aschbacher–Smith I.4.5, printed p.417. It does not use §4D's
q>3 orbit inequality, which fails at q=3. The Sylow-nine and order27-core
exclusions, BN-pair construction and Atlas model comparison remain with
`qt-i45-g2-recognition`. `Chapter14TorusFusion` applies this family to the
original SourceLocalData and retains the original factor markings.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

private theorem involution_line_cases {z x : c.H} (hz : orderOf z = 2)
    (hx : x ∈ zpowers z) : x = 1 ∨ x = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hz] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

/-- Multiplication by the marked central involution preserves each noncentral involution class in H. -/
theorem marked_involution_product_conjugate (z x : c.H)
    (hz : orderOf z = 2) (hline : zpowers z = c.H₁ ⊓ c.H₂)
    (hH : c.H = centralizer ({(z:G)} : Set G))
    (hx : orderOf x = 2) (hxz : x ≠ z) : IsConj x (z*x) := by
  have hzZ : z ∈ center c.H := mem_center_iff.mpr fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hH ▸ y.property))
  have hzz : z*z=1 := by simpa only [pow_two,hz] using pow_orderOf_eq_one z
  have hxx : x*x=1 := by simpa only [pow_two,hx] using pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by intro he; simp [he] at hx
  have hzx1 : z*x ≠ 1 := by
    intro he
    have hh := congrArg (fun y => z*y) he
    rw [←mul_assoc,hzz,one_mul,mul_one] at hh
    exact hxz hh
  have hzx : orderOf (z*x)=2 := orderOf_eq_prime (by
    have hc : Commute z x := (mem_center_iff.mp hzZ x).symm
    rw [hc.mul_pow,pow_two,pow_two,hzz,hxx,one_mul]) hzx1
  have hzK : z ∈ c.H₁ ⊔ c.H₂ := mem_sup_left ((hline ▸ mem_zpowers z).1)
  by_cases hxK : x ∈ c.H₁ ⊔ c.H₂
  · have hxQ := residual_involution_mem_core c x hx hxK
    have hzxQ := residual_involution_mem_core c (z*x) hzx ((c.H₁⊔c.H₂).mul_mem hzK hxK)
    have hnc (y : c.H) (hyQ : y ∈ quaternionCore c) (hy1 : y ≠ 1) (hyz : y ≠ z) :
        (⟨y,hyQ⟩ : quaternionCore c) ∉ center (quaternionCore c) := by
      intro hy
      have hm : y ∈ zpowers z := by
        rw [hline,←quaternionCore_center c]
        exact mem_map_of_mem (quaternionCore c).subtype hy
      exact (involution_line_cases c hz hm).elim hy1 hyz
    exact core_noncentral_involutions_conjugate c ⟨x,hxQ⟩ ⟨z*x,hzxQ⟩
      ((orderOf_coe _).symm.trans hx) (hnc x hxQ hx1 hxz)
      ((orderOf_coe _).symm.trans hzx) (hnc (z*x) hzxQ hzx1 (by simpa using hx1))
  · apply outside_involutions_conjugate c x (z*x) hx hxK hzx
    intro hh
    exact hxK ((c.H₁⊔c.H₂).mul_mem_cancel_left hzK |>.mp hh)

include c in
/-- A conjugator fixes one of two commuting involutions and exchanges the other two points of their four-group. -/
theorem commuting_involution_swap (a b : G) (ha : orderOf a=2) (hb : orderOf b=2)
    (hab : Commute a b) (hne : a ≠ b) :
    ∃ g : G, MulAut.conj g a=a ∧ MulAut.conj g b=a*b := by
  obtain ⟨z,hz,hline,hH⟩ := exists_marked_involution c
  obtain ⟨u,hu⟩ := isConj_iff.mp (marked_involution_fuses_ambient c z
    ((orderOf_coe z).trans hz) hH a ha).symm
  let e := MulAut.conj u
  have hea : e a=(z:G) := hu
  have hecomm : Commute (z:G) (e b) := hea ▸ hab.map e.toMonoidHom
  have hebH : e b ∈ c.H := hH.symm ▸ mem_centralizer_singleton_iff.mpr hecomm.symm
  let x : c.H := ⟨e b,hebH⟩
  have hx : orderOf x=2 := (orderOf_coe _).symm.trans ((e.orderOf_eq b).trans hb)
  have hxz : x ≠ z := by
    intro he
    exact hne (e.injective (hea.trans (congrArg Subtype.val he).symm))
  obtain ⟨v,hv⟩ := isConj_iff.mp (marked_involution_product_conjugate c z x hz hline hH hx hxz)
  have hva : MulAut.conj (v:G) (z:G)=(z:G) := by
    apply mul_inv_eq_iff_eq_mul.mpr
    exact mem_centralizer_singleton_iff.mp (hH ▸ v.property)
  have hvb : MulAut.conj (v:G) (e b)=(z:G)*e b := congrArg Subtype.val hv
  refine ⟨u⁻¹*(v:G)*u,?_,?_⟩
  · apply e.injective
    change u*((u⁻¹*(v:G)*u)*a*(u⁻¹*(v:G)*u)⁻¹)*u⁻¹=u*a*u⁻¹
    calc
      _ = (v:G)*(u*a*u⁻¹)*(v:G)⁻¹ := by group
      _ = u*a*u⁻¹ := by change MulAut.conj (v:G) (e a)=e a; rwa [hea]
  · apply e.injective
    change u*((u⁻¹*(v:G)*u)*b*(u⁻¹*(v:G)*u)⁻¹)*u⁻¹=u*(a*b)*u⁻¹
    calc
      _ = (v:G)*(u*b*u⁻¹)*(v:G)⁻¹ := by group
      _ = (u*a*u⁻¹)*(u*b*u⁻¹) := by
        change MulAut.conj (v:G) (e b)=(e a)*(e b)
        rwa [hea]
      _ = _ := by group

omit [Finite G] in
private theorem four_cases (D : Subgroup G) [IsKleinFour D]
    (a b x : D) (ha : a≠1) (hb : b≠1) (hab : a≠b) :
    x=1 ∨ x=a ∨ x=b ∨ x=a*b := by
  by_cases h1 : x=1
  · exact Or.inl h1
  by_cases h2 : x=a
  · exact Or.inr (Or.inl h2)
  by_cases h3 : x=b
  · exact Or.inr (Or.inr (Or.inl h3))
  exact Or.inr (Or.inr (Or.inr (IsKleinFour.eq_mul_of_ne_all ha hb hab h1 h2 h3)))

include c in
private theorem four_swap (D : Subgroup G) [IsKleinFour D]
    (a b : D) (ha : a≠1) (hb : b≠1) (hab : a≠b) :
    ∃ f ∈ D.normalizerMonoidHom.range, f a=a ∧ f b=a*b ∧ orderOf f=2 := by
  have ha2 : orderOf (a:G)=2 := (orderOf_coe a).trans
    (orderOf_eq_prime (by simpa only [pow_two] using IsKleinFour.mul_self a) ha)
  have hb2 : orderOf (b:G)=2 := (orderOf_coe b).trans
    (orderOf_eq_prime (by simpa only [pow_two] using IsKleinFour.mul_self b) hb)
  let : IsMulCommutative D := IsKleinFour.isMulCommutative
  have hc : Commute (a:G) (b:G) := congrArg Subtype.val (mul_comm' a b)
  obtain ⟨g,hga,hgb⟩ := commuting_involution_swap c a b ha2 hb2 hc
    (fun he => hab (Subtype.ext he))
  have hN : g ∈ normalizer (D:Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro x ⟨y,hy,rfl⟩
      change MulAut.conj g y ∈ D
      rcases four_cases D a b ⟨y,hy⟩ ha hb hab with h|h|h|h
      · have he : y=1 := congrArg Subtype.val h
        simp only [he,map_one,one_mem]
      · have he : y=(a:G) := congrArg Subtype.val h
        simpa only [he,hga] using a.property
      · have he : y=(b:G) := congrArg Subtype.val h
        simpa only [he,hgb] using D.mul_mem a.property b.property
      · have he : y=(a:G)*(b:G) := congrArg Subtype.val h
        rw [he,map_mul,hga,hgb]
        exact D.mul_mem a.property (D.mul_mem a.property b.property)
    · exact le_of_eq (Nat.card_congr (D.equivMapOfInjective
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv)
  let f := D.normalizerMonoidHom ⟨g,hN⟩
  have hfa : f a=a := Subtype.ext hga
  have hfb : f b=a*b := Subtype.ext hgb
  refine ⟨f,⟨⟨g,hN⟩,rfl⟩,hfa,hfb,orderOf_eq_prime ?_ ?_⟩
  · apply MulEquiv.ext
    intro x
    change f (f x)=x
    rcases four_cases D a b x ha hb hab with rfl|rfl|rfl|rfl
    · simp only [map_one]
    · rw [hfa,hfa]
    · rw [hfb,map_mul,hfa,hfb,←mul_assoc,IsKleinFour.mul_self,one_mul]
    · rw [map_mul,hfa,hfb,←mul_assoc,IsKleinFour.mul_self,one_mul,hfb]
  · intro he
    have hh : b=a*b := by rw [he] at hfb; exact hfb
    exact ha (mul_right_cancel (hh.symm.trans (one_mul b).symm))

include c in
/-- Every automorphism of an actual Klein four subgroup is induced by ambient conjugation. -/
theorem kleinFour_normalizer_action_surjective (D : Subgroup G) [IsKleinFour D] :
    Function.Surjective D.normalizerMonoidHom := by
  classical
  let : Fintype D := Fintype.ofFinite D
  obtain ⟨u,v,w,huv,huw,hvw⟩ := Fintype.two_lt_card_iff.mp
    (by rw [IsKleinFour.card_four']; decide : 2 < Fintype.card D)
  let a := u⁻¹*v
  let b := u⁻¹*w
  have ha : a≠1 := by
    intro he
    apply huv
    calc
      u = u*a := by rw [he,mul_one]
      _ = v := by dsimp [a]; group
  have hb : b≠1 := by
    intro he
    apply huw
    calc
      u = u*b := by rw [he,mul_one]
      _ = w := by dsimp [b]; group
  have hab : a≠b := fun he => hvw (mul_left_cancel he)
  obtain ⟨f,hf,hfa,_,hfo⟩ := four_swap c D a b ha hb hab
  obtain ⟨g,hg,_,hga,hgo⟩ := four_swap c D b a hb ha hab.symm
  have hfg : f≠g := by
    intro he
    rw [he,hga] at hfa
    exact hb (mul_right_cancel (hfa.trans (one_mul a).symm))
  let R := D.normalizerMonoidHom.range
  let ff : R := ⟨f,hf⟩
  let gg : R := ⟨g,hg⟩
  have hff : orderOf ff=2 := (orderOf_coe ff).symm.trans hfo
  have hgg : orderOf gg=2 := (orderOf_coe gg).symm.trans hgo
  have hf1 : ff≠1 := by intro he; simp [he] at hff
  have hg1 : gg≠1 := by intro he; simp [he] at hgg
  have hne : ff≠gg := fun he => hfg (congrArg Subtype.val he)
  have hgt : 2 < Nat.card R := by
    let : Fintype R := Fintype.ofFinite R
    rw [Nat.card_eq_fintype_card]
    exact Fintype.two_lt_card_iff.mpr ⟨1,ff,gg,hf1.symm,hg1.symm,hne⟩
  have hd : Nat.card R ∣ 6 := IsKleinFour.card_mulAut D ▸ R.card_subgroup_dvd_card
  have heven : 2 ∣ Nat.card R := hff ▸ orderOf_dvd_natCard ff
  have hcard : Nat.card R=6 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
    have hcases : Nat.card R=4 ∨ Nat.card R=6 := by omega
    rcases hcases with h|h
    · rw [h] at hd
      norm_num at hd
    · exact h
  have htop : R=⊤ := eq_top_of_card_eq R (hcard.trans (IsKleinFour.card_mulAut D).symm)
  exact MonoidHom.range_eq_top.mp htop

include c in
/-- The full ambient normalizer has index six over its pointwise centralizer. -/
theorem kleinFour_normalizer_centralizer_index (D : Subgroup G) [IsKleinFour D] :
    (centralizer (D:Set G)).relIndex (normalizer (D:Set G))=6 := by
  change ((centralizer (D:Set G)).subgroupOf (normalizer (D:Set G))).index=6
  rw [←normalizerMonoidHom_ker,index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective D.normalizerMonoidHom
      (kleinFour_normalizer_action_surjective c D)).toEquiv,IsKleinFour.card_mulAut]

include c in
/-- A three-power element induces the prescribed rotation of an actual four-group. -/
theorem kleinFour_three_rotation (D : Subgroup G) [IsKleinFour D]
    (a b : D) (ha : a≠1) (hb : b≠1) (hab : a≠b) :
    ∃ (g : G) (k : ℕ), g^(3^k)=1 ∧ g ∈ normalizer (D:Set G) ∧
      MulAut.conj g (a:G)=(b:G) ∧ MulAut.conj g (b:G)=(a:G)*(b:G) := by
  let : IsMulCommutative D := IsKleinFour.isMulCommutative
  obtain ⟨f,_,hfa,hfb,_⟩ := four_swap c D a b ha hb hab
  obtain ⟨h,_,hhb,hha,_⟩ := four_swap c D b a hb ha hab.symm
  let r := f*h
  have hra : r a=b := by
    change f (h a)=b
    rw [hha,map_mul,hfb,hfa,mul_assoc,mul_comm' b a,←mul_assoc,IsKleinFour.mul_self,one_mul]
  have hrb : r b=a*b := by change f (h b)=a*b; rw [hhb,hfb]
  have hrab : r (a*b)=a := by
    rw [map_mul,hra,hrb,mul_comm' a b,←mul_assoc,IsKleinFour.mul_self,one_mul]
  have hr3 : r^3=1 := by
    apply MulEquiv.ext
    intro x
    change r (r (r x))=x
    rcases four_cases D a b x ha hb hab with rfl|rfl|rfl|rfl
    · simp only [map_one]
    · rw [hra,hrb,hrab]
    · rw [hrb,hrab,hra]
    · rw [hrab,hra,hrb]
  obtain ⟨g,hg⟩ := kleinFour_normalizer_action_surjective c D r
  obtain ⟨k,m,hm,hpow⟩ := exists_primary_power 3 Nat.prime_three g
  have hcop : Nat.Coprime m (orderOf r) :=
    hm.symm.of_dvd_right (orderOf_dvd_of_pow_eq_one hr3)
  obtain ⟨s,hs⟩ := exists_pow_eq_self_of_coprime hcop
  let v := (g^m)^s
  have hv : D.normalizerMonoidHom v=r := by simpa only [v,map_pow,hg] using hs
  refine ⟨v,k,?_,v.property,?_,?_⟩
  · change (((g:G)^m)^s)^(3^k)=1
    have hpow' : ((g:G)^m)^(3^k)=1 := congrArg Subtype.val (hpow ▸ pow_orderOf_eq_one (g^m))
    rw [←pow_mul,Nat.mul_comm s,pow_mul,hpow',one_pow]
  · exact congrArg (fun j : MulAut D => (j a:G)) hv |>.trans (congrArg Subtype.val hra)
  · exact congrArg (fun j : MulAut D => (j b:G)) hv |>.trans (congrArg Subtype.val hrb)

namespace CubicTorus
variable {c} (t : CubicTorus c)

omit [Finite G] in
/-- The original torus remains a Klein four under its literal ambient inclusion. -/
theorem ambient_torus_kleinFour : IsKleinFour (t.torus.map c.H.subtype) := by
  let : IsKleinFour t.torus := t.torus_kleinFour
  let e := t.torus.equivMapOfInjective c.H.subtype c.H.subtype_injective
  exact {
    card_four := (Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans IsKleinFour.exponent_two }

/-- The marked torus has the full six-element ambient automorphism action. -/
theorem ambient_torus_normalizer_index :
    (Subgroup.centralizer (t.torus.map c.H.subtype : Set G)).relIndex
      (normalizer (t.torus.map c.H.subtype : Set G))=6 := by
  let := t.ambient_torus_kleinFour
  exact kleinFour_normalizer_centralizer_index c _

/-- A three-power actor rotates the original central and outer involutions. -/
theorem exists_three_rotation :
    ∃ (g : G) (k : ℕ), g^(3^k)=1 ∧
      g ∈ normalizer (t.torus.map c.H.subtype : Set G) ∧
      MulAut.conj g (t.z:G)=(t.n:G) ∧
      MulAut.conj g (t.n:G)=(t.z:G)*(t.n:G) := by
  let D := t.torus.map c.H.subtype
  let : IsKleinFour D := t.ambient_torus_kleinFour
  have hzD : (t.z:G) ∈ D := mem_map_of_mem c.H.subtype
    (mem_sup_left (mem_zpowers t.z))
  have hnD : (t.n:G) ∈ D := mem_map_of_mem c.H.subtype
    (mem_sup_right (mem_zpowers t.n))
  let a : D := ⟨t.z,hzD⟩
  let b : D := ⟨t.n,hnD⟩
  have ha : a≠1 := by
    intro he
    have hh : t.z=1 := Subtype.ext (congrArg (fun q : D => (q:G)) he)
    have hz := t.z_order
    simp [hh] at hz
  have hb : b≠1 := by
    intro he
    have hh : t.n=1 := Subtype.ext (congrArg (fun q : D => (q:G)) he)
    have hn := t.n_order
    simp [hh] at hn
  have hab : a≠b := by
    intro he
    have hh : t.z=t.n := Subtype.ext (congrArg (fun q : D => (q:G)) he)
    apply t.outside
    rw [←hh]
    exact mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1)
  exact kleinFour_three_rotation c D a b ha hb hab

/-- The actual common torus has no element of order three in its centralizer. -/
theorem three_not_dvd_torus_centralizer :
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (t.torus.map c.H.subtype : Set G)) := by
  intro hd
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hzD : (t.z:G) ∈ t.torus.map c.H.subtype := mem_map_of_mem c.H.subtype
    (mem_sup_left (mem_zpowers t.z))
  have hnD : (t.n:G) ∈ t.torus.map c.H.subtype := mem_map_of_mem c.H.subtype
    (mem_sup_right (mem_zpowers t.n))
  have huH : (u:G) ∈ c.H := t.centralizer.ge
    (mem_centralizer_singleton_iff.mpr (u.property (t.z:G) hzD).symm)
  let w : c.H := ⟨u,huH⟩
  have hw : orderOf w=3 := (orderOf_coe w).symm.trans ((orderOf_coe u).trans hu)
  have hwn : Commute w t.n := Subtype.ext (u.property (t.n:G) hnD).symm
  have haxis (i : BinaryFourPlus.C2) : axisAction c i w=1 := by
    apply (by decide : ∀ s r : Equiv.Perm (Fin 3),
      s^3=1 → Equiv.Perm.sign r ≠ 1 → s*r=r*s → s=1)
      (axisAction c i w) (axisAction c i t.n)
    · have hw3 : w^3=1 := hw ▸ pow_orderOf_eq_one w
      rw [←map_pow,hw3,map_one]
    · exact (outside_involution_axisAction c t.n t.n_order t.outside i).2
    · exact hwn.map (axisAction c i)
  have houter : coreOuterAction c w=1 := by
    apply RegularWreathProduct.ext
    · exact funext haxis
    · exact coreOuterAction_preserves_factors c w
  have hwQ : w ∈ quaternionCore c := by
    rw [←coreOuterAction_kernel c]
    exact houter
  have hdiv := orderOf_dvd_natCard (⟨w,hwQ⟩ : quaternionCore c)
  rw [orderOf_mk,hw,quaternionCore_card c] at hdiv
  norm_num at hdiv

/-- An actual order-three actor realizes the rotation of the marked torus. -/
theorem exists_cubic_rotation :
    ∃ g : G, orderOf g=3 ∧
      g ∈ normalizer (t.torus.map c.H.subtype : Set G) ∧
      MulAut.conj g (t.z:G)=(t.n:G) ∧
      MulAut.conj g (t.n:G)=(t.z:G)*(t.n:G) := by
  let D := t.torus.map c.H.subtype
  let : IsKleinFour D := t.ambient_torus_kleinFour
  obtain ⟨g,k,hg,hgN,hgz,hgn⟩ := t.exists_three_rotation
  let v : normalizer (D:Set G) := ⟨g,hgN⟩
  let f := D.normalizerMonoidHom
  have hker : Nat.Coprime 3 (Nat.card f.ker) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (D:Set G))).toEquiv]
    exact t.three_not_dvd_torus_centralizer
  have hzD : (t.z:G) ∈ D := mem_map_of_mem c.H.subtype
    (mem_sup_left (mem_zpowers t.z))
  have hnD : (t.n:G) ∈ D := mem_map_of_mem c.H.subtype
    (mem_sup_right (mem_zpowers t.n))
  let a : D := ⟨t.z,hzD⟩
  let b : D := ⟨t.n,hnD⟩
  have ha : a≠1 := by
    intro he
    have hh : t.z=1 := Subtype.ext (congrArg (fun q : D => (q:G)) he)
    have hz := t.z_order
    simp [hh] at hz
  have hb : b≠1 := by
    intro he
    have hh : t.n=1 := Subtype.ext (congrArg (fun q : D => (q:G)) he)
    have hn := t.n_order
    simp [hh] at hn
  have hab : a≠b := by
    intro he
    have hh : t.z=t.n := Subtype.ext (congrArg (fun q : D => (q:G)) he)
    apply t.outside
    rw [←hh]
    exact mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1)
  have hfa : f v a=b := Subtype.ext hgz
  have hfb : f v b=a*b := Subtype.ext hgn
  have hfab : f v (a*b)=a := by
    let : IsMulCommutative D := IsKleinFour.isMulCommutative
    rw [map_mul,hfa,hfb,mul_comm' a b,←mul_assoc,IsKleinFour.mul_self,one_mul]
  have hf3 : orderOf (f v)=3 := orderOf_eq_prime (by
    apply MulEquiv.ext
    intro x
    change f v (f v (f v x))=x
    rcases four_cases D a b x ha hb hab with rfl|rfl|rfl|rfl
    · simp only [map_one]
    · rw [hfa,hfb,hfab]
    · rw [hfb,hfab,hfa]
    · rw [hfab,hfa,hfb]) (by
      intro he
      rw [he] at hfa
      exact hab hfa)
  have hv := f.orderOf_eq_of_prime_power_of_coprime_ker hker v
    ⟨k,Subtype.ext hg⟩
  exact ⟨g,(orderOf_coe v).trans (hv.symm.trans hf3),hgN,hgz,hgn⟩

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
