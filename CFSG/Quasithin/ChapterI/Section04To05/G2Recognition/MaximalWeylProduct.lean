module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalEndpointInvolutions
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.TorusNormalizerStructure

/-!
# The order-six product of the original endpoint reflections

Retain the quaternion marking when constructing each endpoint involution:
multiplication by the original outer involution gives an element in the
opposite normal SL₂(3) factor, with square the marked central involution.
A torus-preserving Sylow aligner supplies two reflections fixing distinct
points of the same four-group. Their product acts as a three-cycle. Its
cube lies in the elementary torus centralizer, so its sixth power is one.

If the cube were one, the product would conjugate the first reflection
to the second and carry their fixed torus points to one another. Composing
with the inverse aligner gives a conjugation inside H preserving the torus.
Such conjugation preserves the opposite-factor coset marking; the second
reflection cannot lie in that coset, since its marked square is nontrivial.
This excludes order three. The three-cycle action excludes order two.

The final theorem retains both original endpoint ranges, their whole Borel
intersection and their torus markings. Chapter14WeylProduct applies it to
the literal source configuration. Compatible Atlas endpoint maps, both
commuting squares, generation, and the separate completion and strongly
three-embedded exclusion theorems remain necessary for I.4.5 recognition.
Source: Aschbacher–Smith I.4.5, printed p.417, and the endpoint order-six
hypothesis of F.4.26, printed p.288. The quaternion calculation is the
existing lower-layer outer-involution theorem.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
private theorem right_quaternion_inverted_square (t : CubicTorus c) :
    ∃ q : c.H, q∈c.H₂ ∧ q^2=t.z ∧ t.n*q*t.n⁻¹=q⁻¹ := by
  let Q := quaternionCore c
  let d := quaternionCoreData c
  have hzC : t.z∈c.H₁.pCoreIn 2 ⊓ c.H₂.pCoreIn 2 := by
    rw [factor_core_intersection c]
    exact t.central_line ▸ mem_zpowers t.z
  let zQ : Q := ⟨t.z,mem_sup_left hzC.1⟩
  let zD : (d.right⊓d.left:Subgroup Q) := ⟨zQ,hzC.2,hzC.1⟩
  let a : MulAut Q := MulAut.conjNormal t.n
  have ha : a^2=1 := by
    change (MulAut.conjNormal t.n : MulAut Q)^2=1
    rw [←map_pow,show t.n^2=1 from t.n_order ▸ pow_orderOf_eq_one t.n,map_one]
  have ho := outside_bothOuter c t.n t.outside
  obtain ⟨hf,_⟩ := quaternion_outer_involution_factor_data d.right d.left d.right_model
    (by rw [inf_comm]; exact d.intersection_card) a ha ho.right_map ho.right_outer
  obtain ⟨hc,hs⟩ := hf zD
  obtain ⟨q,hq⟩ := (Nat.card_pos_iff.mp (show 0<Nat.card {b : d.right //
    (b:Q)⁻¹*a (b:Q)=(zD:Q)} by rw [hc]; decide)).1
  have hsq : (q.val:c.H)^2=t.z := congrArg Subtype.val (hs q hq)
  have he : (q.val:c.H)⁻¹*(t.n*(q.val:c.H)*t.n⁻¹)=t.z := congrArg Subtype.val hq
  refine ⟨q.val,c.H₂.pCoreIn_le 2 q.property,hsq,?_⟩
  have hn2 : t.z^2=1 := t.z_order ▸ pow_orderOf_eq_one t.z
  have hq4 : (q.val:c.H)^4=1 := by rw [show 4=2*2 from rfl,pow_mul,hsq,hn2]
  have hh : t.n*(q.val:c.H)*t.n⁻¹=(q.val:c.H)*t.z :=
    (inv_mul_eq_iff_eq_mul).mp he
  rw [hh,←hsq,←pow_succ']
  exact eq_inv_of_mul_eq_one_left (by rw [←pow_succ,hq4])

private theorem marked_reflection (t : CubicTorus c) :
    ∃ s : c.H, s*t.n∈c.H₂ ∧ (s*t.n)^2=t.z ∧ orderOf s=2 ∧
      s∈normalizer (t.torus:Set c.H) ∧ MulAut.conj s t.n=t.z*t.n := by
  obtain ⟨q,hq,hq2,hnq⟩ := t.right_quaternion_inverted_square
  let s : c.H := q*t.n
  have hsq : s^2=1 := by
    have hn2 : t.n*t.n=1 := by simpa only [pow_two,t.n_order] using pow_orderOf_eq_one t.n
    have he : t.n*q=q⁻¹*t.n := mul_inv_eq_iff_eq_mul.mp hnq
    change (q*t.n)^2=1
    rw [pow_two,mul_assoc,←mul_assoc t.n q t.n,he,mul_assoc,hn2,mul_one,mul_inv_cancel]
  have hs1 : s≠1 := by
    intro he
    have hn : t.n=q⁻¹ := eq_inv_of_mul_eq_one_right he
    exact t.outside (mem_sup_right (hn ▸ c.H₂.inv_mem hq))
  have hs2 : orderOf s=2 := orderOf_eq_prime hsq hs1
  have hsz : MulAut.conj (s:G) (t.z:G)=(t.z:G) := by
    apply mul_inv_eq_iff_eq_mul.mpr
    exact mem_centralizer_singleton_iff.mp (t.centralizer ▸ s.property)
  have hsn : MulAut.conj s t.n=t.z*t.n := by
    change (q*t.n)*t.n*(q*t.n)⁻¹=t.z*t.n
    calc
      _ = q*t.n*q⁻¹ := by group
      _ = q*q*t.n := by
        have hh := congrArg Inv.inv hnq
        simp only [mul_inv_rev,inv_inv,←mul_assoc] at hh
        have hh' : t.n*q⁻¹=q*t.n := mul_inv_eq_iff_eq_mul.mp hh
        rw [mul_assoc,hh',←mul_assoc]
      _ = t.z*t.n := by rw [←pow_two,hq2]
  have hsN : s∈normalizer (t.torus:Set c.H) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rw [torus,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
      apply sup_le
      · apply zpowers_le.mpr
        have hz : MulAut.conj s t.z=t.z := Subtype.ext hsz
        change MulAut.conj s t.z∈zpowers t.z⊔zpowers t.n
        rw [hz]
        exact mem_sup_left (mem_zpowers _)
      · apply zpowers_le.mpr
        change MulAut.conj s t.n∈zpowers t.z⊔zpowers t.n
        rw [hsn]
        exact mul_mem_sup (mem_zpowers _) (mem_zpowers _)
    · rw [card_map_of_injective (MulAut.conj s).injective]
  have hsnq : s*t.n=q := by
    change q*t.n*t.n=q
    rw [mul_assoc,←pow_two,show t.n^2=1 from t.n_order ▸ pow_orderOf_eq_one t.n,mul_one]
  exact ⟨s,hsnq.symm ▸ hq,by rw [hsnq,hq2],hs2,hsN,hsn⟩

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

omit [Finite G] in
private theorem reflection_other (D : Subgroup G) [IsKleinFour D]
    (a b : D) (ha : a≠1) (hb : b≠1) (hab : a≠b)
    (f : MulAut D) (hf : f≠1) (hfa : f a=a) : f b=a*b := by
  apply IsKleinFour.eq_mul_of_ne_all ha hb hab
  · exact fun h=>hb (f.injective (h.trans (map_one f).symm))
  · exact fun h=>hab (f.injective (h.trans hfa.symm)).symm
  · intro hfb
    apply hf
    apply MulEquiv.ext
    intro x
    rcases four_cases D a b x ha hb hab with rfl|rfl|rfl|rfl
    · exact map_one f
    · exact hfa
    · exact hfb
    · rw [map_mul,hfa,hfb]; rfl

omit [Finite G] in
private theorem reflection_product (D : Subgroup G) [IsKleinFour D]
    (a b : D) (ha : a≠1) (hb : b≠1) (hab : a≠b)
    (f k : MulAut D) (hf : f≠1) (hk : k≠1) (hfa : f a=a) (hkb : k b=b) :
    (f*k)^3=1 ∧ (f*k) a=b := by
  let : IsMulCommutative D := IsKleinFour.isMulCommutative
  have hfb := reflection_other D a b ha hb hab f hf hfa
  have hka : k a=a*b := by
    rw [reflection_other D b a hb ha hab.symm k hk hkb,mul_comm' b a]
  have hpa : (f*k) a=b := by
    change f (k a)=b
    rw [hka,map_mul,hfa,hfb,←mul_assoc,IsKleinFour.mul_self,one_mul]
  have hpb : (f*k) b=a*b := by change f (k b)=a*b; rw [hkb,hfb]
  have hpab : (f*k) (a*b)=a := by
    rw [map_mul,hpa,hpb,mul_comm' a b,←mul_assoc,IsKleinFour.mul_self,one_mul]
  refine ⟨?_,hpa⟩
  apply MulEquiv.ext
  intro x
  change (f*k) ((f*k) ((f*k) x))=x
  rcases four_cases D a b x ha hb hab with rfl|rfl|rfl|rfl
  · simp only [map_one]
  · rw [hpa,hpb,hpab]
  · rw [hpb,hpab,hpa]
  · rw [hpab,hpa,hpb]

omit [Finite G] in
private theorem marked_reflections_not_fused (t : CubicTorus c)
    (s r h : c.H) (hs : s*t.n∈c.H₂) (hr : r*t.n∈c.H₁)
    (hrsq : (r*t.n)^2=t.z) (hn : h∈normalizer (t.torus:Set c.H)) :
    MulAut.conj h s≠r := by
  let : IsKleinFour t.torus := t.torus_kleinFour
  let a : t.torus := ⟨t.z,mem_sup_left (mem_zpowers _)⟩
  let b : t.torus := ⟨t.n,mem_sup_right (mem_zpowers _)⟩
  have ha : a≠1 := by intro he; have hh:=t.z_order; simp [show t.z=1 from congrArg Subtype.val he] at hh
  have hb : b≠1 := by intro he; have hh:=t.n_order; simp [show t.n=1 from congrArg Subtype.val he] at hh
  have hab : a≠b := by
    intro he
    have hz : t.z=t.n := congrArg Subtype.val he
    exact t.outside (hz ▸ mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1))
  let f := t.torus.normalizerMonoidHom ⟨h,hn⟩
  have hfa : f a=a := by
    apply Subtype.ext
    change h*t.z*h⁻¹=t.z
    apply mul_inv_eq_iff_eq_mul.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (t.centralizer ▸ h.property)
  have hfn : (f b:t.torus)=b ∨ (f b:t.torus)=a*b := by
    rcases four_cases t.torus a b (f b) ha hb hab with h1|h2|h3|h4
    · exact (hb (f.injective (h1.trans (map_one f).symm))).elim
    · exact (hab (f.injective (h2.trans hfa.symm)).symm).elim
    · exact Or.inl h3
    · exact Or.inr h4
  have hnn : (MulAut.conj h t.n)*t.n∈c.H₂ := by
    rcases hfn with he|he
    · have hh : MulAut.conj h t.n=t.n := congrArg Subtype.val he
      rw [hh,←pow_two,show t.n^2=1 from t.n_order ▸ pow_orderOf_eq_one t.n]
      exact one_mem _
    · have hh : MulAut.conj h t.n=t.z*t.n := congrArg Subtype.val he
      rw [hh,mul_assoc,←pow_two,show t.n^2=1 from t.n_order ▸ pow_orderOf_eq_one t.n,mul_one]
      exact (t.central_line ▸ mem_zpowers t.z).2
  have hnorm := c.H₂_normal.conj_mem (s*t.n) hs h
  intro he
  change MulAut.conj h (s*t.n)∈c.H₂ at hnorm
  rw [map_mul,he] at hnorm
  have hrr : r*t.n∈c.H₂ := by
    have hh := c.H₂.mul_mem hnorm hnn
    have hn2 : (MulAut.conj h t.n)*(MulAut.conj h t.n)=1 := by
      rw [←map_mul,←pow_two,show t.n^2=1 from t.n_order ▸ pow_orderOf_eq_one t.n,map_one]
    simpa only [mul_assoc,←mul_assoc (MulAut.conj h t.n) (MulAut.conj h t.n),hn2,one_mul] using hh
  have hline : r*t.n∈zpowers t.z := t.central_line.symm ▸ (show r*t.n∈c.H₁⊓c.H₂ from ⟨hr,hrr⟩)
  have hdiv := orderOf_dvd_of_mem_zpowers hline
  rw [t.z_order] at hdiv
  have hpow : (r*t.n)^2=1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
  have hz1 := hrsq.symm.trans hpow
  have hzorder := t.z_order
  simp only [hz1,orderOf_one] at hzorder
  omega
private theorem marked_product_order (t : CubicTorus c)
    (s r : c.H) (hs : s*t.n∈c.H₂) (hr : r*t.n∈c.H₁)
    (hrsq : (r*t.n)^2=t.z) (hs2 : orderOf s=2) (hr2 : orderOf r=2)
    (hsN : s∈normalizer (t.torus:Set c.H)) (hrN : r∈normalizer (t.torus:Set c.H))
    (hsn : MulAut.conj s t.n=t.z*t.n) (hrn : MulAut.conj r t.n=t.z*t.n)
    (g : G) (hg : g∈normalizer (t.torus.map c.H.subtype:Set G))
    (hgz : MulAut.conj g (t.z:G)≠(t.z:G)) :
    orderOf ((s:G)*MulAut.conj g (r:G))=6 := by
  let A := t.torus.map c.H.subtype
  let N := normalizer (A:Set G)
  let : IsKleinFour A := t.ambient_torus_kleinFour
  have hzA : (t.z:G)∈A := mem_map_of_mem _ (mem_sup_left (mem_zpowers _))
  have hnA : (t.n:G)∈A := mem_map_of_mem _ (mem_sup_right (mem_zpowers _))
  have hgA : A.map (MulAut.conj g).toMonoidHom=A := mem_normalizer_iff_map_conj_eq.mp hg
  have hgzA : MulAut.conj g (t.z:G)∈A := hgA ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hzA
  have hgnA : MulAut.conj g (t.n:G)∈A := hgA ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hnA
  have hsg : (s:G)∈N := t.torus.le_normalizer_map c.H.subtype (mem_map_of_mem _ hsN)
  have hrg : (r:G)∈N := t.torus.le_normalizer_map c.H.subtype (mem_map_of_mem _ hrN)
  let v := MulAut.conj g (r:G)
  have hvN : v∈N := N.mul_mem (N.mul_mem hg hrg) (N.inv_mem hg)
  let ss : N := ⟨s,hsg⟩
  let rr : N := ⟨v,hvN⟩
  let a : A := ⟨t.z,hzA⟩
  let b : A := ⟨MulAut.conj g (t.z:G),hgzA⟩
  let f := A.normalizerMonoidHom ss
  let k := A.normalizerMonoidHom rr
  have ha : a≠1 := by
    intro he
    have hh := t.z_order
    have hz1 : t.z=1 := Subtype.ext (congrArg (fun q:A => (q:G)) he)
    simp only [hz1,orderOf_one] at hh
    omega
  have hb : b≠1 := by
    intro he
    apply ha
    apply Subtype.ext
    exact (MulAut.conj g).injective ((congrArg Subtype.val he).trans (map_one _).symm)
  have hab : a≠b := fun he=>hgz (congrArg Subtype.val he).symm
  have hfa : f a=a := by
    apply Subtype.ext
    change (s:G)*(t.z:G)*(s:G)⁻¹=(t.z:G)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (t.centralizer ▸ s.property))
  have hkb : k b=b := by
    apply Subtype.ext
    have hfix : MulAut.conj (r:G) (t.z:G)=(t.z:G) :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (t.centralizer ▸ r.property))
    change v*MulAut.conj g (t.z:G)*v⁻¹=MulAut.conj g (t.z:G)
    change (r:G)*(t.z:G)*(r:G)⁻¹=(t.z:G) at hfix
    simpa only [map_mul,map_inv] using congrArg (MulAut.conj g) hfix
  have hf : f≠1 := by
    intro he
    have hh := congrArg (fun e : MulAut A => (e ⟨t.n,hnA⟩:G)) he
    have hsn' : (f ⟨t.n,hnA⟩:G)=(t.z:G)*(t.n:G) := congrArg Subtype.val hsn
    rw [hsn'] at hh
    have hz1 : (t.z:G)=1 := mul_right_cancel (hh.trans (one_mul _).symm)
    exact ha (Subtype.ext hz1)
  have hk : k≠1 := by
    intro he
    have hh := congrArg (fun e : MulAut A => (e ⟨MulAut.conj g (t.n:G),hgnA⟩:G)) he
    have hrn' : v*MulAut.conj g (t.n:G)*v⁻¹=
        MulAut.conj g ((t.z:G)*(t.n:G)) := by
      have hrnG : (r:G)*(t.n:G)*(r:G)⁻¹=(t.z:G)*(t.n:G) := congrArg Subtype.val hrn
      simpa only [map_mul,map_inv] using congrArg (MulAut.conj g) hrnG
    change v*MulAut.conj g (t.n:G)*v⁻¹=MulAut.conj g (t.n:G) at hh
    rw [hrn'] at hh
    have hn := (MulAut.conj g).injective hh
    exact ha (Subtype.ext (mul_right_cancel (hn.trans (one_mul _).symm)))
  obtain ⟨hp,hpa⟩ := reflection_product A a b ha hb hab f k hf hk hfa hkb
  let w := (s:G)*v
  have hwN : w∈N := N.mul_mem hsg hvN
  have hwz : MulAut.conj w (t.z:G)=MulAut.conj g (t.z:G) := by
    change (A.normalizerMonoidHom (ss*rr) a:G)=(b:G)
    rw [map_mul]
    exact congrArg Subtype.val hpa
  have hwC : w^3∈Subgroup.centralizer (A:Set G) := by
    have hk' : (ss*rr)^3∈A.normalizerMonoidHom.ker := by
      change A.normalizerMonoidHom ((ss*rr)^3)=1
      rw [map_pow,map_mul]
      exact hp
    rw [normalizerMonoidHom_ker] at hk'
    exact hk'
  have hw6 : w^6=1 := by
    let : IsElementaryAbelian 2 (Subgroup.centralizer (A:Set G)) := t.torus_centralizer_structure.1
    exact (pow_mul w 3 2).trans (elemPow_eq_one_of_isElementaryAbelian (A:=Subgroup.centralizer (A:Set G)) (w^3) hwC)
  have hw3 : w^3≠1 := by
    intro he
    have hsi : (s:G)⁻¹=(s:G) := inv_eq_of_mul_eq_one_right (by
      exact congrArg Subtype.val (show s*s=1 by simpa only [pow_two,hs2] using pow_orderOf_eq_one s))
    have hvi : v⁻¹=v := inv_eq_of_mul_eq_one_right (by
      have hv2 : v^2=1 := by
        change (MulAut.conj g (r:G))^2=1
        rw [←map_pow,show (r:G)^2=1 from congrArg Subtype.val (hr2 ▸ pow_orderOf_eq_one r),map_one]
      simpa only [pow_two] using hv2)
    have hvv : v*v=1 := by nth_rw 1 [←hvi]; exact inv_mul_cancel v
    have hws : MulAut.conj w (s:G)=v := by
      have hh := congrArg (fun u:G=>u*v) he
      change ((s:G)*v)^3*v=1*v at hh
      simp only [pow_succ,pow_zero,one_mul,mul_one,mul_assoc,hvv] at hh
      change ((s:G)*v)*(s:G)*((s:G)*v)⁻¹=v
      simpa only [mul_inv_rev,hsi,hvi,mul_assoc] using hh
    let h := g⁻¹*w
    have hhz : MulAut.conj h (t.z:G)=(t.z:G) := by
      change (g⁻¹*w)*(t.z:G)*(g⁻¹*w)⁻¹=(t.z:G)
      calc
        _ = g⁻¹*(MulAut.conj w (t.z:G))*g := by change _=g⁻¹*(w*(t.z:G)*w⁻¹)*g; group
        _ = t.z := by rw [hwz]; simp only [MulAut.conj_apply]; group
    have hhH : h∈c.H := t.centralizer.ge
      (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hhz))
    have hhN : h∈N := N.mul_mem (N.inv_mem hg) hwN
    let hH : c.H := ⟨h,hhH⟩
    have hhlocal : hH∈normalizer (t.torus:Set c.H) := by
      have hx := A.le_normalizer_comap c.H.subtype (show hH∈N.comap c.H.subtype from hhN)
      simpa only [A,comap_map_eq_self_of_injective c.H.subtype_injective] using hx
    apply marked_reflections_not_fused t s r hH hs hr hrsq hhlocal
    apply Subtype.ext
    change h*(s:G)*h⁻¹=(r:G)
    calc
      _ = g⁻¹*(MulAut.conj w (s:G))*g := by change _=g⁻¹*(w*(s:G)*w⁻¹)*g; dsimp [h]; group
      _ = r := by rw [hws]; change g⁻¹*(g*(r:G)*g⁻¹)*g=(r:G); group
  have hw2 : w^2≠1 := by
    intro he
    have he3 : w^3=w := by rw [pow_succ,he,one_mul]
    rw [he3] at hwC
    have hfix : MulAut.conj w (t.z:G)=(t.z:G) :=
      mul_inv_eq_iff_eq_mul.mpr (hwC _ hzA).symm
    exact hgz (hwz.symm.trans hfix)
  change orderOf w=6
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) hw6
  intro p hp hd hpow
  have hp' : p=2 ∨ p=3 := by
    have hle := Nat.le_of_dvd (by decide : 0<6) hd
    interval_cases p <;> norm_num at *
  rcases hp' with rfl|rfl
  · exact hw3 hpow
  · exact hw2 hpow
private theorem marked_reflection_endpoint (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) (s : c.H)
    (hs : s*t.n∈c.H₂) (hsN : s∈normalizer (t.torus:Set c.H))
    (hsn : MulAut.conj s t.n=t.z*t.n) :
    (s:G)∈cubicNormalizer c t.x ∧ (s:G)∉t.leftCubicBorel ∧
    (s:G)∈normalizer (t.torus.map c.H.subtype:Set G) := by
  have hn2 : t.n*t.n=1 := by simpa only [pow_two,t.n_order] using pow_orderOf_eq_one t.n
  have hsg : (s:G)∈normalizer (t.torus.map c.H.subtype:Set G) :=
    t.torus.le_normalizer_map c.H.subtype (mem_map_of_mem _ hsN)
  refine ⟨?_,?_,hsg⟩
  · rw [t.left_ambient_normalizer]
    have he : (s:G)=((s*t.n:c.H):G)*(t.n:G) := by
      exact congrArg Subtype.val (show s=(s*t.n)*t.n by rw [mul_assoc,hn2,mul_one])
    rw [he]
    exact mul_mem (mem_sup_left (mem_sup_right (mem_map_of_mem c.H.subtype hs)))
      (mem_sup_right (mem_map_of_mem c.H.subtype (mem_sup_right (mem_zpowers _))))
  · intro hb
    have hsA := (t.maximal_borel_torus_normalizer hc).le ⟨hb,hsg⟩
    let A := t.torus.map c.H.subtype
    let : IsKleinFour A := t.ambient_torus_kleinFour
    let : IsMulCommutative A := IsKleinFour.isMulCommutative
    have hnA : (t.n:G)∈A := mem_map_of_mem _ (mem_sup_right (mem_zpowers _))
    have hh : (s:G)*(t.n:G)=(t.n:G)*(s:G) :=
      congrArg Subtype.val (mul_comm' (⟨s,hsA⟩:A) ⟨t.n,hnA⟩)
    have hsnG : (s:G)*(t.n:G)*(s:G)⁻¹=(t.z:G)*(t.n:G) := congrArg Subtype.val hsn
    rw [hh,mul_inv_cancel_right] at hsnG
    have hz1 : t.z=1 := Subtype.ext (mul_right_cancel (hsnG.symm.trans (one_mul _).symm))
    have hzo := t.z_order
    simp only [hz1,orderOf_one] at hzo
    omega

/-- The aligned original endpoints have involutions outside their whole
Borel whose product has order six, retaining their marked torus actions. -/
theorem maximal_aligned_endpoint_hexagon_involutions (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ∃ g s r : G,
      g∈normalizer (t.torus.map c.H.subtype:Set G) ∧
      t.swap.leftCoreExtension.map (MulAut.conj g).toMonoidHom=t.leftCoreExtension ∧
      cubicNormalizer c t.x ⊓
        (cubicNormalizer (swapFactors c) t.y).map (MulAut.conj g).toMonoidHom=t.leftCubicBorel ∧
      s∈cubicNormalizer c t.x ∧
      r∈(cubicNormalizer (swapFactors c) t.y).map (MulAut.conj g).toMonoidHom ∧
      s∉t.leftCubicBorel ∧ r∉t.leftCubicBorel ∧
      orderOf s=2 ∧ orderOf r=2 ∧ orderOf (s*r)=6 ∧
      s∈normalizer (t.torus.map c.H.subtype:Set G) ∧
      r∈normalizer (t.torus.map c.H.subtype:Set G) ∧
      MulAut.conj s (t.z:G)=(t.z:G) ∧
      MulAut.conj s (t.n:G)=(t.z:G)*(t.n:G) ∧
      MulAut.conj r (MulAut.conj g (t.z:G))=MulAut.conj g (t.z:G) ∧
      MulAut.conj r (MulAut.conj g (t.n:G))=
        MulAut.conj g ((t.z:G)*(t.n:G)) ∧
      MulAut.conj g (t.z:G)≠(t.z:G) := by
  obtain ⟨g,hgN,hg⟩ := t.maximal_extensions_conjugate_in_torus_normalizer hc
  obtain ⟨s,hs,_,hs2,hsN,hsn⟩ := t.marked_reflection
  obtain ⟨r,hr,hrsq,hr2,hrN,hrn⟩ := t.swap.marked_reflection
  obtain ⟨hsP,hsB,hsA⟩ := t.marked_reflection_endpoint hc s hs hsN hsn
  obtain ⟨hrP,hrB,hrA⟩ := t.swap.marked_reflection_endpoint
    (t.oddCore_card_eq.symm.trans hc) r hr hrN hrn
  have hmove := t.maximal_aligner_moves_central_involution hc g hg
  let f := MulAut.conj g
  have hfN : (normalizer (t.torus.map c.H.subtype:Set G)).map f.toMonoidHom=
      normalizer (t.torus.map c.H.subtype:Set G) := by
    rw [map_normalizer_eq_of_bijective _ f.bijective]
    rw [show (t.torus.map c.H.subtype).map f.toMonoidHom=t.torus.map c.H.subtype
      from mem_normalizer_iff_map_conj_eq.mp hgN]
  have fix (v : c.H) : MulAut.conj (v:G) (t.z:G)=(t.z:G) :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (t.centralizer ▸ v.property))
  refine ⟨g,s,f r,hgN,hg,t.maximal_aligned_endpoint_overlap hc g hg,hsP,
    mem_map_of_mem f.toMonoidHom hrP,hsB,?_,(orderOf_coe s).trans hs2,
    (f.orderOf_eq r).trans ((orderOf_coe r).trans hr2),
    t.marked_product_order s r hs hr hrsq hs2 hr2 hsN hrN hsn hrn g hgN hmove,
    hsA,hfN.le (mem_map_of_mem f.toMonoidHom hrA),fix s,congrArg Subtype.val hsn,?_,?_,hmove⟩
  · intro hb
    rw [←t.maximal_aligned_borels hc g hg] at hb
    exact hrB ((mem_map_iff_mem f.injective).mp hb)
  · have hh : (r:G)*(t.z:G)*(r:G)⁻¹=(t.z:G) := fix r
    change f r*f (t.z:G)*(f r)⁻¹=f (t.z:G)
    simpa only [map_mul,map_inv] using congrArg f hh
  · have hh : (r:G)*(t.n:G)*(r:G)⁻¹=(t.z:G)*(t.n:G) := congrArg Subtype.val hrn
    change f r*f (t.n:G)*(f r)⁻¹=f ((t.z:G)*(t.n:G))
    simpa only [map_mul,map_inv] using congrArg f hh
end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
