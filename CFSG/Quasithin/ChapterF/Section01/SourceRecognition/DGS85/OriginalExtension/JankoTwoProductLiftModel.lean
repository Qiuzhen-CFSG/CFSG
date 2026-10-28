module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoGeneratorRelations
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicCentralizer


/-!
# The central lift forced by both Hall–Janko endpoint actions

The A₅ quotient writes every inverter of the marked cubic as r kⁿ t,
with r in the cubic centralizer of the actual order-32 core. The moved
quaternion orbit gives six possible images of q. A checked finite sieve
uses one relation from each reduced endpoint to force (f(t)t)³ = z.
The second relation d z d = v d v excludes first-endpoint automorphisms
with the wrong lift. Agreement on the entire Borel supplies that relation.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–231.
The model is the retained ATLAS J2G1-p100B0 carrier. Its existing radical,
Sylow and cubic tables and the earlier source inverter word supply the
certificates; every equality is checked by Lean's kernel. This module
proves an action relation, not an original Aut(J₂) comparison.
-/


open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Seed PairNormalizer GeneratorPair GeneratorPair.SecondOrbitCertificate FirstParabolic
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.ProductLift

private def k : Carrier := oddGenerator 1
private def d : Carrier := oddGenerator 0
private def q : Carrier := radicalElement 12
private def u : Carrier := sElement 5
private def v : Carrier := sElement 116
private def w : Carrier := sElement 47
private def tWord : List (Fin 3) := [2,2,0,1,0,2,2,2,2,2,2,0,2,0,2,0,2,0,1,0,2,2,0,1,0,1,0,2,0,2,0]
private def t : Carrier := localWord tWord
private def tMap : Fin 100 → Fin 100 := packedMap 3881624724470476115528354446615250408763469728990278980862273442714448688269640655557939205451083296245890251434252628308280335810936193140659017801965556861039639078195667381313023073821921928529120070066492882
private theorem tMap_sq : ∀ i, tMap (tMap i)=i := by apply allFin; decide +kernel
private def tPerm : Equiv.Perm (Fin 100) := tablePerm tMap tMap tMap_sq tMap_sq
private theorem inclusion_word (a : List (Fin 3)) :
    inclusion (localWord a)=evalWord ![tableA,tableB,tableB⁻¹] a := by
  induction a with
  | nil => rfl
  | cons i a ih =>
    change inclusion (![GeneratorPair.a,GeneratorPair.b,GeneratorPair.b⁻¹] i*localWord a)=_
    rw [map_mul,ih]
    congr 1
    fin_cases i <;> simp [GeneratorPair.a,GeneratorPair.b,Sporadic.LeechRelated.J2.inclusion,generatorA_eq_table,generatorB_eq_table]
private theorem t_inclusion : inclusion t=tPerm := by
  rw [t,inclusion_word]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem z_inclusion : inclusion z=SylowData.sTable 6 := by
  change inclusion FirstFusion.t=_
  rw [FirstFusion.inclusion_t]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem t_mem : t∈l₁ := by
  apply mem_centralizer_singleton_iff.mpr
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,t_inclusion,z_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem t_sq : t^2=1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_pow,map_one,t_inclusion]
  exact Equiv.ext tMap_sq
private theorem t_inverts : t*k*t⁻¹=k⁻¹ := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,map_inv,map_inv,t_inclusion,k,oddGenerator_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem a5_centralizer_powers (a b : alternatingGroup (Fin 5))
    (ha : orderOf a=3) (hab : b*a=a*b) : ∃ n : Fin 3,b=a^n.val := by
  have hP : Nat.card (zpowers a)=3 := by rw [Nat.card_zpowers,ha]
  have hC := alternatingGroup.FiveLocalGeometry.cubic_centralizer_card (MulEquiv.refl _) (zpowers a) hP
  have he : zpowers a=centralizer (zpowers a:Set _) :=
    eq_of_le_of_card_ge (zpowers a).le_centralizer (by rw [hP,hC])
  have hb : b∈zpowers a := by
    rw [he]
    have hle : zpowers a≤centralizer ({b}:Set _) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hab.symm)
    exact mem_centralizer_iff.mpr (fun y hy => (mem_centralizer_singleton_iff.mp (hle hy)))
  have hf : IsOfFinOrder a := orderOf_pos_iff.mp (by rw [ha]; decide)
  rw [hf.mem_zpowers_iff_mem_range_orderOf,ha] at hb
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hb
  exact ⟨⟨n,Finset.mem_range.mp hn⟩,he.symm⟩

private theorem inverter_coordinates (a : l₁)
    (ha : (a:Carrier)*k*(a:Carrier)⁻¹=k⁻¹) :
    ∃ r : Fin 32, ∃ n : Fin 3,
      radicalElement r*k=k*radicalElement r ∧
      (a:Carrier)=radicalElement r*k^n.val*t := by
  let ki : l₁ := ⟨k,SecondParabolic.Overlap.B_le_l₁ ((show zpowers k≤SecondParabolic.Overlap.B from le_sup_right) (mem_zpowers k))⟩
  let ti : l₁ := ⟨t,t_mem⟩
  let f := QuotientActions.innerAction
  have hk : orderOf ki=3 := (orderOf_coe _).symm.trans SecondParabolic.Overlap.v_order
  have hk3 : ki^3=1 := by rw [←hk,pow_orderOf_eq_one]
  have hf3 : orderOf (f ki)=3 := by
    apply orderOf_eq_prime
    · rw [←map_pow,hk3,map_one]
    · intro hh
      have hm : ki∈radical.subgroupOf l₁ := by
        rw [←QuotientActions.innerAction_ker card_radical]
        exact hh
      have hd := radical.orderOf_dvd_natCard hm
      change orderOf (ki:Carrier) ∣ Nat.card radical at hd
      rw [card_radical,show orderOf (ki:Carrier)=3 from (orderOf_coe _).trans hk] at hd
      norm_num at hd
  have hc : (a*ti)*ki=ki*(a*ti) := by
    apply Subtype.ext
    change ((a:Carrier)*t)*k=k*((a:Carrier)*t)
    have ht : t*k=k⁻¹*t := mul_inv_eq_iff_eq_mul.mp t_inverts
    have hh : (a:Carrier)*k⁻¹=k*(a:Carrier) := by
      have he : (a:Carrier)*k⁻¹*(a:Carrier)⁻¹=k := by
        calc
          (a:Carrier)*k⁻¹*(a:Carrier)⁻¹=((a:Carrier)*k*(a:Carrier)⁻¹)⁻¹ := by group
          _ = k := by rw [ha,inv_inv]
      exact mul_inv_eq_iff_eq_mul.mp he
    calc
      ((a:Carrier)*t)*k=(a:Carrier)*(k⁻¹*t) := by rw [mul_assoc,ht]
      _=k*((a:Carrier)*t) := by rw [←mul_assoc,hh,mul_assoc]
  obtain ⟨n,hn⟩ := a5_centralizer_powers (f ki) (f (a*ti)) hf3 (by rw [←map_mul,←map_mul,hc])
  let b := a*ti*(ki^n.val)⁻¹
  have hb : b∈radical.subgroupOf l₁ := by
    rw [←QuotientActions.innerAction_ker card_radical]
    change f b=1
    dsimp [b]
    rw [map_mul,map_inv,map_pow,hn,mul_inv_cancel]
  obtain ⟨r,hr⟩ := exists_radicalElement hb
  have he : (a:Carrier)=radicalElement r*k^n.val*t := by
    rw [hr]
    change (a:Carrier)=((a:Carrier)*t*(k^n.val)⁻¹)*k^n.val*t
    calc
      (a:Carrier)= (a:Carrier)*(t*t) := by rw [←pow_two,t_sq,mul_one]
      _= ((a:Carrier)*t*(k^n.val)⁻¹)*k^n.val*t := by group
  refine ⟨r,n,?_,he⟩
  rw [hr]
  have hh := congrArg (fun y : l₁ => (y:Carrier)) hc
  change ((a:Carrier)*t)*k=k*((a:Carrier)*t) at hh
  change ((a:Carrier)*t*(k^n.val)⁻¹)*k=k*((a:Carrier)*t*(k^n.val)⁻¹)
  have hp : Commute ((k^n.val)⁻¹) k := ((Commute.refl k).pow_left n.val).inv_left
  calc
    ((a:Carrier)*t*(k^n.val)⁻¹)*k=((a:Carrier)*t)*(k*(k^n.val)⁻¹) := by rw [mul_assoc,hp.eq]
    _=k*((a:Carrier)*t*(k^n.val)⁻¹) := by rw [←mul_assoc,hh,mul_assoc]


private def orbit (m : Fin 6) : Carrier :=
  k^(m.val%3)*(if m.val<3 then q else q⁻¹)*(k^(m.val%3))⁻¹
private def orbitPerm (m : Fin 6) : Equiv.Perm (Fin 100) :=
  (QuotientData.oddTable 1)^(m.val%3)*
    (if m.val<3 then RadicalStructureData.tablePerm 12 else (RadicalStructureData.tablePerm 12)⁻¹)*
      ((QuotientData.oddTable 1)^(m.val%3))⁻¹
private theorem orbit_inclusion (m : Fin 6) : inclusion (orbit m)=orbitPerm m := by
  simp only [orbit,orbitPerm,map_mul,map_inv,map_pow]
  rw [k,oddGenerator_inclusion]
  split_ifs <;> simp only [q,map_inv,radicalElement_inclusion]

private def betaRelation {A : Type*} [Group A] (k t q w : A) : Prop :=
  w*k*w*t*w=q*k*t*w*t*k
private def alphaRelation {A : Type*} [Group A] (d z v : A) : Prop :=
  d*z*d=v*d*v

private theorem beta_relation : betaRelation k t q w := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_mul,t_inclusion,k,w,q,oddGenerator_inclusion,
    sElement_inclusion,radicalElement_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem alpha_relation : alphaRelation d z v := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simp only [map_mul,d,v,oddGenerator_inclusion,
    z_inclusion,sElement_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem sieve_check : ∀ r : Fin 32, ∀ n : Fin 3, ∀ m : Fin 6,
    let R := RadicalStructureData.tablePerm r
    let K := QuotientData.oddTable 1
    let D := QuotientData.oddTable 0
    let Z := SylowData.sTable 6
    let A := R*K^n.val*tPerm
    let Q := orbitPerm m
    let W := D⁻¹*Q*D
    let V := A⁻¹*SylowData.sTable 5*A
    R*K=K*R → betaRelation K⁻¹ A Q W → alphaRelation D Z V →
      (A*tPerm)^3=Z := by
  intro r
  fin_cases r <;> dsimp only [betaRelation,alphaRelation] <;> decide +kernel

private theorem sift (a : l₁) (m : Fin 6)
    (ha : (a:Carrier)*k*(a:Carrier)⁻¹=k⁻¹)
    (hb : betaRelation k⁻¹ a (orbit m) (d⁻¹*orbit m*d))
    (hc : alphaRelation d z ((a:Carrier)⁻¹*u*a)) :
    ((a:Carrier)*t)^3=z := by
  obtain ⟨r,n,hr,he⟩ := inverter_coordinates a ha
  simp only [betaRelation,alphaRelation] at hb hc
  rw [he] at hb hc ⊢
  apply Sporadic.LeechRelated.J2.inclusion_injective
  have hr' := congrArg inclusion hr
  have hb' := congrArg inclusion hb
  have hc' := congrArg inclusion hc
  simp only [map_mul,map_inv,map_pow,k,d,u,orbit_inclusion,radicalElement_inclusion,
    oddGenerator_inclusion,sElement_inclusion,t_inclusion,z_inclusion] at hr' hb' hc' ⊢
  exact sieve_check r n m hr' hb' hc'


private theorem k_mem_B : k∈SecondParabolic.Overlap.B :=
  (show zpowers k≤SecondParabolic.Overlap.B from le_sup_right) (mem_zpowers k)
private theorem q_mem_B : q∈SecondParabolic.Overlap.B := by
  have he : q=sElement 42 := by
    apply Sporadic.LeechRelated.J2.inclusion_injective
    rw [q,radicalElement_inclusion,sElement_inclusion]
    apply Equiv.ext
    apply allFin
    decide +kernel
  exact (show s≤SecondParabolic.Overlap.B from le_sup_left) (he ▸ sElement_mem 42)
private theorem z_mem_B : z∈SecondParabolic.Overlap.B := by
  have he : z=sElement 6 := by
    apply Sporadic.LeechRelated.J2.inclusion_injective
    rw [z_inclusion,sElement_inclusion]
  exact (show s≤SecondParabolic.Overlap.B from le_sup_left) (he ▸ sElement_mem 6)
private theorem u_mem_B : u∈SecondParabolic.Overlap.B :=
  (show s≤SecondParabolic.Overlap.B from le_sup_left) (sElement_mem 5)
private theorem v_mem_B : v∈SecondParabolic.Overlap.B :=
  (show s≤SecondParabolic.Overlap.B from le_sup_left) (sElement_mem 116)
private theorem w_mem_B : w∈SecondParabolic.Overlap.B :=
  (show s≤SecondParabolic.Overlap.B from le_sup_left) (sElement_mem 47)
private def leftB (b : Carrier) (hb : b∈SecondParabolic.Overlap.B) : l₁ :=
  ⟨b,SecondParabolic.Overlap.B_le_l₁ hb⟩
private def rightB (b : Carrier) (hb : b∈SecondParabolic.Overlap.B) : p₂ :=
  ⟨b,SecondParabolic.Overlap.B_le_p₂ hb⟩
private def dR : p₂ := ⟨d,oddGenerator_mem_p₂ 0⟩
private def tL : l₁ := ⟨t,t_mem⟩

private theorem word_relations : u=d⁻¹*z*d ∧ v=t⁻¹*u*t ∧ w=d⁻¹*q*d := by
  refine ⟨?_,?_,?_⟩ <;> apply Sporadic.LeechRelated.J2.inclusion_injective
  all_goals
    simp only [map_mul,map_inv,d,u,v,w,q,t_inclusion,z_inclusion,
      oddGenerator_inclusion,radicalElement_inclusion,sElement_inclusion]
    apply Equiv.ext
    apply allFin
    decide +kernel

private theorem q_commutator : leftB q q_mem_B∈⁅pCore 2 l₁,zpowers (leftB k k_mem_B)⁆ := by
  let r : l₁ := ⟨radicalElement 2,radical_le_l₁ (radicalElement_mem 2)⟩
  have hr : r∈pCore 2 l₁ := by rw [l₁_core_eq]; exact radicalElement_mem 2
  have he : leftB q q_mem_B=r*leftB k k_mem_B*r⁻¹*(leftB k k_mem_B)⁻¹ := by
    apply Subtype.ext
    apply Sporadic.LeechRelated.J2.inclusion_injective
    change inclusion q=inclusion (radicalElement 2*k*(radicalElement 2)⁻¹*k⁻¹)
    rw [map_mul,map_mul,map_mul,map_inv,map_inv,q,k,
      radicalElement_inclusion,radicalElement_inclusion,oddGenerator_inclusion]
    apply Equiv.ext
    apply allFin
    decide +kernel
  rw [he]
  exact commutator_mem_commutator hr (mem_zpowers _)

private theorem q_order : orderOf q=4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (p:=2) (n:=1)
  · intro he
    have hh := congrArg inclusion he
    rw [map_pow,map_one,q,radicalElement_inclusion] at hh
    exact (by decide +kernel : (RadicalStructureData.tablePerm 12)^2≠1) hh
  · apply Sporadic.LeechRelated.J2.inclusion_injective
    rw [map_pow,map_one,q,radicalElement_inclusion]
    apply Equiv.ext
    apply allFin
    decide +kernel

private theorem actor_q_orbit (f : MulAut l₁)
    (hk : f (leftB k k_mem_B)=(leftB k k_mem_B)⁻¹) :
    ∃ m : Fin 6,(f (leftB q q_mem_B):Carrier)=orbit m := by
  have hm := mem_map_of_mem f.toMonoidHom q_commutator
  rw [map_commutator,pCore_map_iso,MonoidHom.map_zpowers] at hm
  simp only [MulEquiv.coe_toMonoidHom,hk,zpowers_inv] at hm
  have hh := mem_map_of_mem l₁.subtype hm
  rw [map_commutator,MonoidHom.map_zpowers,l₁_core_eq,
    map_subgroupOf_eq_of_le radical_le_l₁] at hh
  have ho : orderOf (f (leftB q q_mem_B):Carrier)=4 :=
    (orderOf_coe _).trans ((f.orderOf_eq _).trans ((orderOf_coe _).symm.trans q_order))
  obtain ⟨n,hn⟩ := GeneratorRelations.Orbit.quaternion_orbit _ hh ho
  rcases hn with hn | hn
  · refine ⟨⟨n.val,by omega⟩,?_⟩
    simpa only [orbit,k,q,if_pos n.isLt,Nat.mod_eq_of_lt n.isLt,Subgroup.subtype_apply] using hn
  · refine ⟨⟨n.val+3,by omega⟩,?_⟩
    have hn3 : ¬n.val+3<3 := by omega
    have hmod : (n.val+3)%3=n.val := by omega
    simpa only [orbit,k,q,if_neg hn3,hmod,Subgroup.subtype_apply] using hn

private theorem invert_inverse {A : Type*} [Group A] (a k : A)
    (h : a*k⁻¹*a⁻¹=k) : a*k*a⁻¹=k⁻¹ := by
  calc
    a*k*a⁻¹=(a*k⁻¹*a⁻¹)⁻¹ := by group
    _=k⁻¹ := congrArg Inv.inv h

/-- The two literal endpoint actions force the missing sixth-power relation.
The second relation is essential: first-endpoint automorphisms alone do not
force this central lift. -/
private theorem compatible_actor_data
    (f : MulAut l₁) (g : MulAut p₂)
    (hB : ∀ (b : Carrier) (hb : b∈SecondParabolic.Overlap.B),
      (f (leftB b hb):Carrier)=(g (rightB b hb):Carrier))
    (hk : f (leftB k k_mem_B)=(leftB k k_mem_B)⁻¹)
    (hd : g dR=dR) (hz : g (rightB z z_mem_B)=rightB z z_mem_B) :
    ∃ m : Fin 6,
      (f (leftB q q_mem_B):Carrier)=orbit m ∧
      (f tL:Carrier)*k*(f tL:Carrier)⁻¹=k⁻¹ ∧
      betaRelation k⁻¹ (f tL) (orbit m) (d⁻¹*orbit m*d) ∧
      alphaRelation d z ((f tL:Carrier)⁻¹*u*(f tL:Carrier)) := by
  obtain ⟨m,hm⟩ := actor_q_orbit f hk
  let fl := l₁.subtype.comp f.toMonoidHom
  let gr := p₂.subtype.comp g.toMonoidHom
  have hk' : fl (leftB k k_mem_B)=k⁻¹ := by
    have hh := congrArg l₁.subtype hk
    simpa only [fl,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_inv,leftB,Subgroup.coe_mk,Subgroup.subtype_apply] using hh
  have hd' : gr dR=d := by
    simpa only [gr,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,dR,Subgroup.coe_mk,Subgroup.subtype_apply] using congrArg p₂.subtype hd
  have hz' : gr (rightB z z_mem_B)=z := by
    simpa only [gr,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,rightB,Subgroup.coe_mk,Subgroup.subtype_apply] using congrArg p₂.subtype hz
  have hq' : gr (rightB q q_mem_B)=orbit m := (hB q q_mem_B).symm.trans hm
  have huR : rightB u u_mem_B=dR⁻¹*rightB z z_mem_B*dR := Subtype.ext word_relations.1
  have hwR : rightB w w_mem_B=dR⁻¹*rightB q q_mem_B*dR := Subtype.ext word_relations.2.2
  have hu' : fl (leftB u u_mem_B)=u := by
    rw [show fl (leftB u u_mem_B)=gr (rightB u u_mem_B) from hB u u_mem_B,
      huR,map_mul,map_mul,map_inv,hd',hz']
    exact word_relations.1.symm
  have hw' : fl (leftB w w_mem_B)=d⁻¹*orbit m*d := by
    rw [show fl (leftB w w_mem_B)=gr (rightB w w_mem_B) from hB w w_mem_B,
      hwR,map_mul,map_mul,map_inv,hd',hq']
  have hvL : leftB v v_mem_B=tL⁻¹*leftB u u_mem_B*tL := Subtype.ext word_relations.2.1
  have hv' : gr (rightB v v_mem_B)=(f tL:Carrier)⁻¹*u*(f tL:Carrier) := by
    rw [show gr (rightB v v_mem_B)=fl (leftB v v_mem_B) from (hB v v_mem_B).symm,
      hvL,map_mul,map_mul,map_inv,hu']
    rfl
  have ha : (f tL:Carrier)*k*(f tL:Carrier)⁻¹=k⁻¹ := by
    have he : tL*leftB k k_mem_B*tL⁻¹=(leftB k k_mem_B)⁻¹ := Subtype.ext t_inverts
    have he' := congrArg fl he
    rw [map_mul,map_mul,map_inv,map_inv,hk',inv_inv] at he'
    exact invert_inverse _ _ he'
  refine ⟨m,hm,ha,?_,?_⟩
  · have he : betaRelation (leftB k k_mem_B) tL (leftB q q_mem_B) (leftB w w_mem_B) :=
      Subtype.ext beta_relation
    have he' := congrArg fl he
    simp only [map_mul,hk',show fl (leftB q q_mem_B)=orbit m from hm,hw'] at he'
    exact he'
  · have he : alphaRelation dR (rightB z z_mem_B) (rightB v v_mem_B) :=
      Subtype.ext alpha_relation
    have he' := congrArg gr he
    simp only [map_mul,hd',hz',hv'] at he'
    exact he'


/-- The actual reduced ATLAS amalgam with its full odd Borel. -/
@[expose] public def modelAmalgam := RankTwoAmalgam.ofSubgroups l₁
  SecondParabolic.Overlap.B p₂ SecondParabolic.Overlap.B_le_l₁ SecondParabolic.Overlap.B_le_p₂
/-- The first-endpoint inverter used in the source generator frame. -/
public def sourceInverter : l₁ := tL
/-- The fixed-point-free second-endpoint cubic. -/
public def sourceCubic : p₂ := dR
/-- The common Cartan cubic. -/
public def sourceCartan : SecondParabolic.Overlap.B := ⟨k,k_mem_B⟩
/-- The marked central involution in the first endpoint. -/
public def sourceCentral : SecondParabolic.Overlap.B := ⟨z,z_mem_B⟩

/-- Compatible endpoint actions give the nontrivial central sixth power.
The second inclusion square supplies the relation excluding the spurious lift. -/
public theorem model_actor_sixth (a : RankTwoAmalgam.Iso modelAmalgam modelAmalgam)
    (hk : a.middle sourceCartan=sourceCartan⁻¹)
    (hd : a.right sourceCubic=sourceCubic)
    (hz : a.middle sourceCentral=sourceCentral) :
    (a.left sourceInverter*sourceInverter)^3=modelAmalgam.left sourceCentral := by
  apply Subtype.ext
  change ((a.left tL:Carrier)*t)^3=z
  have hdata : ∃ m : Fin 6,
      (a.left (leftB q q_mem_B):Carrier)=orbit m ∧
      (a.left tL:Carrier)*k*(a.left tL:Carrier)⁻¹=k⁻¹ ∧
      betaRelation k⁻¹ (a.left tL) (orbit m) (d⁻¹*orbit m*d) ∧
      alphaRelation d z ((a.left tL:Carrier)⁻¹*u*(a.left tL:Carrier)) := by
    apply compatible_actor_data a.left a.right
    · intro b hb
      exact (congrArg (fun y : l₁ => (y:Carrier)) (a.left_commutes ⟨b,hb⟩)).trans
        (congrArg (fun y : p₂ => (y:Carrier)) (a.right_commutes ⟨b,hb⟩)).symm
    · have hh := a.left_commutes sourceCartan
      rw [hk,map_inv] at hh
      exact hh
    · exact hd
    · have hh := a.right_commutes sourceCentral
      rw [hz] at hh
      exact hh
  obtain ⟨m,_,ha,hb,hc⟩ := hdata
  exact sift (a.left tL) m ha hb hc

/-- The explicit source inverter is an involution. -/
public theorem sourceInverter_square : sourceInverter^2=1 := by
  change tL^2=1
  exact Subtype.ext t_sq
/-- The marked central element has order two. -/
public theorem sourceCentral_order : orderOf sourceCentral=2 :=
  (orderOf_coe _).symm.trans (orderOf_eq_prime z_sq z_ne_one)
/-- The concrete frame and catalogue marking have both commuting squares. -/
@[expose] public noncomputable def catalogueIso : RankTwoAmalgam.Iso modelAmalgam
    GreenBook.HallJanko.j2Model.toMarking.amalgam where
  left := MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_zero.symm
  middle := MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_B.symm
  right := MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_one.symm
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

/-- The lifting coordinates agree with the endpoint generator frame. -/
public theorem source_coordinates :
    (sourceCartan:Carrier)=oddGenerator 1 ∧
    (sourceCubic:Carrier)=oddGenerator 0 ∧
    (sourceCentral:Carrier)=z ∧
    (sourceInverter:Carrier)=localWord [2,2,0,1,0,2,2,2,2,2,2,0,2,0,2,0,2,0,1,0,2,2,0,1,0,1,0,2,0,2,0] :=
  ⟨rfl,rfl,rfl,rfl⟩

private def outerActor (n : Fin 3) : Extension :=
  intoExtension (k^n.val*(sGenerator 5*sGenerator 0))*outerElement
private def outerActorPerm (n : Fin 3) : Equiv.Perm (Fin 100) :=
  (QuotientData.oddTable 1)^n.val*
    (SylowData.sGenTable 5*SylowData.sGenTable 0)*SecondParabolic.outerTable

private theorem outerActor_mem (n : Fin 3) : outerActor n∈SecondParabolic.Overlap.outerB := by
  apply mul_mem_sup
  apply mem_map_of_mem
  apply SecondParabolic.Overlap.B.mul_mem (SecondParabolic.Overlap.B.pow_mem k_mem_B _)
  apply (show s≤SecondParabolic.Overlap.B from le_sup_left)
  exact s.mul_mem (subset_closure ⟨5,rfl⟩) (subset_closure ⟨0,rfl⟩)
  exact mem_zpowers _

private theorem outerActor_inclusion (n : Fin 3) :
    extension.subtype (outerActor n)=outerActorPerm n := by
  change inclusion (k^n.val*(sGenerator 5*sGenerator 0))*extension.subtype outerElement=_
  rw [map_mul,map_pow,map_mul,k,oddGenerator_inclusion,
    sGenerator_inclusion,sGenerator_inclusion,SecondParabolic.outerElement_inclusion]
  rfl

private theorem outerActor_square (n : Fin 3) : (outerActor n)^2=1 := by
  apply extension.subtype_injective
  rw [map_pow,map_one,outerActor_inclusion]
  have hc : ∀ n : Fin 3,(outerActorPerm n)^2=1 := by
    intro n
    fin_cases n <;> decide +kernel
  exact hc n

private theorem outerActor_outside (n : Fin 3) : outerActor n∉intoExtension.range := by
  intro hn
  apply SecondParabolic.outerElement_not_mem_range
  have hh := intoExtension.range.mul_mem
    (intoExtension.range.inv_mem ⟨k^n.val*(sGenerator 5*sGenerator 0),rfl⟩) hn
  change (intoExtension (k^n.val*(sGenerator 5*sGenerator 0)))⁻¹*
    (intoExtension (k^n.val*(sGenerator 5*sGenerator 0))*outerElement)∈_ at hh
  simpa only [inv_mul_cancel_left] using hh

private theorem actor_inclusion (n : Fin 3) (y : Carrier) :
    inclusion (extensionAction (outerActor n) y)=
      outerActorPerm n*inclusion y*(outerActorPerm n)⁻¹ := by
  change extension.subtype (outerActor n)*inclusion y*(extension.subtype (outerActor n))⁻¹=_
  rw [outerActor_inclusion]

private theorem outerActor_marked (n : Fin 3) :
    extensionAction (outerActor n) k=k⁻¹ ∧
    extensionAction (outerActor n) d=d ∧
    extensionAction (outerActor n) z=z := by
  have hc : ∀ n : Fin 3,
      outerActorPerm n*QuotientData.oddTable 1*(outerActorPerm n)⁻¹=(QuotientData.oddTable 1)⁻¹ ∧
      outerActorPerm n*QuotientData.oddTable 0*(outerActorPerm n)⁻¹=QuotientData.oddTable 0 ∧
      outerActorPerm n*SylowData.sTable 6*(outerActorPerm n)⁻¹=SylowData.sTable 6 := by
    intro n
    fin_cases n <;> decide +kernel
  rcases hc n with ⟨hk,hd,hz⟩
  refine ⟨?_,?_,?_⟩ <;> apply Sporadic.LeechRelated.J2.inclusion_injective
  · simpa only [actor_inclusion,map_inv,k,oddGenerator_inclusion] using hk
  · simpa only [actor_inclusion,d,oddGenerator_inclusion] using hd
  · simpa only [actor_inclusion,z_inclusion] using hz

private theorem sieve_actor_check : ∀ r : Fin 32, ∀ n : Fin 3, ∀ m : Fin 6,
    let R := RadicalStructureData.tablePerm r
    let K := QuotientData.oddTable 1
    let D := QuotientData.oddTable 0
    let Z := SylowData.sTable 6
    let A := R*K^n.val*tPerm
    let Q := orbitPerm m
    let W := D⁻¹*Q*D
    let V := A⁻¹*SylowData.sTable 5*A
    R*K=K*R → betaRelation K⁻¹ A Q W → alphaRelation D Z V →
      ∃ c : Fin 3,
        A=outerActorPerm c*tPerm*(outerActorPerm c)⁻¹ ∧
        Q=outerActorPerm c*RadicalStructureData.tablePerm 12*(outerActorPerm c)⁻¹ := by
  intro r
  fin_cases r <;> dsimp only [betaRelation,alphaRelation] <;> decide +kernel

private theorem sift_actor (a : l₁) (m : Fin 6)
    (ha : (a:Carrier)*k*(a:Carrier)⁻¹=k⁻¹)
    (hb : betaRelation k⁻¹ a (orbit m) (d⁻¹*orbit m*d))
    (hc : alphaRelation d z ((a:Carrier)⁻¹*u*a)) :
    ∃ c : Fin 3, (a:Carrier)=extensionAction (outerActor c) t ∧
      orbit m=extensionAction (outerActor c) q := by
  obtain ⟨r,n,hr,he⟩ := inverter_coordinates a ha
  simp only [betaRelation,alphaRelation] at hb hc
  rw [he] at hb hc ⊢
  have hr' := congrArg inclusion hr
  have hb' := congrArg inclusion hb
  have hc' := congrArg inclusion hc
  simp only [map_mul,map_inv,map_pow,k,d,u,orbit_inclusion,radicalElement_inclusion,
    oddGenerator_inclusion,sElement_inclusion,t_inclusion,z_inclusion] at hr' hb' hc'
  obtain ⟨c,ht,hq⟩ := sieve_actor_check r n m hr' hb' hc'
  refine ⟨c,?_,?_⟩ <;> apply Sporadic.LeechRelated.J2.inclusion_injective
  · simpa only [actor_inclusion,map_mul,map_pow,k,oddGenerator_inclusion,
      radicalElement_inclusion,t_inclusion] using ht
  · simpa only [actor_inclusion,orbit_inclusion,q,radicalElement_inclusion] using hq

/-- Every compatible marked outer action is induced by one element of the
actual full outer Borel, on both whole reduced endpoints simultaneously. -/
public theorem model_actor_lift (a : RankTwoAmalgam.Iso modelAmalgam modelAmalgam)
    (hk : a.middle sourceCartan=sourceCartan⁻¹)
    (hd : a.right sourceCubic=sourceCubic)
    (hz : a.middle sourceCentral=sourceCentral) :
    ∃ y : SecondParabolic.Overlap.outerB,
      y^2=1 ∧ (y:Extension)∉intoExtension.range ∧
      (∀ b : SecondParabolic.Overlap.B,
        (a.middle b:Carrier)=extensionAction y (b:Carrier)) ∧
      (∀ v : l₁,(a.left v:Carrier)=extensionAction y (v:Carrier)) ∧
      (∀ v : p₂,(a.right v:Carrier)=extensionAction y (v:Carrier)) := by
  have hB (b : Carrier) (hb : b∈SecondParabolic.Overlap.B) :
      (a.left (leftB b hb):Carrier)=(a.right (rightB b hb):Carrier) :=
    (congrArg (fun y : l₁ => (y:Carrier)) (a.left_commutes ⟨b,hb⟩)).trans
      (congrArg (fun y : p₂ => (y:Carrier)) (a.right_commutes ⟨b,hb⟩)).symm
  have hkL : a.left (leftB k k_mem_B)=(leftB k k_mem_B)⁻¹ := by
    have hh := a.left_commutes sourceCartan
    rw [hk,map_inv] at hh
    exact hh
  have hzR : a.right (rightB z z_mem_B)=rightB z z_mem_B := by
    have hh := a.right_commutes sourceCentral
    rw [hz] at hh
    exact hh
  obtain ⟨m,hm,ha,hb,hc⟩ := compatible_actor_data a.left a.right hB hkL hd hzR
  obtain ⟨c,ht,hq⟩ := sift_actor (a.left tL) m ha hb hc
  obtain ⟨F,hFk,hFd,hFz,hFq,hFt⟩ := GeneratorRelations.atlas_frame_coordinates
  let f₁ := l₁.subtype.comp a.left.toMonoidHom
  let f₂ := p₂.subtype.comp a.right.toMonoidHom
  let g₁ := (extensionAction (outerActor c)).toMonoidHom.comp l₁.subtype
  let g₂ := (extensionAction (outerActor c)).toMonoidHom.comp p₂.subtype
  have hv (b : SecondParabolic.Overlap.B) :
      f₁ (modelAmalgam.left b)=f₂ (modelAmalgam.right b) := hB b b.property
  have ⟨hck,hcd,hcz⟩ := outerActor_marked c
  have hFLk : F.k=sourceCartan := Subtype.ext hFk
  have hFRd : F.d=sourceCubic := Subtype.ext hFd
  have hFBz : F.z=sourceCentral := Subtype.ext hFz
  have hFLq : modelAmalgam.left F.q=leftB q q_mem_B := Subtype.ext hFq
  have hFLt : F.t=tL := Subtype.ext hFt
  have he : f₁=g₁ ∧ f₂=g₂ := by
    apply F.compatible_hom_ext f₁ g₁ f₂ g₂ hv (fun _ => rfl)
    · rw [hFLk]
      exact (congrArg (fun v : l₁ => (v:Carrier)) hkL).trans hck.symm
    · rw [hFLt]
      exact ht
    · change f₁ (modelAmalgam.left F.q)=g₁ (modelAmalgam.left F.q)
      rw [hFLq]
      exact hm.trans hq
    · rw [hFRd]
      exact (congrArg (fun v : p₂ => (v:Carrier)) hd).trans hcd.symm
    · rw [hFBz]
      exact (congrArg (fun v : p₂ => (v:Carrier)) hzR).trans hcz.symm
  refine ⟨⟨outerActor c,outerActor_mem c⟩,Subtype.ext (outerActor_square c),
    outerActor_outside c,?_,?_,?_⟩
  · intro b
    have hh := congrArg (fun f : l₁ →* Carrier => f (modelAmalgam.left b)) he.1
    exact (congrArg (fun v : l₁ => (v:Carrier)) (a.left_commutes b)).symm.trans hh
  · intro v
    exact congrArg (fun f : l₁ →* Carrier => f v) he.1
  · intro v
    exact congrArg (fun f : p₂ →* Carrier => f v) he.2

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.ProductLift
