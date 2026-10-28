module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoQuaternionAction
public import Theory.GroupTheory.SylowPrimeOrderCoverage
public import Theory.GroupAction.MaximalCosetOrbit
public import Theory.SpecificGroups.SymmetricFive.ThreeCentralizer

/-!
# The two Cartan inverters over the original Hall–Janko pair

A checked word in the retained ATLAS generators supplies an involution
in the concrete first endpoint inverting its cubic. Sylow conjugacy gives
such an inverter for every cubic in that endpoint. The normal order-128
subgroup of the reduced Borel has quotient of order three, which excludes
all these inverters from that Borel. The literal intersection with the
original Borel and the reduced index five then give both endpoint
generation statements. The existing outer and quaternion actors are
retained for the same cubic.

The actual reduced first endpoint is the inverse image of A₅ in every
S₅ coordinate system on the original first core quotient. The two
inverters have a product centralizing the cubic. Its odd image has order
two or six; replacing the reduced inverter t by t*k in the order-two case
makes this image have order six while preserving inversion and generation.
All quotient maps and original/reduced inclusions are literal.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–231,
clause (iv) and the quotient-order step. The repository's first endpoint
is the source's beta endpoint. The word was discovered from the existing
ATLAS J2G1-p100B0 tables; only kernel-checked identities are used here.
The order-twelve lift, the remaining endpoint actions and Aut(J₂)
parabolic recognition remain separate obligations. Genuine reduced
recognition remains explicit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Seed PairNormalizer GeneratorPair
open GeneratorPair.SecondOrbitCertificate
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo

private def inverterWord : List (Fin 3) := [2, 2, 0, 1, 0, 2, 2, 2, 2, 2, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0]
private def inverter : Carrier := localWord inverterWord
private def inverterMap : Fin 100 → Fin 100 := packedMap 3881624724470476115528354446615250408763469728990278980862273442714448688269640655557939205451083296245890251434252628308280335810936193140659017801965556861039639078195667381313023073821921928529120070066492882
private theorem inverterMap_sq : ∀ i, inverterMap (inverterMap i)=i := by
  apply allFin
  decide +kernel
private def inverterPerm : Equiv.Perm (Fin 100) :=
  tablePerm inverterMap inverterMap inverterMap_sq inverterMap_sq
private theorem inclusion_word (w : List (Fin 3)) :
    inclusion (localWord w)=evalWord ![tableA,tableB,tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a,b,b⁻¹] i*localWord w)=_
    rw [map_mul,ih]
    congr 1
    fin_cases i <;> simp [a,b,Sporadic.LeechRelated.J2.inclusion,generatorA_eq_table,generatorB_eq_table]

private theorem inverter_inclusion : inclusion inverter=inverterPerm := by
  rw [inverter,inclusion_word]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem inverter_center_check : ∀ a,
    inverterMap (FirstFusion.OrbitData.value 0 a)=
      FirstFusion.OrbitData.value 0 (inverterMap a) := by
  apply allFin
  decide +kernel

private theorem inverter_mem : inverter∈l₁ := by
  apply mem_centralizer_singleton_iff.mpr
  apply Sporadic.LeechRelated.J2.inclusion_injective
  have hz : Sporadic.LeechRelated.J2.inclusion z=FirstFusion.tPerm := FirstFusion.inclusion_t
  rw [map_mul,map_mul,inverter_inclusion,hz]
  apply Equiv.ext
  intro a
  have hmap (u : Fin 100) : inverterPerm u=inverterMap u := rfl
  simpa only [Equiv.Perm.mul_apply,hmap,←FirstFusion.value_zero] using inverter_center_check a

private theorem inverter_square : inverter^2=1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_pow,map_one,inverter_inclusion]
  apply Equiv.ext
  exact inverterMap_sq

private theorem inverter_inverts : inverter*oddGenerator 1*inverter⁻¹=(oddGenerator 1)⁻¹ := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,map_inv,map_inv,inverter_inclusion,oddGenerator_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem conjugate_inverter {A : Type*} [Group A] [Finite A]
    (hc : ¬9∣Nat.card A) (r t : A) (hr : orderOf r=3)
    (ht : t^2=1) (htr : t*r*t⁻¹=r⁻¹) (k : A) (hk : orderOf k=3) :
    ∃ u : A,u^2=1 ∧ u*k*u⁻¹=k⁻¹ := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n,g,hg⟩ := exists_conjugate_pow_of_orderOf_eq_prime hc hk hr
  let c := MulAut.conj g
  have he : k=c (r^n) := hg
  refine ⟨c t,?_,?_⟩
  · rw [←map_pow,ht,map_one]
  · rw [he]
    have hp : t*r^n*t⁻¹=(r^n)⁻¹ := by
      change (MulAut.conj t) (r^n)=(r^n)⁻¹
      rw [map_pow,show MulAut.conj t r=r⁻¹ from htr,inv_pow]
    simpa only [map_mul,map_inv] using congrArg c hp

private theorem first_cubic_inverter (k : l₁) (hk : orderOf k=3) :
    ∃ t : l₁,t^2=1 ∧ t*k*t⁻¹=k⁻¹ := by
  let r : l₁ := ⟨oddGenerator 1,SecondParabolic.Overlap.B_le_l₁
    ((le_sup_right : zpowers (oddGenerator 1)≤SecondParabolic.Overlap.B) (mem_zpowers _))⟩
  apply conjugate_inverter (by rw [FirstParabolic.card_l₁]; decide) r ⟨inverter,inverter_mem⟩
    ((orderOf_coe r).symm.trans SecondParabolic.Overlap.v_order)
    (Subtype.ext inverter_square) (Subtype.ext inverter_inverts) k hk

private theorem square_cube_one {A : Type*} [Group A] (a : A)
    (h2 : a^2=1) (h3 : a^3=1) : a=1 := by
  simpa only [show 3=2+1 from rfl,pow_succ,h2,one_mul] using h3

private theorem no_inverter_in_two_closed_borel {A : Type*} [Group A] [Finite A]
    (N : Subgroup A) [N.Normal] (hN : Nat.card N=128) (hA : Nat.card A=384)
    (k t : A) (hk : orderOf k=3) (ht : t^2=1) (hinv : t*k*t⁻¹=k⁻¹) : False := by
  let q := QuotientGroup.mk' N
  have hc : Nat.card (A⧸N)=3 := by
    have hh := N.card_mul_index
    rw [index_eq_card,hN,hA] at hh
    omega
  have hcub (a : A⧸N) : a^3=1 := by simpa only [hc] using pow_card_eq_one' (x:=a)
  have htq : q t=1 := square_cube_one _ (by rw [←map_pow,ht,map_one]) (hcub _)
  have hkqinv : q k=(q k)⁻¹ := by
    have hh := congrArg q hinv
    simpa only [map_mul,map_inv,htq,one_mul,inv_one,mul_one] using hh
  have hkq2 : (q k)^2=1 := by
    rw [pow_two]
    exact (congrArg (fun a => a*q k) hkqinv).trans (inv_mul_cancel _)
  have hkN : k∈N := (QuotientGroup.eq_one_iff _).mp (square_cube_one _ hkq2 (hcub _))
  have hd := _root_.orderOf_dvd_natCard (x:=(⟨k,hkN⟩:N))
  rw [←orderOf_coe,hk,hN] at hd
  norm_num at hd

private theorem subgroup_first_inverter {A : Type*} [Group A]
    (P : Subgroup A) (f : P ≃* l₁) (k : A) (hkP : k∈P) (hk : orderOf k=3) :
    ∃ t : A,t∈P ∧ t^2=1 ∧ t*k*t⁻¹=k⁻¹ := by
  let ki : P := ⟨k,hkP⟩
  have hki : orderOf ki=3 := (orderOf_coe ki).symm.trans hk
  obtain ⟨u,hu2,huinv⟩ := first_cubic_inverter (f ki) ((f.orderOf_eq ki).trans hki)
  let t : P := f.symm u
  have ht2 : t^2=1 := by
    change (f.symm u)^2=1
    rw [←map_pow,hu2,map_one]
  have hti : t*ki*t⁻¹=ki⁻¹ := by
    apply f.injective
    simp only [map_mul,map_inv,t,f.apply_symm_apply]
    exact huinv
  exact ⟨t,t.property,congrArg Subtype.val ht2,congrArg Subtype.val hti⟩

open SuzukiContainment GreenBook
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Any prescribed cubic in the literal reduced Borel has a reduced
first-endpoint involution inverting it and lying outside that whole Borel.
It generates the reduced endpoint with B₀ and the original endpoint with B. -/
theorem original_reduced_inverting_generator
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (k : commonBorel L (reducedSylow L S)) (hk : orderOf k=3) :
    ∃ t : G,t∈parabolic L (reducedSylow L S) i ∧ t^2=1 ∧
      t∉commonBorel L S ∧ t*(k:G)*t⁻¹=(k:G)⁻¹ ∧
      commonBorel L (reducedSylow L S) ⊔ zpowers t=parabolic L (reducedSylow L S) i ∧
      commonBorel L S ⊔ zpowers t=parabolic L S i := by
  let B₀ := commonBorel L (reducedSylow L S)
  let P₀ := parabolic L (reducedSylow L S) i
  let f : P₀ ≃* l₁ := e.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_zero)
  obtain ⟨t,ht,htc,htic⟩ := subgroup_first_inverter P₀ f (k:G)
    (commonBorel_le_parabolic i k.property) ((orderOf_coe k).trans hk)
  have hB : Nat.card B₀=384 := (Nat.card_congr b.toEquiv).trans HallJanko.card_j2Model_B
  have htB : (t:G)∉B₀ := by
    intro htB
    let := (reduced_hypothesis h).finite_commonBorel
    let N := (reducedSylow L S).subgroupOf B₀
    let : N.Normal := reduced_sylow_normal h
    have hN : Nat.card N=128 :=
      (Nat.card_congr (subgroupOfEquivOfLe
        (show reducedSylow L S≤B₀ from le_sup_right)).toEquiv).trans (reduced_sylow_card h i e)
    exact no_inverter_in_two_closed_borel N hN hB k ⟨t,htB⟩ hk
      (Subtype.ext htc) (Subtype.ext htic)
  have htBout : (t:G)∉commonBorel L S := by
    intro htB'
    apply htB
    change (t:G)∈commonBorel L (reducedSylow L S)
    rw [←reduced_parabolic_inf_borel h i]
    exact ⟨ht,htB'⟩
  have hi : B₀.relIndex P₀=5 := by
    have hh := (B₀.subgroupOf P₀).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show B₀≤P₀ from commonBorel_le_parabolic i)).toEquiv,hB,reduced_first_card i e] at hh
    change (B₀.subgroupOf P₀).index=5
    omega
  have hg : B₀⊔zpowers (t:G)=P₀ :=
    sup_zpowers_eq_of_relIndex_prime (commonBorel_le_parabolic i) (by decide) hi ht htB
  refine ⟨t,ht,htc,htBout,htic,hg,?_⟩
  calc
    commonBorel L S ⊔ zpowers (t:G) = (B₀⊔zpowers (t:G))⊔commonBorel L S := by
      rw [sup_comm B₀,sup_assoc,sup_eq_right.mpr (reduced_commonBorel_le h),sup_comm]
    _ = P₀⊔commonBorel L S := congrArg (fun A : Subgroup G => A⊔commonBorel L S) hg
    _ = parabolic L S i := reduced_parabolic_supplement h i

/-- One Cartan cubic has both source inverters: the common outer Borel
involution and a reduced first-endpoint involution. The quaternion word
and every original/reduced supplement are retained for the order-twelve step. -/
theorem exists_original_inverting_generators
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (hne : S≠reducedSylow L S) :
    ∃ k x : commonBorel L S, ∃ q t : G,
      orderOf k=3 ∧ (k:G)∈commonBorel L (reducedSylow L S) ∧
      x^2=1 ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧ x*k*x⁻¹=k⁻¹ ∧
      q∈⁅twoCore (parabolic L S i),zpowers (k:G)⁆ ∧
      orderOf q=4 ∧ orderOf ((x:G)*q)=8 ∧
      t∈parabolic L (reducedSylow L S) i ∧ t^2=1 ∧ t∉commonBorel L S ∧
      t*(k:G)*t⁻¹=(k:G)⁻¹ ∧
      commonBorel L (reducedSylow L S) ⊔ zpowers t=parabolic L (reducedSylow L S) i ∧
      commonBorel L S ⊔ zpowers t=parabolic L S i ∧
      (commonBorel L (reducedSylow L S) ⊔ zpowers (x:G)=commonBorel L S ∧
        Disjoint (commonBorel L (reducedSylow L S)) (zpowers (x:G))) ∧
      ∀ r : Fin 2, parabolic L (reducedSylow L S) r ⊔ zpowers (x:G)=parabolic L S r ∧
        Disjoint (parabolic L (reducedSylow L S) r) (zpowers (x:G)) := by
  obtain ⟨k,x,q,hk,hkB,hx,hxB,hinv,hq,hqo,hxq,hB,hP⟩ :=
    exists_original_quaternion_generators h i j e f b hne
  let k₀ : commonBorel L (reducedSylow L S) := ⟨k,hkB⟩
  have hk₀ : orderOf k₀=3 := (orderOf_coe k₀).symm.trans ((orderOf_coe k).trans hk)
  obtain ⟨t,ht,ht2,htB,htk,htgen,htgen'⟩ :=
    original_reduced_inverting_generator h i e b k₀ hk₀
  exact ⟨k,x,q,t,hk,hkB,hx,hxB,hinv,hq,hqo,hxq,ht,ht2,htB,htk,htgen,htgen',hB,hP⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo

namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo

private theorem inverter_product_commute {A : Type*} [Group A] (k x t : A)
    (hx : x*k*x⁻¹=k⁻¹) (ht : t*k*t⁻¹=k⁻¹) : Commute (x*t) k := by
  apply mul_inv_eq_iff_eq_mul.mp
  calc
    (x*t)*k*(x*t)⁻¹=x*(t*k*t⁻¹)*x⁻¹ := by group
    _=x*k⁻¹*x⁻¹ := by rw [ht]
    _=(x*k*x⁻¹)⁻¹ := by group
    _=k := by rw [hx,inv_inv]

private theorem cubic_translate_inverter {A : Type*} [Group A] (k t : A)
    (ht : t^2=1) (hi : t*k*t⁻¹=k⁻¹) :
    (t*k)^2=1 ∧ (t*k)*k*(t*k)⁻¹=k⁻¹ := by
  constructor
  · calc
      (t*k)^2=(t*k*t⁻¹)*(t^2)*k := by simp only [pow_two]; group
      _=1 := by rw [hi,ht]; simp
  · calc
      (t*k)*k*(t*k)⁻¹=t*k*t⁻¹ := by group
      _=k⁻¹ := hi

private theorem symmetric_five_centralizing_odd
    (k y : Equiv.Perm (Fin 5)) (hk : orderOf k=3)
    (hy : y∉alternatingGroup (Fin 5)) (hc : Commute y k) :
    orderOf y=2 ∨ orderOf y=6 := by
  have hm : y∈centralizer ({k} : Set (Equiv.Perm (Fin 5))) :=
    mem_centralizer_singleton_iff.mpr hc.eq
  have hd := _root_.orderOf_dvd_natCard (x:=(⟨y,hm⟩:centralizer ({k} : Set (Equiv.Perm (Fin 5)))))
  rw [←orderOf_coe,Theory.SpecificGroups.SymmetricFive.centralizer_three_card k hk] at hd
  have hn : ¬y^3=1 := by
    intro hh
    apply hy
    exact (show ∀ a : Equiv.Perm (Fin 5),a^3=1 → a∈alternatingGroup (Fin 5) by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide +kernel) y hh
  have hnot : ¬orderOf y∣3 := by simpa only [orderOf_dvd_iff_pow_eq_one] using hn
  have hb := Nat.le_of_dvd (by decide : 0<6) hd
  interval_cases (orderOf y) <;> norm_num at *

/-- Choose an inverter or its cubic translate so that its product with the
odd actor has order six in the specified symmetric-five image. -/
public theorem select_product_six {A : Type*} [Group A]
    (v : A →* Equiv.Perm (Fin 5)) (k x t : A)
    (hk : orderOf (v k)=3) (hxodd : v x∉alternatingGroup (Fin 5))
    (hteven : v t∈alternatingGroup (Fin 5))
    (hxk : x*k*x⁻¹=k⁻¹) (ht2 : t^2=1) (htk : t*k*t⁻¹=k⁻¹) :
    ∃ u : A,(u=t ∨ u=t*k) ∧ u^2=1 ∧ u*k*u⁻¹=k⁻¹ ∧ orderOf (v (x*u))=6 := by
  have hc := inverter_product_commute k x t hxk htk
  have hc' : Commute (v (x*t)) (v k) := hc.map v
  have hyodd : v (x*t)∉alternatingGroup (Fin 5) := by
    rw [map_mul]
    exact fun he => hxodd ((alternatingGroup (Fin 5)).mul_mem_cancel_right hteven |>.mp he)
  rcases symmetric_five_centralizing_odd (v k) (v (x*t)) hk hyodd hc' with ho | ho
  · obtain ⟨hu2,huk⟩ := cubic_translate_inverter k t ht2 htk
    refine ⟨t*k,Or.inr rfl,hu2,huk,?_⟩
    rw [←mul_assoc,map_mul]
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hc' (by rw [ho,hk]; decide),ho,hk]
  · exact ⟨t,Or.inl rfl,ht2,htk,ho⟩

open SuzukiContainment GreenBook
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Under any S₅ coordinates on the original first core quotient, the
literal reduced endpoint is precisely the inverse image of A₅. -/
theorem original_first_quotient_reduced
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (hne : S≠reducedSylow L S)
    (d : (parabolic L S i ⧸ pCore 2 (parabolic L S i)) ≃* Equiv.Perm (Fin 5))
    (y : parabolic L S i) :
    d (QuotientGroup.mk' (pCore 2 (parabolic L S i)) y)∈alternatingGroup (Fin 5) ↔
      (y:G)∈parabolic L (reducedSylow L S) i := by
  let P := parabolic L S i
  let N := (parabolic L (reducedSylow L S) i).subgroupOf P
  let v := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hv : Function.Surjective v := d.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : v.ker≤N := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
    intro z hz
    exact (show reducedSylow L S≤parabolic L (reducedSylow L S) i from le_sup_right.trans le_sup_left)
      (parabolic_core_le_reducedSylow h i (mem_map_of_mem P.subtype hz))
  have hi : N.index=2 :=
    (parabolic_extension_index h i).trans (original_borel_index_two_of_ne h i e hne)
  have hJ : N.map v=alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two ((N.index_map_eq hv hk).trans hi)
  change v y∈alternatingGroup (Fin 5) ↔ y∈N
  rw [←hJ]
  change y∈(N.map v).comap v ↔ y∈N
  rw [comap_map_eq,sup_eq_left.mpr hk]

private theorem sup_zpowers_mul {A : Type*} [Group A] (B : Subgroup A)
    (k t : A) (hk : k∈B) : B⊔zpowers (t*k)=B⊔zpowers t := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply zpowers_le.mpr
    exact (B⊔zpowers t).mul_mem
      ((show zpowers t≤B⊔zpowers t from le_sup_right) (mem_zpowers t))
      ((show B≤B⊔zpowers t from le_sup_left) hk)
  · apply sup_le le_sup_left
    apply zpowers_le.mpr
    have hh : (t*k)*k⁻¹∈B⊔zpowers (t*k) :=
      (B⊔zpowers (t*k)).mul_mem
        ((show zpowers (t*k)≤B⊔zpowers (t*k) from le_sup_right) (mem_zpowers _))
        ((show B≤B⊔zpowers (t*k) from le_sup_left) (B.inv_mem hk))
    simpa only [mul_inv_cancel_right] using hh

/-- Select the reduced inverter so that the product with the original outer
involution has order six in the literal first two-core quotient. -/
theorem original_inverter_product_six
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (hne : S≠reducedSylow L S) (k x : commonBorel L S)
    (hk : orderOf k=3) (hkB : (k:G)∈commonBorel L (reducedSylow L S))
    (hxB : (x:G)∉commonBorel L (reducedSylow L S))
    (hinv : x*k*x⁻¹=k⁻¹) :
    ∃ t : parabolic L S i,
      (t:G)∈parabolic L (reducedSylow L S) i ∧ t^2=1 ∧
      (t:G)∉commonBorel L S ∧ t*(Subgroup.inclusion (commonBorel_le_parabolic i) k)*t⁻¹=
        (Subgroup.inclusion (commonBorel_le_parabolic i) k)⁻¹ ∧
      orderOf (QuotientGroup.mk' (pCore 2 (parabolic L S i))
        (Subgroup.inclusion (commonBorel_le_parabolic i) x*t))=6 ∧
      commonBorel L (reducedSylow L S) ⊔ zpowers (t:G)=parabolic L (reducedSylow L S) i ∧
      commonBorel L S ⊔ zpowers (t:G)=parabolic L S i := by
  let := h.finite_parabolic i
  let P := parabolic L S i
  let ki : P := ⟨k,commonBorel_le_parabolic i k.property⟩
  let xi : P := ⟨x,commonBorel_le_parabolic i x.property⟩
  let k₀ : commonBorel L (reducedSylow L S) := ⟨k,hkB⟩
  have hk₀ : orderOf k₀=3 := (orderOf_coe k₀).symm.trans ((orderOf_coe k).trans hk)
  obtain ⟨t,ht,ht2,htB,htk,htgen,htgen'⟩ := original_reduced_inverting_generator h i e b k₀ hk₀
  let ti : P := ⟨t,reduced_parabolic_le h i ht⟩
  obtain ⟨d⟩ := original_first_quotient_of_ne h i e hne
  let q := QuotientGroup.mk' (pCore 2 P)
  let v := d.toMonoidHom.comp q
  have hki : orderOf ki=3 := (orderOf_coe ki).symm.trans ((orderOf_coe k).trans hk)
  have hk3 : ki^3=1 := by rw [←hki,pow_orderOf_eq_one]
  have hvk : orderOf (v ki)=3 := by
    apply orderOf_eq_prime
    · rw [←map_pow,hk3,map_one]
    · intro he
      have hq : q ki=1 := d.injective (he.trans d.map_one.symm)
      have hkQ : ki∈pCore 2 P := (QuotientGroup.eq_one_iff _).mp hq
      have hd := _root_.orderOf_dvd_natCard (x:=(⟨ki,hkQ⟩:pCore 2 P))
      rw [←orderOf_coe,hki,original_core_card h i e] at hd
      norm_num at hd
  have hxodd : v xi∉alternatingGroup (Fin 5) := by
    intro he
    have hxN := (original_first_quotient_reduced h i e hne d xi).mp he
    apply hxB
    rw [←reduced_parabolic_inf_borel h i]
    exact ⟨hxN,x.property⟩
  have hteven : v ti∈alternatingGroup (Fin 5) :=
    (original_first_quotient_reduced h i e hne d ti).mpr ht
  have hxi : xi*ki*xi⁻¹=ki⁻¹ :=
    Subtype.ext (congrArg (fun y : commonBorel L S => (y:G)) hinv)
  obtain ⟨u,hu,hu2,huk,hu6⟩ := select_product_six v ki xi ti hvk hxodd hteven
    hxi (Subtype.ext ht2) (Subtype.ext htk)
  have huN : (u:G)∈parabolic L (reducedSylow L S) i := by
    rcases hu with rfl | rfl
    · exact ht
    · exact mul_mem ht (commonBorel_le_parabolic i hkB)
  have huB : (u:G)∉commonBorel L S := by
    rcases hu with rfl | rfl
    · exact htB
    · exact fun he => htB ((commonBorel L S).mul_mem_cancel_right k.property |>.mp he)
  have hugen : commonBorel L (reducedSylow L S) ⊔ zpowers (u:G)=parabolic L (reducedSylow L S) i := by
    rcases hu with rfl | rfl
    · exact htgen
    · exact (sup_zpowers_mul _ (k:G) t hkB).trans htgen
  have hugen' : commonBorel L S ⊔ zpowers (u:G)=parabolic L S i := by
    rcases hu with rfl | rfl
    · exact htgen'
    · exact (sup_zpowers_mul _ (k:G) t k.property).trans htgen'
  exact ⟨u,huN,hu2,huB,huk,(d.orderOf_eq (q (xi*u))).symm.trans hu6,hugen,hugen'⟩

private theorem actors_in_endpoint {A : Type*} [Group A]
    (B₀ B P₀ P : Subgroup A) (hBP : B≤P)
    (hs : ∃ k x : B,orderOf k=3 ∧ (k:A)∈B₀ ∧ x^2=1 ∧ (x:A)∉B₀ ∧
      x*k*x⁻¹=k⁻¹ ∧ ∃ t : P,(t:A)∈P₀ ∧ t^2=1 ∧ (t:A)∉B ∧
        t*(Subgroup.inclusion hBP k)*t⁻¹=(Subgroup.inclusion hBP k)⁻¹ ∧
        orderOf (QuotientGroup.mk' (pCore 2 P) (Subgroup.inclusion hBP x*t))=6 ∧
        B₀⊔zpowers (t:A)=P₀ ∧ B⊔zpowers (t:A)=P) :
    ∃ k x t : P,orderOf k=3 ∧ (k:A)∈B₀ ∧ x^2=1 ∧ (x:A)∈B ∧ (x:A)∉B₀ ∧
      x*k*x⁻¹=k⁻¹ ∧ (t:A)∈P₀ ∧ t^2=1 ∧ (t:A)∉B ∧ t*k*t⁻¹=k⁻¹ ∧
      orderOf (QuotientGroup.mk' (pCore 2 P) (x*t))=6 ∧
      B₀⊔zpowers (t:A)=P₀ ∧ B⊔zpowers (t:A)=P := by
  obtain ⟨k,x,hk,hkB,hx,hxB,hinv,t,ht,ht2,htB,htk,ho,hg,hg'⟩ := hs
  let ki : P := ⟨k,hBP k.property⟩
  let xi : P := ⟨x,hBP x.property⟩
  have hk' : orderOf ki=3 := (orderOf_coe ki).symm.trans ((orderOf_coe k).trans hk)
  have hx' : xi^2=1 := Subtype.ext (congrArg (fun y : B => (y:A)) hx)
  have hinv' : xi*ki*xi⁻¹=ki⁻¹ := Subtype.ext (congrArg (fun y : B => (y:A)) hinv)
  exact ⟨ki,xi,t,hk',hkB,hx',x.property,hxB,hinv',ht,ht2,htB,htk,ho,hg,hg'⟩

/-- The order-six product is realized in the same original first endpoint,
with both full Borel generations and the literal reduced inclusion. -/
theorem exists_original_product_six_actors
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (hne : S≠reducedSylow L S) :
    ∃ k x t : parabolic L S i,
      orderOf k=3 ∧ (k:G)∈commonBorel L (reducedSylow L S) ∧
      x^2=1 ∧ (x:G)∈commonBorel L S ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧
      x*k*x⁻¹=k⁻¹ ∧ (t:G)∈parabolic L (reducedSylow L S) i ∧ t^2=1 ∧
      (t:G)∉commonBorel L S ∧ t*k*t⁻¹=k⁻¹ ∧
      orderOf (QuotientGroup.mk' (pCore 2 (parabolic L S i)) (x*t))=6 ∧
      commonBorel L (reducedSylow L S) ⊔ zpowers (t:G)=parabolic L (reducedSylow L S) i ∧
      commonBorel L S ⊔ zpowers (t:G)=parabolic L S i := by
  apply actors_in_endpoint _ _ _ _ (commonBorel_le_parabolic i)
  obtain ⟨k,x,hk,hkB,hx,hxB,hinv,_⟩ :=
    exists_original_simultaneous_generators h i j e f b hne
  obtain ⟨t,ht,ht2,htB,htk,ho,hg,hg'⟩ :=
    original_inverter_product_six h i e b hne k x hk hkB hxB hinv
  exact ⟨k,x,hk,hkB,hx,hxB,hinv,t,ht,ht2,htB,htk,ho,hg,hg'⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
