module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoSplitting
public import Theory.SpecificGroups.MinusExtraspecial.CubicAction.NormalForm
public import Theory.GroupTheory.CentralProductEquivalence

public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The outer quaternion-word relation over the reduced Hall–Janko pair

The concrete reduced first core is identified with Q₈ ∘ D₈ by gluing its
proved factor embeddings on their common central involution. Transport
through the unchanged original core and cubic normal form makes the
chosen Cartan cubic act as the quaternion cycle. A 32-row checked norm
calculation then gives an order-four quaternion element whose product
with any inverting involution has order eight.

Two explicit cubic commutators express every quaternion element, so the
witness belongs to the actual [O₂(Pᵢ),k], rather than just an abstract
quaternion group. Characteristic two and the original core order prove
the cubic action nontrivial. The original full Borel and both reduced
endpoint supplements are retained in the common-generator application.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–230,
the choice of q in [Qβ,K] and the order of xq. This proves that relation
for a suitable order-four q; it does not assert the separate order-twelve
product on p.231 or an Aut(J₂) parabolic equivalence. The genuine reduced
comparison remains an explicit source input.
-/

public noncomputable section
open Subgroup MinusExtraspecial
open Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.RadicalStructureData
open MinusExtraspecial.CubicAction
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo

private theorem radical_overlap (q : QuaternionGroup 2) (d : DihedralGroup 4) :
    radicalQuaternionHom q = radicalDihedralHom d ↔
      (q=1 ∧ d=1) ∨ (q=.a 2 ∧ d=.r 2) := by
  change radicalEnum (quaternionIndex q)=radicalEnum (dihedralIndex d) ↔ _
  rw [radicalEnum_injective.eq_iff]
  revert q d
  decide +kernel

private theorem radical_coordinates : Nonempty (radical ≃* Model) := by
  let Q := quaternion.range
  let D := dihedral.range
  let eq : radicalQuaternionFactor ≃* Q := radicalQuaternionEquiv.trans
    (MonoidHom.ofInjective quaternion_injective)
  let ed : radicalDihedralFactor ≃* D := radicalDihedralEquiv.trans
    (MonoidHom.ofInjective dihedral_injective)
  have hgen : Q ⊔ D=⊤ := by
    apply top_unique
    intro x _
    obtain ⟨q,d,rfl⟩ := factors_generate x
    exact mul_mem_sup ⟨q,rfl⟩ ⟨d,rfl⟩
  have hcomm : ∀ q : Q, ∀ d : D, Commute (q:Model) (d:Model) := by
    rintro ⟨_,q,rfl⟩ ⟨_,d,rfl⟩
    exact factors_commute q d
  have hcompat : ∀ q : radicalQuaternionFactor, ∀ d : radicalDihedralFactor,
      (q:radical)=(d:radical) ↔ (eq q:Model)=(ed d:Model) := by
    intro q d
    have hq : radicalQuaternionHom (radicalQuaternionEquiv q)=q :=
      MonoidHom.apply_ofInjective_symm radicalQuaternionHom_injective q
    have hd : radicalDihedralHom (radicalDihedralEquiv d)=d :=
      MonoidHom.apply_ofInjective_symm radicalDihedralHom_injective d
    change (q:radical)=(d:radical) ↔
      quaternion (radicalQuaternionEquiv q)=dihedral (radicalDihedralEquiv d)
    rw [←hq,←hd,radical_overlap,factors_overlap]
  obtain ⟨e,_,_⟩ := exists_mulEquiv_of_central_products
    radicalQuaternionFactor radicalDihedralFactor Q D
    (fun q d => radical_factors_commute q q.property d d.property)
    hcomm radical_factors_sup hgen eq ed hcompat
  exact ⟨e⟩


private def quaternionWord (a b : Model) : QuaternionGroup 2 → Model
  | .a i => a^i.val
  | .xa i => b*a^i.val

private theorem norm_table : ∀ a : Model, a^2≠1 →
    let b := cycle (cycle a)*a⁻¹
    b^2=a^2 → b*a=a⁻¹*b →
    ∃ q : QuaternionGroup 2, q^2≠1 ∧ (quaternion q * quaternionWord a b q)^2=quaternion z := by
  decide +kernel

private theorem quaternionWord_aut (f : MulAut Model) (q : QuaternionGroup 2) :
    quaternionWord (f (generators 0)) (f (generators 1)) q=f (quaternion q) := by
  have hh := aut_word f (quaternion q)
  cases q <;> simpa [MinusExtraspecial.word,quaternion,quaternionWord] using hh

private theorem normalized_inverter_norm (f : MulAut Model)
    (hinv : f*cycle=cycle^2*f) :
    ∃ q : QuaternionGroup 2, q^2≠1 ∧ (quaternion q*f (quaternion q))^2=quaternion z := by
  let a := f (generators 0)
  let b := f (generators 1)
  have ha : a^2≠1 := by
    intro he
    have hq : (generators 0)^2=1 := f.injective (by simpa only [map_pow,map_one] using he)
    exact (by decide : (generators 0)^2≠1) hq
  have hb : b^2=a^2 := by
    rw [←map_pow,←map_pow]
    exact congrArg f (by decide : (generators 1)^2=(generators 0)^2)
  have hba : b*a=a⁻¹*b := by
    rw [←map_inv,←map_mul,←map_mul]
    exact congrArg f (by decide : generators 1*generators 0=(generators 0)⁻¹*generators 1)
  have he : b=cycle (cycle a)*a⁻¹ := by
    have hh := DFunLike.congr_fun hinv (generators 0)
    change f (cycle (generators 0))=cycle (cycle (f (generators 0))) at hh
    rw [show cycle (generators 0)=generators 1*generators 0 from by decide,map_mul] at hh
    exact eq_mul_inv_iff_mul_eq.mpr hh
  obtain ⟨q,hq2,hq⟩ := norm_table a ha (he ▸ hb) (he ▸ hba)
  refine ⟨q,hq2,?_⟩
  rw [←he,quaternionWord_aut] at hq
  exact hq

open Subgroup
private theorem core_inverter_order_eight {P : Type*} [Group P]
    (Q : Subgroup P) [Q.Normal] (e : Q ≃* Model) (k x : P)
    (hk : k^3=1) (ha : (MulAut.conjNormal k : MulAut Q)≠1)
    (hx : x^2=1) (hinv : x*k*x⁻¹=k⁻¹) :
    ∃ q : P, q∈⁅Q,zpowers k⁆ ∧ orderOf q=4 ∧ orderOf (q*x)=8 := by
  let a : P →* MulAut Model := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have ha3 : a k^3=1 := by rw [←map_pow,hk,map_one]
  have hane : a k≠1 := by
    intro hh
    apply ha
    exact (MulAut.congr e).injective (hh.trans (map_one (MulAut.congr e)).symm)
  obtain ⟨f,hf⟩ := hasCubicNormalForm (a k) ha3 hane
  let E : Q ≃* Model := e.trans f
  let b : P →* MulAut Model := (MulAut.congr E).toMonoidHom.comp MulAut.conjNormal
  have hbk : b k=cycle := by
    apply DFunLike.ext
    intro y
    change f (e (MulAut.conjNormal k (e.symm (f.symm y))))=cycle y
    change f (a k (f.symm y))=cycle y
    rw [hf,f.apply_symm_apply]
  have hconj (u : Q) : E (MulAut.conjNormal k u)=cycle (E u) := by
    have hh := DFunLike.congr_fun hbk (E u)
    change E (MulAut.conjNormal k (E.symm (E u)))=cycle (E u) at hh
    simpa only [E.symm_apply_apply] using hh
  have hcyinv : cycle⁻¹=cycle^2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [←pow_succ'] using cycle_cube
  have hbinv : b x*cycle=cycle^2*b x := by
    have hh := congrArg b hinv
    simp only [map_mul,map_inv,hbk,hcyinv] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨q,hq2,hnorm⟩ := normalized_inverter_norm (b x) hbinv
  let u : Q := E.symm (quaternion q)
  have hu : orderOf (u:P)=4 := by
    rw [orderOf_coe u,←E.orderOf_eq u]
    change orderOf (E (E.symm (quaternion q)))=4
    rw [E.apply_symm_apply,orderOf_injective quaternion quaternion_injective]
    have hq4 : q^4=1 := (show ∀ y : QuaternionGroup 2,y^4=1 by decide +kernel) q
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_pow (p:=2) (n:=1) hq2 hq4
  have hm : (u:P)∈⁅Q,zpowers k⁆ := by
    obtain ⟨r,s,hrs⟩ := quaternion_commutators q
    let r' : Q := E.symm (quaternion r)
    let s' : Q := E.symm (quaternion s)
    have hh : (r'*MulAut.conjNormal k r'⁻¹)*(s'*MulAut.conjNormal k s'⁻¹)=u := by
      apply E.injective
      simp only [map_mul,hconj,map_inv,r',s',u,E.apply_symm_apply]
      simpa only [map_mul,map_inv,cycle_quaternion] using congrArg quaternion hrs
    have hc : ((r':P)*k*(r':P)⁻¹*k⁻¹)*((s':P)*k*(s':P)⁻¹*k⁻¹)=(u:P) := by
      simpa only [Subgroup.coe_mul,Subgroup.coe_inv,MulAut.conjNormal_apply,mul_assoc] using congrArg Subtype.val hh
    rw [←hc]
    exact mul_mem (commutator_mem_commutator r'.property (mem_zpowers k))
      (commutator_mem_commutator s'.property (mem_zpowers k))
  have hxinv : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  let v : Q := u*MulAut.conjNormal x u
  have hv : (v:P)=((u:P)*x)^2 := by
    change (u:P)*(x*(u:P)*x⁻¹)=((u:P)*x)^2
    rw [hxinv,pow_two]
    simp only [mul_assoc]
  have hvnorm : (E v)^2=quaternion z := by
    change (E (u*MulAut.conjNormal x u))^2=quaternion z
    rw [map_mul]
    have hh : E (MulAut.conjNormal x u)=b x (quaternion q) := by
      change E (MulAut.conjNormal x (E.symm (quaternion q)))=
        E (MulAut.conjNormal x (E.symm (quaternion q)))
      rfl
    rw [hh,show E u=quaternion q from E.apply_symm_apply _]
    exact hnorm
  have hv2 : v^2≠1 := by
    intro hh
    have hz1 : quaternion z=(1:Model) := by rw [←hvnorm,←map_pow,hh,map_one]
    exact (by decide : quaternion z≠(1:Model)) hz1
  have hv4 : v^4=1 := by
    apply E.injective
    rw [map_pow,map_one,show 4=2*2 from rfl,pow_mul,hvnorm]
    decide +kernel
  have hp4 : ((u:P)*x)^4≠1 := by
    intro hh
    apply hv2
    apply Subtype.ext
    change (v:P)^2=1
    rw [hv,←pow_mul]
    exact hh
  have hp8 : ((u:P)*x)^8=1 := by
    have hh := congrArg Subtype.val hv4
    change (v:P)^4=1 at hh
    rwa [hv,←pow_mul] at hh
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨u,hm,hu,orderOf_eq_prime_pow (p:=2) (n:=2) hp4 hp8⟩

open SuzukiContainment GreenBook
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- For any cubic and inverting involution in the full original Borel,
there is an order-four element in the actual cubic commutator factor whose
product with that involution has order eight. -/
theorem original_quaternion_word
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (k x : commonBorel L S) (hk : orderOf k=3) (hx : x^2=1)
    (hinv : x*k*x⁻¹=k⁻¹) :
    ∃ q : G, q∈⁅twoCore (parabolic L S i),zpowers (k:G)⁆ ∧
      orderOf q=4 ∧ orderOf ((x:G)*q)=8 := by
  let := h.finite_parabolic i
  let P := parabolic L S i
  let Q := pCore 2 P
  let ki : P := inclusion (commonBorel_le_parabolic i) k
  let xi : P := inclusion (commonBorel_le_parabolic i) x
  have hk3 : ki^3=1 := by
    have hh : k^3=1 := by rw [←hk,pow_orderOf_eq_one]
    exact (map_pow _ k 3).symm.trans ((congrArg (inclusion (commonBorel_le_parabolic i)) hh).trans (map_one _))
  have hko : orderOf ki=3 := (orderOf_injective
    (inclusion (commonBorel_le_parabolic i)) (inclusion_injective _) k).trans hk
  have hxi : xi^2=1 := by
    change (inclusion (commonBorel_le_parabolic i) x)^2=1
    simpa only [map_pow,map_one] using congrArg (inclusion (commonBorel_le_parabolic i)) hx
  have hinvi : xi*ki*xi⁻¹=ki⁻¹ := by
    simpa only [map_mul,map_inv] using congrArg (inclusion (commonBorel_le_parabolic i)) hinv
  have ha : (MulAut.conjNormal ki : MulAut Q)≠1 := by
    intro hh
    have hc : ki∈centralizer (Q:Set P) := by
      apply mem_centralizer_iff.mpr
      intro v hv
      have he := congrArg (fun f : MulAut Q => (f ⟨v,hv⟩:P)) hh
      change ki*v*ki⁻¹=v at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hkQ : ki∈Q :=
      (ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two i) hc
    have hd := _root_.orderOf_dvd_natCard (x:=(⟨ki,hkQ⟩:Q))
    rw [←orderOf_coe (⟨ki,hkQ⟩:Q),hko] at hd
    change 3 ∣ Nat.card (pCore 2 (parabolic L S i)) at hd
    rw [original_core_card h i e] at hd
    norm_num at hd
  obtain ⟨c⟩ := radical_coordinates
  obtain ⟨q,hq,hqo,hxq⟩ := core_inverter_order_eight Q
    ((originalCoreEquiv h i e).trans c) ki xi hk3 ha hxi hinvi
  have hqm := mem_map_of_mem P.subtype hq
  rw [map_commutator,MonoidHom.map_zpowers] at hqm
  refine ⟨q,hqm,?_,?_⟩
  · exact (orderOf_coe q).trans hqo
  · have hh := (MulAut.conj (x:G)).orderOf_eq ((q:G)*(xi:G))
    have he : MulAut.conj (x:G) ((q:G)*(xi:G))=(x:G)*(q:G) := by
      change (x:G)*((q:G)*(x:G))*(x:G)⁻¹=(x:G)*(q:G)
      simp only [mul_assoc,mul_inv_cancel,mul_one]
    rw [he] at hh
    exact hh.trans ((orderOf_coe (q*xi)).trans hxq)

/-- The common splitting involution has the source quaternion-word
relation in the original first endpoint. The full Borel and both actual
reduced endpoint supplements are retained. -/
theorem exists_original_quaternion_generators
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (hne : S≠reducedSylow L S) :
    ∃ k x : commonBorel L S, ∃ q : G,
      orderOf k=3 ∧ (k:G)∈commonBorel L (reducedSylow L S) ∧
      x^2=1 ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧ x*k*x⁻¹=k⁻¹ ∧
      q∈⁅twoCore (parabolic L S i),zpowers (k:G)⁆ ∧
      orderOf q=4 ∧ orderOf ((x:G)*q)=8 ∧
      (commonBorel L (reducedSylow L S) ⊔ zpowers (x:G)=commonBorel L S ∧
        Disjoint (commonBorel L (reducedSylow L S)) (zpowers (x:G))) ∧
      ∀ r : Fin 2, parabolic L (reducedSylow L S) r ⊔ zpowers (x:G)=parabolic L S r ∧
        Disjoint (parabolic L (reducedSylow L S) r) (zpowers (x:G)) := by
  obtain ⟨k,x,hk,hkB,hx,hxB,hinv,_,_,hB,hP⟩ :=
    exists_original_simultaneous_generators h i j e f b hne
  obtain ⟨q,hq,hqo,hxq⟩ := original_quaternion_word h i e k x hk hx hinv
  exact ⟨k,x,q,hk,hkB,hx,hxB,hinv,hq,hqo,hxq,hB,hP⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
