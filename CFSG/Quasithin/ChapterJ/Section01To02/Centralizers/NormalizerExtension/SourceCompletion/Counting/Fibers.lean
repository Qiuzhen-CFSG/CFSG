module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.InvolutionGeometry
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Counting.SectionCounts
public import Theory.SpecificGroups.SymmetricFive.EvenInvolutions
import all CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting.Count

/-!
# The fifteen actual z-class fibers

The original Ru2 map identifies each z-class fiber over an involution with
filtered inverted elements of Q. Its surjectivity lifts the S5 conjugacy of
all fifteen even involutions. The earlier source provides a z-class involution
in K outside Q and transports it inside H to an inverter of the original B.
Thus one computed quaternion fiber gives the literal total count.

Source: Aschbacher–Smith J.2.7(8), printed p.437.
-/

open Subgroup Representation Representation.BinaryConjugationSection
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (c:Choices d)

public theorem K_normalized_source : d.toTypeRuSetup.H≤normalizer d.toTypeRuSetup.K := by
  apply (normal_subgroupOf_iff_le_normalizer d.toTypeRuSetup.K_le_H).mp
  rw [d.toTypeRuSetup.K_subgroupOf_H]
  infer_instance

public theorem mem_K_iff_even_source (x:d.toTypeRuSetup.H) :
    (x:G)∈d.toTypeRuSetup.K ↔ d.ru2.quotientMap x∈alternatingGroup (Fin 5) := by
  have hk : d.ru2.quotientMap.ker≤d.toTypeRuSetup.K.subgroupOf d.toTypeRuSetup.H := by
    rw [d.ru2.quotient_kernel]
    exact fun _ h=>d.Q_le_K h
  rw [←d.toTypeRuSetup.quotientMap_K]
  change x∈d.toTypeRuSetup.K.subgroupOf d.toTypeRuSetup.H ↔
    x∈((d.toTypeRuSetup.K.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap).comap _
  rw [comap_map_eq_self hk]

public theorem exists_middle_inverter_source : ∃i:d.toTypeRuSetup.H,
    (i:G)∈d.toTypeRuSetup.K ∧ (i:G)∉d.toTypeRuSetup.Q ∧ orderOf (i:G)=2 ∧
      c.InvertsB (i:G) ∧ IsConj c.z (i:G) := by
  obtain ⟨w,hzw,hw⟩:=InvolutionGeometry.exists_z_class_mem_K_diff_Q c
    (SourceCompletion.fusion c).2.2.1
  have hwH:=d.toTypeRuSetup.K_le_H hw.1
  obtain ⟨h,hh,hbi⟩:=c.H_inverter_transport_source w hwH hw.2.1 hw.2.2
  have hiH:=d.toTypeRuSetup.H.mul_mem (d.toTypeRuSetup.H.mul_mem hh hwH)
    (d.toTypeRuSetup.H.inv_mem hh)
  refine ⟨⟨h*w*h⁻¹,hiH⟩,?_,?_,?_,hbi,?_⟩
  · exact (mem_normalizer_iff.mp (K_normalized_source (d:=d) hh) w).mp hw.1
  · exact fun hn=>hw.2.1 ((mem_normalizer_iff.mp (d.ru2.six.normalized hh) w).mpr hn)
  · exact ((MulAut.conj h).orderOf_eq w).trans hw.2.2
  · exact hzw.trans (isConj_iff.mpr ⟨h,rfl⟩)


public theorem z_class_order (x:G) (hx:IsConj c.z x) : orderOf x=2 := by
  obtain ⟨g,hg⟩:=isConj_iff.mp hx
  rw [←hg]
  exact ((MulAut.conj g).orderOf_eq c.z).trans (SourceCompletion.z_order c)

public abbrev zFiber (t:S5) := {x:d.toTypeRuSetup.H//IsConj c.z (x:G) ∧ d.ru2.quotientMap x=t}

public noncomputable def zFiberEquivInverting (i:d.toTypeRuSetup.H) (hi:(i:G)^2=1) :
    c.zFiber (d.ru2.quotientMap i)≃{a:Inverting d.toTypeRuSetup.Q (i:G)//IsConj c.z ((a.val:G)*i)} := by
  have hdiff (x:d.toTypeRuSetup.H) (hx:d.ru2.quotientMap x=d.ru2.quotientMap i) :
      (x:G)*(i:G)⁻¹∈d.toTypeRuSetup.Q := by
    have hh:x*i⁻¹∈d.ru2.quotientMap.ker:=by
      simp only [MonoidHom.mem_ker,map_mul,map_inv,hx,mul_inv_cancel]
    rw [d.ru2.quotient_kernel] at hh
    exact hh
  have hcoord (a:d.toTypeRuSetup.Q) :
      d.ru2.quotientMap ⟨(a:G)*i,d.toTypeRuSetup.H.mul_mem
        (d.ru2.six.section_le a.property) i.property⟩=d.ru2.quotientMap i := by
    let aH:d.toTypeRuSetup.H:=⟨a,d.ru2.six.section_le a.property⟩
    have hh:d.ru2.quotientMap aH=1:=by
      change aH∈d.ru2.quotientMap.ker
      rw [d.ru2.quotient_kernel]
      exact a.property
    change d.ru2.quotientMap (aH*i)=_
    rw [map_mul,hh,one_mul]
  refine {
    toFun:=fun x=>⟨⟨⟨(x.val:G)*(i:G)⁻¹,hdiff x.val x.property.2⟩,?_⟩,?_⟩
    invFun:=fun a=>⟨⟨(a.val:G)*i,d.toTypeRuSetup.H.mul_mem
      (d.ru2.six.section_le a.val.val.property) i.property⟩,a.property,hcoord a.val.val⟩
    left_inv:=fun x=>by apply Subtype.ext;apply Subtype.ext;simp
    right_inv:=fun x=>by apply Subtype.ext;apply Subtype.ext;apply Subtype.ext;simp }
  · apply (Fusion.Outer.inverting_iff_square _ _ hi).mpr
    simp only [inv_mul_cancel_right]
    have hx2:orderOf (x.val:G)=2:=c.z_class_order _ x.property.1
    exact hx2 ▸ pow_orderOf_eq_one (x.val:G)
  · simpa only [inv_mul_cancel_right] using x.property.1

public noncomputable def zFiberConj (h:d.toTypeRuSetup.H) (t:S5) :
    c.zFiber t≃c.zFiber (d.ru2.quotientMap h*t*(d.ru2.quotientMap h)⁻¹) :=
  Equiv.subtypeEquiv (MulAut.conj h).toEquiv (fun x=>by
    change (IsConj c.z (x:G) ∧ d.ru2.quotientMap x=t) ↔
      IsConj c.z ((h:G)*(x:G)*(h:G)⁻¹) ∧
        d.ru2.quotientMap (h*x*h⁻¹)=d.ru2.quotientMap h*t*(d.ru2.quotientMap h)⁻¹
    rw [c.isConj_conj_iff,map_mul,map_mul,map_inv]
    simp only [mul_left_inj,mul_right_inj])

public theorem card_zFiber_conjugate (t t':S5) (hc:IsConj t t') : Nat.card (c.zFiber t)=Nat.card (c.zFiber t') := by
  obtain ⟨g,hg⟩:=isConj_iff.mp hc
  obtain ⟨h,hh⟩:=d.ru2.quotient_surjective g
  have hcard:=Nat.card_congr (c.zFiberConj h t)
  rw [hh,hg] at hcard
  exact hcard

public theorem card_middle_of_one_fiber (i:d.toTypeRuSetup.H) (hiK:(i:G)∈d.toTypeRuSetup.K)
    (hiQ:(i:G)∉d.toTypeRuSetup.Q) (hi:(i:G)^2=1) (n:ℕ)
    (hc:Nat.card (c.zFiber (d.ru2.quotientMap i))=n) :
    Nat.card {x:G//IsConj c.z x ∧ x∈d.toTypeRuSetup.K ∧ x∉d.toTypeRuSetup.Q}=15*n := by
  classical
  let D:={t:S5//t∈alternatingGroup (Fin 5) ∧ t^2=1 ∧ t≠1}
  let X:={x:G//IsConj c.z x ∧ x∈d.toTypeRuSetup.K ∧ x∉d.toTypeRuSetup.Q}
  let F:X→D:=fun x=>⟨d.ru2.quotientMap ⟨x,d.toTypeRuSetup.K_le_H x.property.2.1⟩,
    quotient_even_involution (d:=d) _ x.property.2.1 x.property.2.2
      (by rw [←c.z_class_order x x.property.1];exact pow_orderOf_eq_one (x:G))⟩
  have hf (t:D):Nat.card {x:X//F x=t}=n := by
    let e:{x:X//F x=t}≃c.zFiber t := {
      toFun:=fun x=>⟨⟨x.val.val,d.toTypeRuSetup.K_le_H x.val.property.2.1⟩,
        x.val.property.1,congrArg Subtype.val x.property⟩
      invFun:=fun x=>⟨⟨x.val.val,x.property.1,
        (mem_K_iff_even_source (d:=d) x.val).mpr (by rw [x.property.2];exact t.property.1),by
          intro hxQ
          have hx1:d.ru2.quotientMap x.val=1:=by
            change x.val∈d.ru2.quotientMap.ker
            rw [d.ru2.quotient_kernel]
            exact hxQ
          exact t.property.2.2 (x.property.2.symm.trans hx1)⟩,Subtype.ext x.property.2⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
    rw [Nat.card_congr e,←c.card_zFiber_conjugate (d.ru2.quotientMap i) t
      (Equiv.Perm.even_involutions_five_isConj _ _
        (quotient_even_involution (d:=d) i hiK hiQ hi) t.property)]
    exact hc
  let := Fintype.ofFinite D
  have htot:Nat.card X=Nat.card D*n := by
    rw [←Nat.card_congr (Equiv.sigmaFiberEquiv F),Nat.card_sigma]
    simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
  have hD:Nat.card D=15:=Equiv.Perm.even_involutions_five_card
  rw [hD] at htot
  exact htot

public theorem card_Q_z_filter (i:d.toTypeRuSetup.H) (hiK:(i:G)∈d.toTypeRuSetup.K)
    (hiQ:(i:G)∉d.toTypeRuSetup.Q) (hi:(i:G)^2=1) (hbi:c.InvertsB (i:G)) :
    Nat.card {a:Inverting d.toTypeRuSetup.Q (i:G)//IsConj c.z ((a.val:G)*i)}=
      16*Nat.card {b:Inverting (Fusion.HB d.toTypeRuSetup c.sylowThree) (i:G)//IsConj c.z ((b.val:G)*i)} := by
  have ht:=quotient_even_involution (d:=d) i hiK hiQ hi
  have hf:=natural_free_involution d.ru2.naturalAction (d.ru2.quotientMap i) ht.2.1 ht.2.2 ht.1
  rw [card_Q_filter i hiK hiQ hi _ (fun a x=>c.isConj_conj_iff a x),
    c.card_HC_filter i hbi hi hf _ (fun a x=>c.isConj_conj_iff a x)]
  omega

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
