module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Counting.Middle
public import Theory.Representation.BinaryConjugationSection.CocycleConjugacy
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.QuaternionCosetInvolutions.Noncentral
import all CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.TwoClasses
import all CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Counting.Fibers

/-!
# The corrected H-transitivity of the middle z-class

Each free natural section permits conjugating an involution lift into its
coordinate kernel. Repeating this moves every z-class element of a Q-coset
into the original quaternion coset. That filtered coset has two elements,
and the marked Aut(A6) calculation supplies a quaternion element moving
the inverter, so both lie in one quaternion orbit. Surjectivity onto S5
then joins all fifteen even-involution fibers under the original H.

This proves the actual H-transitivity assertion along with the literal480
count. It preserves the distinction from the invalid stronger K-transitivity
assertion recorded by the existing source diagnostics.

Source: Aschbacher–Smith J.2.7(8), printed p.437 (PDF p.448).
-/

open Subgroup Representation Representation.BinaryConjugationSection
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (c:Choices d)

public theorem quaternion_moved_by_inverter_source (i:d.toTypeRuSetup.H)
    (hi:orderOf (i:G)=2) (hbi:c.InvertsB (i:G)) :
    ∃a:Fusion.HB d.toTypeRuSetup c.sylowThree,(i:G)*(a:G)≠(a:G)*i := by
  let A:=Fusion.HB d.toTypeRuSetup c.sylowThree
  obtain ⟨eA⟩:=SourceCompletion.quaternion c.sylowThree
  have hAp:IsPGroup 2 A:=IsPGroup.of_card (n:=3) (by
    rw [Nat.card_congr eA.toEquiv,Nat.card_eq_fintype_card];decide +kernel)
  have hAN:A≤c.NB:=inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨e,hM⟩:=c.normalizer_equiv_autA6_source
  let φ:=CubicSylow.markedMap c e
  have hker:Nat.Coprime 2 (Nat.card φ.ker):=by
    rw [CubicSylow.markedMap_ker,CubicSylow.normalizerKernel_card c (SourceCompletion.B_card c)]
    decide
  let j:A→*AlternatingSix.ShadowLocal.AutA6:=φ.comp (inclusion hAN)
  have hj:Function.Injective j:=
    (injective_comp_subtype_of_coprime_ker φ hker (A.subgroupOf c.NB) hAp.comap_subtype).comp
      (subgroupOfEquivOfLe hAN).symm.injective
  let Q:=j.range
  let eqv:A≃*Q:=MonoidHom.ofInjective hj
  let iN:c.NB:=⟨i,c.mem_NB_of_inverts hbi⟩
  let β:=φ iN
  have hβ:orderOf β=2:=c.inverter_marked_order e iN hbi ((orderOf_coe iN).symm.trans hi)
  have hQM:Q≤AlternatingSix.M10.extension:=by
    rintro _ ⟨a,rfl⟩
    rw [←hM]
    exact ⟨c.normalizerQuotientMap (inclusion hAN a),
      mem_map_of_mem c.normalizerQuotientMap a.property.2,rfl⟩
  have hβQ:β∉Q:=fun h=>c.inverter_marked_not_extension e hM iN hbi (hQM h)
  obtain ⟨q,hq⟩:=AlternatingSix.ShadowLocal.QuaternionCosetInvolutions.exists_quaternion_noncommuting
    Q ⟨eqv.symm.trans eA⟩ β hβ hβQ
  obtain ⟨a,rfl⟩:=eqv.surjective q
  refine ⟨a,fun ha=>hq ?_⟩
  change φ iN*φ (inclusion hAN a)=φ (inclusion hAN a)*φ iN
  rw [←map_mul,←map_mul]
  exact congrArg φ (Subtype.ext ha)

public theorem Q_inverting_conjugate_into_HB (i:d.toTypeRuSetup.H)
    (hiK:(i:G)∈d.toTypeRuSetup.K) (hiQ:(i:G)∉d.toTypeRuSetup.Q)
    (hi:(i:G)^2=1) (hbi:c.InvertsB (i:G)) (a:Inverting d.toTypeRuSetup.Q (i:G)) :
    ∃g:d.toTypeRuSetup.Q,∃b:Inverting (Fusion.HB d.toTypeRuSetup c.sylowThree) (i:G),
      (g:G)*((a.val:G)*i)*(g:G)⁻¹=(b.val:G)*i := by
  have ht:=quotient_even_involution (d:=d) i hiK hiQ hi
  have hf:=natural_free_involution d.fusionNaturalHead.action (d.ru2.quotientMap i) ht.2.1 ht.2.2 ht.1
  obtain ⟨g,b,hgb⟩:=inverting_conjugate_into_kernel (i:G) hi
    (d.fusionNaturalHead.sectionData.normalized i.property)
    d.fusionNaturalHead.sectionData.coordinates d.fusionNaturalHead.sectionData.onto
    d.fusionNaturalHead.sectionData.coordinates_eq_one_iff
    _ (d.fusionNaturalHead.sectionData.equivariant i) hf a
  obtain ⟨p,hp,hpk,hpe⟩:=c.HC_coordinates_source
  have hk (x:d.toTypeRuSetup.HC):p x=1↔(x:G)∈Fusion.HB d.toTypeRuSetup c.sylowThree:=by
    change x∈p.ker↔_
    rw [hpk]
    rfl
  have hf':=natural_free_involution d.ru2.naturalAction (d.ru2.quotientMap i) ht.2.1 ht.2.2 ht.1
  obtain ⟨g',b',hgb'⟩:=inverting_conjugate_into_kernel (i:G) hi
    (Fusion.CoreOrbit.centralizer_normalized d.toTypeRuSetup i.property) p hp hk
    _ (c.HC_coordinates_equivariant p hpe i hbi) hf' b
  refine ⟨⟨(g':G)*g,d.toTypeRuSetup.Q.mul_mem (d.toTypeRuSetup.HC_le_Q g'.property) g.property⟩,b',?_⟩
  calc
    ((g':G)*(g:G))*((a.val:G)*i)*((g':G)*(g:G))⁻¹=
      (g':G)*((g:G)*((a.val:G)*i)*(g:G)⁻¹)*(g':G)⁻¹ := by group
    _=(b'.val:G)*i := by rw [hgb,hgb']

public theorem inverter_fiber_transitive_source (i:d.toTypeRuSetup.H)
    (hiK:(i:G)∈d.toTypeRuSetup.K) (hiQ:(i:G)∉d.toTypeRuSetup.Q)
    (hi:orderOf (i:G)=2) (hbi:c.InvertsB (i:G)) (hzi:IsConj c.z (i:G))
    (x:c.zFiber (d.ru2.quotientMap i)) :
    ∃h∈d.toTypeRuSetup.Q,h*(i:G)*h⁻¹=(x.val:G) := by
  have hi2:(i:G)^2=1:=hi ▸ pow_orderOf_eq_one (i:G)
  let a:=c.zFiberEquivInverting i hi2 x
  have ha:(a.val.val:G)*i=(x.val:G):=by
    change ((x.val:G)*(i:G)⁻¹)*(i:G)=(x.val:G)
    group
  obtain ⟨g,b,hgb⟩:=c.Q_inverting_conjugate_into_HB i hiK hiQ hi2 hbi a.val
  have hzb:IsConj c.z ((b.val:G)*i):=by
    rw [←hgb,ha]
    exact (c.isConj_conj_iff g _).mpr x.property.1
  obtain ⟨r,hr⟩:=conjugacy_filter_of_card_two (Fusion.HB d.toTypeRuSetup c.sylowThree)
    (i:G) hi2 (c.HB_normalized_by_inverter i i.property hbi) (IsConj c.z) hzi
    (fun q y=>c.isConj_conj_iff q y)
    (c.quaternion_inverting_z_class_card i hiK hiQ hi hbi hzi)
    (c.quaternion_moved_by_inverter_source i hi hbi) b hzb
  refine ⟨(g:G)⁻¹*r,d.toTypeRuSetup.Q.mul_mem (d.toTypeRuSetup.Q.inv_mem g.property)
    r.property.1,?_⟩
  calc
    ((g:G)⁻¹*(r:G))*(i:G)*((g:G)⁻¹*(r:G))⁻¹=
      (g:G)⁻¹*((r:G)*(i:G)*(r:G)⁻¹)*(g:G) := by group
    _=(g:G)⁻¹*((g:G)*((a.val.val:G)*i)*(g:G)⁻¹)*(g:G) := by rw [hr,←hgb]
    _=(x.val:G) := by rw [ha];group

public theorem middle_z_class_conjugate_to_seed (i:d.toTypeRuSetup.H)
    (hiK:(i:G)∈d.toTypeRuSetup.K) (hiQ:(i:G)∉d.toTypeRuSetup.Q)
    (hi:orderOf (i:G)=2) (hbi:c.InvertsB (i:G)) (hzi:IsConj c.z (i:G))
    (x:G) (hxz:IsConj c.z x) (hxK:x∈d.toTypeRuSetup.K) (hxQ:x∉d.toTypeRuSetup.Q) :
    ∃h∈d.toTypeRuSetup.H,h*(i:G)*h⁻¹=x := by
  let xH:d.toTypeRuSetup.H:=⟨x,d.toTypeRuSetup.K_le_H hxK⟩
  have hi2:(i:G)^2=1:=hi ▸ pow_orderOf_eq_one (i:G)
  have hx2:x^2=1:=c.z_class_order x hxz ▸ pow_orderOf_eq_one x
  have hconj:=Equiv.Perm.even_involutions_five_isConj _ _
    (quotient_even_involution i hiK hiQ hi2) (quotient_even_involution xH hxK hxQ hx2)
  obtain ⟨k,hk⟩:=isConj_iff.mp hconj
  obtain ⟨h,hh⟩:=d.ru2.quotient_surjective k
  let y:d.toTypeRuSetup.H:=h⁻¹*xH*h
  have hyq:d.ru2.quotientMap y=d.ru2.quotientMap i:=by
    change d.ru2.quotientMap (h⁻¹*xH*h)=_
    rw [map_mul,map_mul,map_inv,hh,←hk]
    group
  have hyz:IsConj c.z (y:G):=by
    change IsConj c.z ((h:G)⁻¹*x*(h:G))
    simpa only [inv_inv] using (c.isConj_conj_iff (h:G)⁻¹ x).mpr hxz
  obtain ⟨a,ha,hai⟩:=c.inverter_fiber_transitive_source i hiK hiQ hi hbi hzi ⟨y,hyz,hyq⟩
  refine ⟨(h:G)*a,d.toTypeRuSetup.H.mul_mem h.property (d.ru2.six.section_le ha),?_⟩
  calc
    ((h:G)*a)*(i:G)*((h:G)*a)⁻¹=(h:G)*(a*(i:G)*a⁻¹)*(h:G)⁻¹ := by group
    _=x := by rw [hai];change (h:G)*((h:G)⁻¹*x*(h:G))*(h:G)⁻¹=x;group

public theorem middle_z_class_H_transitive_source :
    ∀x y:G,IsConj c.z x→x∈d.toTypeRuSetup.K→x∉d.toTypeRuSetup.Q→
      IsConj c.z y→y∈d.toTypeRuSetup.K→y∉d.toTypeRuSetup.Q→
      ∃h∈d.toTypeRuSetup.H,h*x*h⁻¹=y := by
  obtain ⟨i,hiK,hiQ,hi,hbi,hzi⟩:=c.exists_middle_inverter_source
  intro x y hxz hxK hxQ hyz hyK hyQ
  obtain ⟨a,ha,hax⟩:=c.middle_z_class_conjugate_to_seed i hiK hiQ hi hbi hzi x hxz hxK hxQ
  obtain ⟨b,hb,hby⟩:=c.middle_z_class_conjugate_to_seed i hiK hiQ hi hbi hzi y hyz hyK hyQ
  refine ⟨b*a⁻¹,d.toTypeRuSetup.H.mul_mem hb (d.toTypeRuSetup.H.inv_mem ha),?_⟩
  rw [←hax,←hby]
  group

public theorem middle_z_class_orbit_source :
    Fusion.TransitiveOn d.toTypeRuSetup.H
      {x:G|IsConj c.z x ∧ x∈d.toTypeRuSetup.K ∧ x∉d.toTypeRuSetup.Q} ∧
    Nat.card {x:G//IsConj c.z x ∧ x∈d.toTypeRuSetup.K ∧ x∉d.toTypeRuSetup.Q}=480 := by
  refine ⟨?_,c.middle_z_class_card_source⟩
  intro x y hx hy
  obtain ⟨h,hh,he⟩:=c.middle_z_class_H_transitive_source x y hx.1 hx.2.1 hx.2.2 hy.1 hy.2.1 hy.2.2
  exact ⟨⟨h,hh⟩,he⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
