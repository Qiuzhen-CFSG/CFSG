module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Counting.CentralProduct

/-!
# The two natural four-fold lifting counts

The natural sections Q/HC and HC/HB both have four fixed coordinates for
an involution in K outside Q. In the second section only the chosen inverter
is used: it normalizes the original quaternion factor HB and acts on HC/HB
through the specified U/Z coordinates. Conjugacy-invariant filters are retained.

Source: Aschbacher–Smith J.2.7(8), printed p.437.
-/

open scoped Pointwise
open Subgroup Representation Representation.BinaryConjugationSection
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d:LocalSetup G} (c:Choices d)

public theorem HB_normalized_by_inverter (i:G) (hi:i∈d.toTypeRuSetup.H) (hbi:c.InvertsB i) :
    i∈normalizer (Fusion.HB d.toTypeRuSetup c.sylowThree) := by
  apply inf_normalizer_le_normalizer_inf
  exact ⟨d.ru2.six.normalized hi,normalizer_le_normalizer_centralizer _ (c.mem_NB_of_inverts hbi)⟩

public theorem HC_coordinates_equivariant (p:d.toTypeRuSetup.HC→*Multiplicative FourSpace)
    (hp:∀a:Fusion.HB d.toTypeRuSetup c.sylowThree,∀b:d.toTypeRuSetup.U,
      p ⟨(a:G)*(b:G),d.toTypeRuSetup.HC.mul_mem (c.HB_le_HC_source a.property)
        (d.U_le_HC b.property)⟩=d.ru2.natural.coordinates b)
    (i:d.toTypeRuSetup.H) (hbi:c.InvertsB (i:G)) (x:d.toTypeRuSetup.HC) :
    (p (d.toTypeRuSetup.HC.normalizerMonoidHom
      ⟨i,Fusion.CoreOrbit.centralizer_normalized d.toTypeRuSetup i.property⟩ x)).toAdd=
      d.ru2.naturalAction.action (d.ru2.quotientMap i) (p x).toAdd := by
  have cp:=Fusion.centralProductData_of_quaternion d c.sylowThree (SourceCompletion.quaternion c.sylowThree)
  have hBU:Fusion.HB d.toTypeRuSetup c.sylowThree≤centralizer (d.toTypeRuSetup.U:Set G):=
    c.HB_le_HC_source.trans inf_le_right
  have hx : (x:G)∈(↑(Fusion.HB d.toTypeRuSetup c.sylowThree):Set G)*(↑d.toTypeRuSetup.U:Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ (hBU.trans (Subgroup.centralizer_le_normalizer _)),←cp.product_eq]
    exact x.property
  obtain ⟨a,ha,b,hb,he⟩:=hx
  let a':Fusion.HB d.toTypeRuSetup c.sylowThree:=⟨(i:G)*a*(i:G)⁻¹,
    (mem_normalizer_iff.mp (c.HB_normalized_by_inverter i i.property hbi) a).mp ha⟩
  let b':d.toTypeRuSetup.U:=⟨(i:G)*b*(i:G)⁻¹,
    (mem_normalizer_iff.mp (d.ru2.natural.normalized i.property) b).mp hb⟩
  have hx' : x=⟨a*b,d.toTypeRuSetup.HC.mul_mem (c.HB_le_HC_source ha) (d.U_le_HC hb)⟩ := Subtype.ext he.symm
  rw [hx',hp ⟨a,ha⟩ ⟨b,hb⟩]
  have he' : d.toTypeRuSetup.HC.normalizerMonoidHom
      ⟨i,Fusion.CoreOrbit.centralizer_normalized d.toTypeRuSetup i.property⟩
      ⟨a*b,d.toTypeRuSetup.HC.mul_mem (c.HB_le_HC_source ha) (d.U_le_HC hb)⟩=
      ⟨(a':G)*(b':G),d.toTypeRuSetup.HC.mul_mem (c.HB_le_HC_source a'.property) (d.U_le_HC b'.property)⟩ := by
    apply Subtype.ext
    change (i:G)*(a*b)*(i:G)⁻¹=((i:G)*a*(i:G)⁻¹)*((i:G)*b*(i:G)⁻¹)
    group
  rw [he',hp a' b']
  exact d.ru2.natural.equivariant i ⟨b,hb⟩

public theorem card_HC_filter (i:d.toTypeRuSetup.H) (hbi:c.InvertsB (i:G)) (hi:(i:G)^2=1)
    (hfree:Fusion.Outer.FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i))
    (P:G→Prop) (hP:∀a:d.toTypeRuSetup.HC,∀x:G,P ((a:G)*x*(a:G)⁻¹)↔P x) :
    Nat.card {a:Inverting d.toTypeRuSetup.HC (i:G)//P ((a.val:G)*i)}=
      4*Nat.card {b:Inverting (Fusion.HB d.toTypeRuSetup c.sylowThree) (i:G)//P ((b.val:G)*i)} := by
  obtain ⟨p,hp,hpk,hpe⟩:=c.HC_coordinates_source
  have hk (a:d.toTypeRuSetup.HC):p a=1↔(a:G)∈Fusion.HB d.toTypeRuSetup c.sylowThree := by
    change a∈p.ker↔_
    rw [hpk]
    rfl
  rw [card_inverting_hom_filter (i:G) hi (Fusion.CoreOrbit.centralizer_normalized d.toTypeRuSetup i.property)
    c.HB_le_HC_source p hp hk _ (c.HC_coordinates_equivariant p hpe i hbi) hfree P hP,
    Fusion.Outer.card_natural_fixed_of_free d.toTypeRuSetup i hi hfree]

public theorem quotient_even_involution (i:d.toTypeRuSetup.H) (hiK:(i:G)∈d.toTypeRuSetup.K)
    (hiQ:(i:G)∉d.toTypeRuSetup.Q) (hi:(i:G)^2=1) :
    d.ru2.quotientMap i∈alternatingGroup (Fin 5) ∧
      (d.ru2.quotientMap i)^2=1 ∧ d.ru2.quotientMap i≠1 := by
  refine ⟨?_,?_,?_⟩
  · rw [←d.toTypeRuSetup.quotientMap_K]
    exact mem_map_of_mem _ hiK
  · rw [←map_pow,show i^2=1 from Subtype.ext hi,map_one]
  · intro h
    apply hiQ
    have hh:i∈d.ru2.quotientMap.ker:=h
    rw [d.ru2.quotient_kernel] at hh
    exact hh

public theorem card_Q_filter (i:d.toTypeRuSetup.H) (hiK:(i:G)∈d.toTypeRuSetup.K)
    (hiQ:(i:G)∉d.toTypeRuSetup.Q) (hi:(i:G)^2=1)
    (P:G→Prop) (hP:∀a:d.toTypeRuSetup.Q,∀x:G,P ((a:G)*x*(a:G)⁻¹)↔P x) :
    Nat.card {a:Inverting d.toTypeRuSetup.Q (i:G)//P ((a.val:G)*i)}=
      4*Nat.card {b:Inverting d.toTypeRuSetup.HC (i:G)//P ((b.val:G)*i)} := by
  have ht:=quotient_even_involution (d:=d) i hiK hiQ hi
  have hf:=natural_free_involution d.fusionNaturalHead.action (d.ru2.quotientMap i)
    ht.2.1 ht.2.2 ht.1
  have hc : Nat.card (Fixed (d.fusionNaturalHead.action.action (d.ru2.quotientMap i)))=4 := by
    have hh:=card_fixed_sq ((d.fusionNaturalHead.action.action.comp d.ru2.quotientMap) i)
      (representation_sq _ i hi) hf
    have hW:Nat.card FourSpace=16:=by rw [Nat.card_eq_fintype_card];exact SL2FourNatural.card_vector
    rw [hW] at hh
    change 16=Nat.card (Fixed (d.fusionNaturalHead.action.action (d.ru2.quotientMap i)))*
      Nat.card (Fixed (d.fusionNaturalHead.action.action (d.ru2.quotientMap i))) at hh
    nlinarith
  rw [card_inverting_section_filter d.fusionNaturalHead.sectionData i hi hf P hP]
  rw [MonoidHom.comp_apply,hc]

public theorem isConj_conj_iff (a x:G) : IsConj c.z (a*x*a⁻¹)↔IsConj c.z x := by
  have hh : IsConj x (a*x*a⁻¹):=isConj_iff.mpr ⟨a,rfl⟩
  exact ⟨fun h=>h.trans hh.symm,fun h=>h.trans hh⟩


end CFSG.Quasithin.ChapterJ.Centralizers.Choices
