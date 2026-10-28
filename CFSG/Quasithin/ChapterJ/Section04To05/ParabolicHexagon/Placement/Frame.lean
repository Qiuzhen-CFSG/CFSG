module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.GraphActions
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SourceReflections
/-!
# Choosing the original quotient frame

The product of the two genuine source transvections sends zu to z and z to u,
while normalizing the same marked plane. In this frame, any actor sending z
to u induces a quotient automorphism fixing the inverter image: it sends u
to zu, and the original central involution lies in Q. The quotient commutation
condition is thus derived from the original label equations.
Source: Aschbacher--Smith J.4.7 proof, printed p.444.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
open ChapterF.SourceCompletion.BinaryRee
variable {D:Type*} [Group D] (q:Completion D)
  {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  (e:first≃*p.F₁ B5) (f:D→*G)
  (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
include q f hleft hz hfive

theorem exists_quotient_frame :
    ∃k:G,k∈normalizer (pairSpan c.z (sourceU e):Set G) ∧
      k*(c.z*sourceU e)*k⁻¹=c.z ∧ k*c.z*k⁻¹=sourceU e := by
  obtain ⟨r,t,hr,ht,hrz,hru,htu,htz,_,_⟩:=source_two_transvections q c B5 e f hleft hz hfive
  have hn: r*t∈normalizer (pairSpan c.z (sourceU e):Set G):=
    sourceI_normalizer_le_pairSpan_normalizer p B5 c e hz
      ((normalizer (sourceI e:Set G)).mul_mem hr ht)
  obtain ⟨hzo,huo,_,hcomm⟩:=source_pair_marks p B5 c e hz
  have htzu:t*(c.z*sourceU e)*t⁻¹=c.z := by
    calc
      _=(t*c.z*t⁻¹)*(t*sourceU e*t⁻¹):=by group
      _=(c.z*sourceU e)*sourceU e:=by rw [htz,htu,←hcomm.eq]
      _=c.z:=by rw [mul_assoc,←pow_two,(orderOf_eq_prime_iff.mp huo).1,mul_one]
  have hrzu:r*(c.z*sourceU e)*r⁻¹=sourceU e := by
    calc
      _=(r*c.z*r⁻¹)*(r*sourceU e*r⁻¹):=by group
      _=c.z*(c.z*sourceU e):=by rw [hrz,hru]
      _=sourceU e:=by rw [←mul_assoc,←pow_two,(orderOf_eq_prime_iff.mp hzo).1,one_mul]
  refine ⟨r*t,hn,?_,?_⟩
  · calc
      _=r*(t*(c.z*sourceU e)*t⁻¹)*r⁻¹:=by group
      _=c.z:=by rw [htzu,hrz]
  · calc
      _=r*(t*c.z*t⁻¹)*r⁻¹:=by group
      _=sourceU e:=by rw [htz,←hcomm.eq,hrzu]

omit q f hleft hfive in
include hz in
theorem quotient_actor_commutes (j k:G)
    (hjz:j*c.z*j⁻¹=sourceU e)
    (hkcolor:k*(c.z*sourceU e)*k⁻¹=c.z) (hkz:k*c.z*k⁻¹=sourceU e)
    (a:d.toTypeRuSetup.H) (ha:(a:G)=k*j*k⁻¹) :
    Commute (d.ru2.quotientMap (sourceInverter p B5 e)) (d.ru2.quotientMap a) := by
  have hku:k*sourceU e*k⁻¹=c.z*sourceU e := by
    have he:sourceU e*(k*sourceU e*k⁻¹)=c.z := by
      calc
        _=(k*c.z*k⁻¹)*(k*sourceU e*k⁻¹):=by rw [hkz]
        _=c.z:=by rw [show (k*c.z*k⁻¹)*(k*sourceU e*k⁻¹)=k*(c.z*sourceU e)*k⁻¹ by group,hkcolor]
    obtain ⟨_,huo,_,hcomm⟩:=source_pair_marks p B5 c e hz
    apply mul_left_cancel (a:=sourceU e)
    rw [he,←mul_assoc,hcomm.symm.eq,mul_assoc,←pow_two,(orderOf_eq_prime_iff.mp huo).1,mul_one]
  have hau:(a:G)*sourceU e*(a:G)⁻¹=c.z*sourceU e := by
    calc
      _=(k*j*k⁻¹)*(k*c.z*k⁻¹)*(k*j*k⁻¹)⁻¹:=by rw [ha,hkz]
      _=k*(j*c.z*j⁻¹)*k⁻¹:=by group
      _=c.z*sourceU e:=by rw [hjz,hku]
  let zH:d.toTypeRuSetup.H:=⟨c.z,p.F₁_le_H B5 (hz ▸ (e modelZ).property)⟩
  have hzQ:d.ru2.quotientMap zH=1 := by
    apply MonoidHom.mem_ker.mp
    rw [d.ru2.quotient_kernel]
    exact d.ru2.six.kernel_le (d.ru2.natural.kernel_le c.z_mem_Z)
  have he:a*sourceInverter p B5 e*a⁻¹=zH*sourceInverter p B5 e:=Subtype.ext hau
  have hq:=congrArg d.ru2.quotientMap he
  simp only [map_mul,map_inv,hzQ,one_mul] at hq
  exact (mul_inv_eq_iff_eq_mul.mp hq).symm
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
