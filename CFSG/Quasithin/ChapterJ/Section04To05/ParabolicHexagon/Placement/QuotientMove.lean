module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.Placement.QuotientTransport
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.GraphActions
/-!
# Moving the original color pair through its canonical quotient labels

Translate the zu-colored family to the original z-colored family by an
actual plane normalizer. Equivariance of the literal H/Q labels identifies
conjugation by kjk⁻¹ with the S5 action on the two inverted pentagons.
Consequently a moving quotient actor fixes no original zu-colored member.
The quotient actor is the image of the specified original H element.
Source: Aschbacher--Smith J.4.7 proof, printed p.444.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
  (c:Choices d) (e:first≃*p.F₁ B5) (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
include s hi hz hfive

theorem color_member_moved_of_quotient (k j:G)
    (hk:k∈normalizer (pairSpan c.z (sourceU e):Set G))
    (hkcolor:k*(c.z*sourceU e)*k⁻¹=c.z)
    (a:d.toTypeRuSetup.H) (ha:(a:G)=k*j*k⁻¹)
    (hmove:∀P:Sylow 5 S5,
      d.ru2.quotientMap (sourceInverter p B5 e)∈normalizer (P:Set S5) →
      d.ru2.quotientMap a • P≠P)
    (E:Subgroup G) (hE:E∈colorFamily p B5 c.z (sourceU e) (c.z*sourceU e)) :
    E.conjBy j≠E := by
  intro he
  have hEk:E.conjBy k∈colorFamily p B5 c.z (sourceU e) c.z := by
    simpa only [hkcolor] using color_conjugate_mem p B5 c.z (sourceU e) k hk hE
  rw [colorFamily_z p B5 c e hz] at hEk
  obtain ⟨P,hP⟩ := (sourceFamilyEquiv p s B5 hi c e hz hfive).surjective ⟨E.conjBy k,hEk⟩
  have hPE:parabolicFor p B5 P.val=E.conjBy k :=
    (sourceFamilyEquiv_apply p s B5 hi c e hz hfive P).symm.trans (congrArg Subtype.val hP)
  apply hmove P.val P.property
  apply parabolicFor_injective p s B5 hi
  rw [parabolicFor_conj p s B5 hi,hPE,ha,conjBy_conjBy]
  have hm:(k*j*k⁻¹)*k=k*j:=by group
  rw [hm,conjBy_mul,he]
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
