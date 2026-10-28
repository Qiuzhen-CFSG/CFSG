module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SourceOppositeFive
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Correspondence

/-!
# The original quaternion reflection fixes the parabolic family

The quaternion CQ has order eight, whereas its intersection with the
marked torus I has order four. Choose r in CQ outside I. The original
wreath calculation gives its transvection u to zu while preserving I.
Crucially r belongs to Q. Since Q normalizes F1 and is normal in H, it
normalizes every H-conjugate of F1. Thus this actual r fixes both source
parabolics on z, without asserting that it normalizes a particular SL2
factor or preserves a chosen opposite five.

This is the parabolic-level reflection required for J.4.10 and J.4.7,
printed pp.443--445. The final theorem obtains fusion from the original
completion and keeps all ambient subgroup and quotient choices unchanged.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

/-- The source reflection can be selected in the actual quaternion two-core. -/
theorem exists_source_core_reflection
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    ∃ r:G,r∈CQ B5 ∧ r∈normalizer (sourceI e:Set G) ∧
      r*c.z*r⁻¹=c.z ∧ r*sourceU e*r⁻¹=c.z*sourceU e := by
  obtain ⟨R,hIR,hRH,hRN,hR32,hCQ,hd,hgen,heR,hzc,hcu,href⟩ :=
    exists_source_reflection c B5 e hz hfive
  obtain ⟨r,hrCQ,hrI⟩ : ∃r∈CQ B5,r∉sourceI e := by
    by_contra! hh
    have hle:CQ B5≤sourceI e⊓centralizer (B5Image B5:Set G) :=
      le_inf hh inf_le_right
    have hc:=card_le_of_le hle
    obtain ⟨q⟩ := c.fiveQuaternionData_source B5
    rw [CQ_card B5 q,sourceI_five_centralizer_card c B5 e hz hfive hfusion] at hc
    omega
  refine ⟨r,hrCQ,?_,?_,href r (hCQ hrCQ) hrI⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    apply sourceI_weakly_closed_in_complement e R hIR heR
    have hh:=map_mono (f:=(MulAut.conj r).toMonoidHom) hIR
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer (hCQ hrCQ)))
  · exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hRH (hCQ hrCQ)))
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer

namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)

include s hi in
/-- The original Q fixes every original H-conjugate parabolic. -/
theorem Q_normalizes_conjugate (E:Subgroup G) (hE:E∈conjugateFamily p B5) :
    d.toTypeRuSetup.Q≤normalizer (E:Set G) := by
  obtain ⟨h,rfl⟩:=hE
  have hQN:d.toTypeRuSetup.Q≤normalizer (p.F₁ B5:Set G) := by
    intro x hx
    exact ((first_relative_normalizer p s B5 hi).symm ▸
      (show x∈p.F₁ B5⊔d.toTypeRuSetup.Q from mem_sup_right hx)).2
  have hm: d.toTypeRuSetup.Q.map (MulAut.conj (h:G)).toMonoidHom=d.toTypeRuSetup.Q :=
    mem_normalizer_iff_map_conj_eq.mp (d.ru2.six.normalized h.property)
  have hh := (map_mono (f:=(MulAut.conj (h:G)).toMonoidHom) hQN).trans
    ((p.F₁ B5).le_normalizer_map (MulAut.conj (h:G)).toMonoidHom)
  rwa [hm] at hh
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily

namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer ParabolicFamily

/-- The genuine completion supplies the reflection fixing the full original family. -/
theorem source_parabolic_reflection {D:Type*} [Group D] (q:Completion D)
    {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
    (p:Plane d) (s:SourceChoice p) (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    {F:Subgroup G} (e:first≃*F) (f:D→*G)
    (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
    (hfive:(zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    ∃r:G,r∈CQ B5 ∧ r∈normalizer (sourceI e:Set G) ∧
      r*c.z*r⁻¹=c.z ∧ r*sourceU e*r⁻¹=c.z*sourceU e ∧
      ∀E∈conjugateFamily p B5,E.conjBy r=E := by
  obtain ⟨r,hr,hI,hz',hu⟩:=exists_source_core_reflection c B5 e hz hfive
    (PathTransport.source_fusion q c e f hleft hz)
  refine ⟨r,hr,hI,hz',hu,?_⟩
  intro E hE
  exact mem_normalizer_iff_map_conj_eq.mp (Q_normalizes_conjugate p s B5 hi E hE hr.1)
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
