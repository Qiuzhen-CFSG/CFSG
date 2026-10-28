module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuNativeComplement
public import Theory.SpecificGroups.ReeTwo.NativeComplementRecognition
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.Verified

/-!
# The whole original first endpoint is the full binary Ree first parabolic

The actual native five and four actors give the complete Ree centralizer
presentation on F₁. The supplied core embedding preserves the original
central involution, so the whole map is faithful; the already proved source
order makes it an isomorphism. The verified matrix comparison then identifies
F₁ with the actual first parabolic of the full binary Ree model. Both the
literal original core and its central point are retained in the first map.

The final application starts from original TypeRu and constructs all local
choices internally. It assumes no core, complement, or endpoint equivalence.
The other endpoint and compatibility of the common Sylow are separate
remaining obligations of F.1.12.
Source: Aschbacher–Smith J.4.5, printed pp.441–442; Shinoda (1975), pp.81–83.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- The entire actual first endpoint is the Ree centralizer model, retaining
the original core and central point. -/
theorem SourceChoice.exists_F₁_core_preserving_equiv (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃e:ReeTwo.Centralizer≃*p.F₁ B5,
      zpowers ((e (ReeTwo.Centralizer.root 9):p.F₁ B5):G)=d.toTypeRuSetup.Z ∧
      ReeTwo.Centralizer.core.map e.toMonoidHom=(fiveHyperplane d B5).subgroupOf (p.F₁ B5) := by
  obtain ⟨e,c,b,hz,_hc,hco,hb,hbc,hjc,hjb⟩:=s.exists_F₁_native_complement B5 hi
  let j:ReeTwo.Core→*p.F₁ B5:=(inclusion (p.fiveHyperplane_le_F₁ B5)).comp e.symm.toMonoidHom
  have hj:Function.Injective j:=(inclusion_injective (p.fiveHyperplane_le_F₁ B5)).comp e.symm.injective
  have hjz:j (ReeTwo.Core.root 9)≠1:=by
    intro hh
    have heq:ReeTwo.Core.root 9=1:=hj (hh.trans j.map_one.symm)
    exact (by decide +kernel:ReeTwo.Core.root 9≠1) heq
  have hcc:c^5=1:=hco ▸ pow_orderOf_eq_one c
  have hactc:∀q,j (ReeTwo.Core.c q)=c*j q*c⁻¹:=fun q=>Subtype.ext (hjc q)
  have hactb:∀q,j (ReeTwo.Core.a q)=b*j q*b⁻¹:=fun q=>Subtype.ext (hjb q)
  obtain ⟨E,hE⟩:=ReeTwo.Centralizer.exists_equiv_of_native_actions
    (s.card_F₁ p B5 hi) j c b hcc hb hbc hactc hactb hjz
  refine ⟨E,?_,?_⟩
  · change zpowers ((E (SemidirectProduct.inl (ReeTwo.Core.root 9)):p.F₁ B5):G)=_
    rw [hE]
    exact hz
  · change SemidirectProduct.inl.range.map E.toMonoidHom=_
    rw [←MonoidHom.range_comp]
    have hcomp:E.toMonoidHom.comp SemidirectProduct.inl=j:=MonoidHom.ext hE
    rw [hcomp]
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
      ←MonoidHom.range_eq_map,inclusion_range]

/-- The verified matrix comparison identifies the actual first endpoint. -/
theorem SourceChoice.F₁_equiv_fullRee_first (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nonempty ((p.F₁ B5)≃*Tits.ExceptionalParabolics.FullRee.first) := by
  obtain ⟨e,_,_⟩:=s.exists_F₁_core_preserving_equiv B5 hi
  exact ⟨e.symm.trans ReeTwo.ParabolicMarkedComparison.Verified.firstEquiv⟩

/-- Original TypeRu supplies the entire first endpoint, without an endpoint
or core model assumption. -/
theorem first_endpoint_equiv_of_typeRu (h:IsTypeRu G) :
    ∃(d:LocalSetup G)(p:Plane d)(B5:Sylow 5 d.toTypeRuSetup.H),
      Nonempty ((p.F₁ B5)≃*Tits.ExceptionalParabolics.FullRee.first) := by
  obtain ⟨d,p,⟨s⟩⟩:=source_J4_choice h
  obtain ⟨B5,hi⟩:=s.inverts_sylow_five
  exact ⟨d,p,B5,s.F₁_equiv_fullRee_first B5 hi⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
