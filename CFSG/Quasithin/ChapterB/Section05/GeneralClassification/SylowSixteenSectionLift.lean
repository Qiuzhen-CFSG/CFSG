module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenReduction
public import Theory.Representation.BinaryPermutation.SevenPointFixedExclusion
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
import Theory.Representation.NormalComponentConstituents
import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Lifting the actual fitting-component moved section to the whole six-space

The fitting component of the normal offender subgroup is normal in the
whole actor. Faithful irreducibility makes its moved space the whole module
and its fixed space zero. Thus the literal B.5 quotient has no lost central
attachment, and its marked action can be used on the original module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
open QuasisimpleSource
variable {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

theorem fitting_section_full (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ))) :
    s.space.toSubmodule=⊤ ∧ s.central.toSubmodule=⊥ := by
  let J := offenderSubgroup ρ
  let F := generalizedFitting J
  let N := F.map J.subtype
  let : J.Normal := offenderSubgroup_normal ρ
  let : F.Characteristic := generalizedFitting_characteristic
  let : N.Normal := inferInstance
  let : IsQuasisimple F := hq
  let : IsSimpleGroup (F ⧸ center F) := hq.simple
  let : Nontrivial F := (QuotientGroup.mk'_surjective (center F)).nontrivial
  have hN : N≠⊥ := by
    intro he
    have hF : F=⊥ := by
      apply map_injective J.subtype_injective
      simpa only [Subgroup.map_bot] using he
    exact (nontrivial_iff_ne_bot F).mp inferInstance hF
  have hm := subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf hi N hN
  have hz := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi N hN
  have hs : s.space.toSubmodule=⊤ := by
    rw [s.space_eq]
    change subspaceCommutator (ρ.comp J.subtype) ⊤ F=⊤
    rw [subspaceCommutator_comp_map]
    exact hm
  refine ⟨hs,?_⟩
  rw [s.central_eq]
  apply bot_unique
  intro v hv
  apply Subtype.ext
  have hv' : v.val∈fixedSpace (ρ.comp J.subtype) F :=
    fun f => congrArg Subtype.val (hv f)
  rw [fixedSpace_comp_map,hz] at hv'
  exact hv'

/-- The quotient in the genuine B.5 source is the whole original module,
with the action of every element of the original offender subgroup. -/
theorem fitting_section_equiv (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ))) :
    ∃ E : V≃ₗ[ZMod 2](s.space.toSubmodule ⧸ s.central.toSubmodule),
      ∀ (g : offenderSubgroup ρ) v, E (ρ g v)=s.central.quotientRepresentation g (E v) := by
  obtain ⟨hs,hz⟩ := fitting_section_full ρ hf hi hq s
  let b : s.space.toSubmodule≃ₗ[ZMod 2]V :=
    LinearEquiv.ofBijective s.space.toSubmodule.subtype
      ⟨Subtype.val_injective,fun v => ⟨⟨v,hs.ge (Submodule.mem_top)⟩,rfl⟩⟩
  let q := s.central.toSubmodule.mkQ
  have hqbij : Function.Bijective q := ⟨LinearMap.ker_eq_bot.mp (by
    rw [Submodule.ker_mkQ,hz]),Submodule.mkQ_surjective _⟩
  let E := LinearEquiv.ofBijective (q.comp b.symm.toLinearMap) (hqbij.comp b.symm.bijective)
  have hb (v : V) : (b.symm v).val=v := b.apply_symm_apply v
  refine ⟨E,?_⟩
  intro g v
  change q (b.symm (ρ g v))=q (s.space.toRepresentation g (b.symm v))
  congr 1
  apply Subtype.ext
  change (b.symm (ρ g v)).val=ρ g (b.symm v).val
  rw [hb,hb]

/-- A literal fixed-line two-group excludes the natural seven-letter
marking on the genuine fitting-component moved-section quotient. -/
theorem not_seven_natural_section
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (A : Subgroup D) (hA : IsPGroup 2 A)
    (hfix : Module.finrank (ZMod 2) (fixedSpace ρ A)=1)
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ)))
    (e : ActionEquiv (s.central.quotientRepresentation.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      (alternatingNatural 7)) : False := by
  let J := offenderSubgroup ρ
  let F := generalizedFitting J
  let N := F.map J.subtype
  let : J.Normal := offenderSubgroup_normal ρ
  let : F.Characteristic := generalizedFitting_characteristic
  let : N.Normal := inferInstance
  obtain ⟨b,hb⟩ := fitting_section_equiv ρ hf hi hq s
  let en := F.equivMapOfInjective J.subtype J.subtype_injective
  let f := e.groupEquiv.toMonoidHom.comp en.symm.toMonoidHom
  let cn := BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
  let E := b.trans (e.linearEquiv.trans cn.symm)
  apply BinaryPermutation.SevenAmbientAction.no_marked_normal_core_of_fixed_line
    ρ A N hA hfix f (e.groupEquiv.surjective.comp en.symm.surjective) E
  intro n v
  have hne : ((en.symm n : F) : J).val=n.val := by
    exact congrArg Subtype.val (en.apply_symm_apply n)
  apply cn.injective
  change cn (cn.symm (e.linearEquiv (b (ρ n v))))=
    cn (BinaryPermutation.alternatingCoreRepresentation (Fin 7) (f n) (E v))
  rw [cn.apply_symm_apply]
  change e.linearEquiv (b (ρ n v))=
    cn (BinaryPermutation.coreRepresentation (Fin 7) (f n).val (E v))
  rw [BinaryPermutation.coreEquivNatural_equivariant]
  change e.linearEquiv (b (ρ n v))=
    alternatingNatural 7 (e.groupEquiv (en.symm n)) (cn (cn.symm (e.linearEquiv (b v))))
  rw [cn.apply_symm_apply,←hne,hb]
  exact e.intertwines (en.symm n) (b v)

/-- The symmetric-seven constructor of the actual B.5 source is excluded
with its own compatible A7 marking and the original fixed-line two-group. -/
theorem not_seven_symmetric_section
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (A : Subgroup D) (hA : IsPGroup 2 A)
    (hfix : Module.finrank (ZMod 2) (fixedSpace ρ A)=1)
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ)))
    (H : Subgroup (offenderSubgroup ρ))
    (e : MarkedActionEquiv s.central.quotientRepresentation H
      (generalizedFitting (offenderSubgroup ρ))
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) : False := by
  apply not_seven_natural_section ρ hf hi hq A hA hfix s
  refine ⟨e.subgroupEquiv,e.action.linearEquiv,?_⟩
  intro f v
  have hh := e.action.intertwines ⟨f,e.contained f.property⟩ v
  rw [e.compatible] at hh
  exact hh

end CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
