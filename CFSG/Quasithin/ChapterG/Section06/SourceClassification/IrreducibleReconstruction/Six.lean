module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleReconstruction.EvenSections
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleReconstruction.AmbientSection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo

/-!
# The full binary symplectic row of G.6.4

The same polar isomorphism identifies both Sp4(2) and its marked derived
subgroup with S6 and A6. The perfect central-cover theorem reconstructs the
original natural or augmentation-core module. Ambient action on the faithful
natural quotient proves that the original normal closure is all of G.
The previously established central-Sylow conclusion completes this row.

Source: Aschbacher–Smith, G.6.4, pp.345–346, and B.4.2(3), p.86.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource IrreducibleReconstruction
open ExtensionConsequences.SymplecticTwo
universe u v

namespace IrreducibleReconstruction
open Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {H L : Subgroup D}

noncomputable def markedSymplecticSix
    (e : MarkedActionEquiv ρ H L (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) :
    MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin 6))
      (alternatingGroup (Fin 6)) where
  action :=
    { groupEquiv := e.action.groupEquiv.trans naturalActionEquiv.groupEquiv
      linearEquiv := e.action.linearEquiv.trans naturalActionEquiv.linearEquiv
      intertwines g v := (congrArg naturalActionEquiv.linearEquiv
        (e.action.intertwines g v)).trans (naturalActionEquiv.intertwines _ _) }
  contained := e.contained
  subgroupEquiv := e.subgroupEquiv.trans alternatingDerivedEquiv.symm
  compatible l := by
    change symmetricSymplecticEquiv.symm (e.action.groupEquiv _) =
      (alternatingDerivedEquiv.symm (e.subgroupEquiv l) : Equiv.Perm (Fin 6))
    apply symmetricSymplecticEquiv.injective
    rw [symmetricSymplecticEquiv.apply_symm_apply, e.compatible]
    exact (congrArg Subtype.val (alternatingDerivedEquiv.apply_symm_apply _)).symm
end IrreducibleReconstruction

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.conclusion_of_symplecticTwo_section
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (s : MovedSection (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G))))
    (hs : s.space.toSubmodule = ⊤)
    (e : MarkedActionEquiv s.action ⊤
      (generalizedFitting (normalClosure ({a} : Set G)))
      (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) : Conclusion ρ a := by
  let := h.finite_module
  have hK := h.normalClosure_eq_top_of_symplectic_section hr s hs (actionOfTop rfl e.action)
  have hm := lemma_G_6_2_1 ρ a h.generated
  rw [hK] at hm
  apply h.conclusion_of_factor_decomposition hr
  left
  refine ⟨hK, ?_, hm⟩
  rw [hm]
  rcases six_section_models s hs (markedSymplecticSix e) with he | he
  · obtain ⟨E⟩ := he
    refine Or.inr (Or.inl ⟨6, by decide, by decide, ?_⟩)
    have E' : ActionEquiv (ρ.comp (⊤ : Subgroup G).subtype)
        (BinaryPermutation.naturalRepresentation (Fin 6)) := by rw [← hK]; exact E
    exact hasModelOn_top_of_actionEquiv ρ ⊤ _ E'
  · obtain ⟨E⟩ := he
    refine Or.inr (Or.inr ⟨6, Or.inl rfl, ?_⟩)
    have E' : ActionEquiv (ρ.comp (⊤ : Subgroup G).subtype)
        (BinaryPermutation.coreRepresentation (Fin 6)) := by rw [← hK]; exact E
    exact hasModelOn_top_of_actionEquiv ρ ⊤ _ E'

end CFSG.Quasithin.ChapterG.Section06
