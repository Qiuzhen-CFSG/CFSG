module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleReconstruction.OddSymmetric
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.Representation.BinaryPermutation.CoreQuotientModels
public import Theory.Representation.BinaryPermutation.TransvectionCoreMap
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections

/-!
# Original even symmetric modules in G.6.4

For S6, the literal central projection of the moved section is a perfect
central cover, so the proved six-letter cover theorem gives natural or core
coordinates. For S8, the original rank-one involution is a transposition;
its conjugate centers give an augmentation-core map onto the original moved
space. The kernel classification again gives natural or core coordinates.
Every marking remains the one supplied by the actual B.4 quotient row.

Source: Aschbacher–Smith, G.6.4, pp.345–346, and B.3.1–3, pp.83–84.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource IrreducibleReconstruction
universe u v

namespace IrreducibleReconstruction
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {L : Subgroup D}

theorem marked_top_map {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} {M : Subgroup E}
    (e : MarkedActionEquiv ρ ⊤ L σ M) :
    L.map (actionOfTop rfl e.action).groupEquiv.toMonoidHom = M := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (e.compatible ⟨g, hg⟩).symm ▸ (e.subgroupEquiv ⟨g, hg⟩).property
  · intro hx
    obtain ⟨g, hg⟩ := e.subgroupEquiv.surjective ⟨x, hx⟩
    exact ⟨g, g.property, (e.compatible g).trans (congrArg Subtype.val hg)⟩

theorem six_section_models [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) (hs : s.space.toSubmodule = ⊤)
    (e : MarkedActionEquiv s.action ⊤ L
      (BinaryPermutation.naturalRepresentation (Fin 6)) (alternatingGroup (Fin 6))) :
    IsSymmetricNatural ρ 6 ∨
      Nonempty (ActionEquiv ρ (BinaryPermutation.coreRepresentation (Fin 6))) := by
  let E := actionOfTop rfl e.action
  let p : V →ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    E.linearEquiv.toLinearMap.comp
      (s.central.toSubmodule.mkQ.comp (topSpaceEquiv s hs).toLinearMap)
  have hp (g : D) (v : V) : p (ρ g v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (E.groupEquiv g) (p v) :=
    E.intertwines g (s.central.toSubmodule.mkQ (topSpaceEquiv s hs v))
  have hsur : Function.Surjective p := E.linearEquiv.surjective.comp
    ((Submodule.mkQ_surjective _).comp (topSpaceEquiv s hs).surjective)
  have hker : p.ker ≤ fixedSpace ρ L := by
    intro v hv
    have hz : s.central.toSubmodule.mkQ (topSpaceEquiv s hs v) = 0 :=
      E.linearEquiv.injective (show E.linearEquiv _ = E.linearEquiv 0 from
        (show p v = 0 from hv).trans (map_zero _).symm)
    have hc := (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [s.central_eq] at hc
    intro g
    exact congrArg Subtype.val (hc g)
  have hgen : subspaceCommutator ρ ⊤ L = ⊤ := s.space_eq.symm.trans hs
  rcases BinaryPermutation.SixCover.naturalOrCore_symmetric ρ E.groupEquiv L
      (marked_top_map e) p hp hsur hker hgen with ⟨F, hF⟩ | ⟨F, hF⟩
  · exact Or.inl ⟨⟨E.groupEquiv, F, hF⟩⟩
  · exact Or.inr ⟨⟨E.groupEquiv, F, hF⟩⟩

theorem eight_section_models [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ)
    (s : MovedSection ρ L) (hs : s.space.toSubmodule = ⊤)
    (e : MarkedActionEquiv s.action ⊤ L
      (BinaryPermutation.naturalRepresentation (Fin 8)) (alternatingGroup (Fin 8)))
    (t : D) (hne : t ≠ 1) (ht : t ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 1) :
    IsSymmetricNatural ρ 8 ∨
      Nonempty (ActionEquiv ρ (BinaryPermutation.coreRepresentation (Fin 8))) := by
  let E := actionOfTop rfl e.action
  have hcost : fixedCodim ρ (zpowers t) = 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank, hr]
  have hswap := Representation.SymmetricEightTransvections.isSwap_of_fixedCodim_eq_one
    ρ hf E.groupEquiv t hne ht hcost
  obtain ⟨f, heq, hgen⟩ := BinaryPermutation.TransvectionCoreMap.exists_core_map_of_transposition
    ρ hf E.groupEquiv L (marked_top_map e) t hswap hcost
  have hsgen : subspaceCommutator ρ ⊤ L = ⊤ := s.space_eq.symm.trans hs
  have hsur : Function.Surjective f := LinearMap.range_eq_top.mp (hgen.trans hsgen)
  have hfn : f ≠ 0 := by
    intro hz
    have hzero (v : V) : v = 0 := by obtain ⟨u, rfl⟩ := hsur v; simp [hz]
    apply hne
    apply hf
    ext v
    exact (hzero _).trans (hzero _).symm
  rcases BinaryPermutation.natural_or_core_of_core_surjection (by decide : 5 ≤ 8)
      ρ E.groupEquiv f heq hsur hfn with ⟨F, hF⟩ | ⟨F, hF⟩
  · exact Or.inl ⟨⟨E.groupEquiv, F, hF⟩⟩
  · exact Or.inr ⟨⟨E.groupEquiv, F, hF⟩⟩
end IrreducibleReconstruction

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.conclusion_of_coreEight_normalClosure
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (e : ActionEquiv (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (BinaryPermutation.coreRepresentation (Fin 8))) : Conclusion ρ a := by
  have hK := h.normalClosure_eq_top_of_symmetric hr (by decide) (by decide) e.groupEquiv
  have hm := lemma_G_6_2_1 ρ a h.generated
  rw [hK] at hm
  apply h.conclusion_of_factor_decomposition hr
  left
  refine ⟨hK, ?_, hm⟩
  rw [hm]
  refine Or.inr (Or.inr ⟨8, Or.inr rfl, ?_⟩)
  have E : ActionEquiv (ρ.comp (⊤ : Subgroup G).subtype)
      (BinaryPermutation.coreRepresentation (Fin 8)) := by
    rw [← hK]
    exact e
  exact hasModelOn_top_of_actionEquiv ρ ⊤ _ E

theorem Hypotheses.conclusion_of_symmetricEight_section
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (s : MovedSection (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (Theory.GroupTheory.generalizedFitting (normalClosure ({a} : Set G))))
    (hs : s.space.toSubmodule = ⊤)
    (e : MarkedActionEquiv s.action ⊤
      (Theory.GroupTheory.generalizedFitting (normalClosure ({a} : Set G)))
      (BinaryPermutation.naturalRepresentation (Fin 8)) (alternatingGroup (Fin 8))) :
    Conclusion ρ a := by
  let := h.finite_module
  let t : normalClosure ({a} : Set G) := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  rcases eight_section_models (ρ := ρ.comp (normalClosure ({a} : Set G)).subtype)
      (fun x y he => Subtype.ext (h.faithful he)) s hs e t
      (fun he => h.nonidentity (congrArg Subtype.val he))
      (Subtype.ext h.involution) hr with he | he
  · obtain ⟨E⟩ := he
    exact h.conclusion_of_symmetric_normalClosure hr (by decide) (by decide) (by decide) E
  · obtain ⟨E⟩ := he
    exact h.conclusion_of_coreEight_normalClosure hr E

end CFSG.Quasithin.ChapterG.Section06
