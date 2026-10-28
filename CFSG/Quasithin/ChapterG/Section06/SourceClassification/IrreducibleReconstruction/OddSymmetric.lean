module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleReconstruction.SectionKernel
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.AmbientPlacement
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.CentralModels

/-!
# The odd symmetric moved sections in G.6.4

Vanishing of the two natural cohomology groups removes the fixed kernel
of the actual moved section. Every automorphism of S5 or S7 is inner, while
the original rank-one displacement generation makes the normal closure's
ambient centralizer trivial. Consequently the recovered natural actor is all
of the original group. This proves the full G.6 conclusion for these rows.

Source: Aschbacher–Smith, G.6.4, pp.345–346, using B.5.1(2), p.99.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource IrreducibleReconstruction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.normalClosure_eq_top_of_symmetric
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    {n : ℕ} (hn : 5 ≤ n) (h6 : n ≠ 6)
    (e : normalClosure ({a} : Set G) ≃* Equiv.Perm (Fin n)) :
    normalClosure ({a} : Set G) = ⊤ := by
  apply h.normalClosure_eq_top_of_inner_automorphisms hr
  intro f
  obtain ⟨p, hp⟩ := Equiv.Perm.conj_surjective_of_degree hn h6 (MulAut.congr e f)
  refine ⟨e.symm p, ?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj, e.apply_symm_apply]
  exact hp

theorem Hypotheses.conclusion_of_symmetric_normalClosure
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≤ 8) (h6 : n ≠ 6)
    (e : ActionEquiv (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (BinaryPermutation.naturalRepresentation (Fin n))) : Conclusion ρ a := by
  have hK := h.normalClosure_eq_top_of_symmetric hr hn h6 e.groupEquiv
  have hm := lemma_G_6_2_1 ρ a h.generated
  rw [hK] at hm
  apply h.conclusion_of_factor_decomposition hr
  left
  refine ⟨hK, ?_, hm⟩
  rw [hm]
  refine Or.inr (Or.inl ⟨n, hn, hn8, ?_⟩)
  have E : ActionEquiv (ρ.comp (⊤ : Subgroup G).subtype)
      (BinaryPermutation.naturalRepresentation (Fin n)) := by
    rw [← hK]
    exact e
  exact hasModelOn_top_of_actionEquiv ρ ⊤ _ E

theorem Hypotheses.conclusion_of_symmetricOdd_section
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (s : MovedSection (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G))))
    (hs : s.space.toSubmodule = ⊤)
    (hi : IsIrrPlus (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G))) s.space.toSubmodule)
    {n : ℕ} (hn : n = 5 ∨ n = 7)
    (e : MarkedActionEquiv s.action ⊤
      (generalizedFitting (normalClosure ({a} : Set G)))
      (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n))) :
    Conclusion ρ a := by
  let := h.finite_group
  let := h.finite_module
  have emark : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (normalClosure ({a} : Set G)))
      (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)) := by
    rw [h.normalClosure_section_generated hr s]
    exact e
  have hc := ExtensionConsequences.symmetricOdd_isCompl s hi hn emark
  exact h.conclusion_of_symmetric_normalClosure hr
    (by rcases hn with rfl | rfl <;> decide)
    (by rcases hn with rfl | rfl <;> decide)
    (by rcases hn with rfl | rfl <;> decide)
    (liftTopModel s hs (central_eq_bot_of_isCompl s hc) (actionOfTop rfl e.action))

end CFSG.Quasithin.ChapterG.Section06
