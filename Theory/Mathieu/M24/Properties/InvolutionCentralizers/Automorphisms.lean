module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.Mathieu.M24.Properties.Simplicity
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Involutory automorphisms and marked centralizers of M₂₄

The existing innerness theorem and centerlessness lift an involutory
automorphism to an element of order two. Exhaustive element fusion then
identifies its full fixed subgroup with a marked centralizer. Centerlessness
uses the existing simplicity theorem and two explicitly noncommuting generators.
No shape or order of either centralizer is assumed.

Source: Aschbacher–Smith 16.1.5(7), printed p.1171.
-/

public section
namespace Sporadic.Mathieu.M24InvolutionCentralizers
open Subgroup

/-- The center of the actual Witt-design M₂₄ is trivial. -/
theorem center_eq_bot : center M24 = ⊥ := by
  let := m24_isSimpleGroup
  rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let a : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩
    let b : M24 := ⟨m24GeneratorB, m24GeneratorB_mem⟩
    have ha : a ∈ center M24 := h ▸ mem_top a
    have hab := mem_center_iff.mp ha b
    have hp := congrArg (fun g : M24 => g.val 1) hab
    have hn : (m24GeneratorB * m24GeneratorA) (1 : Fin 24) ≠
        (m24GeneratorA * m24GeneratorB) (1 : Fin 24) := by decide +kernel
    exact (hn hp).elim

/-- An involutory automorphism is conjugation by an element of order exactly two. -/
theorem exists_inner_involution (r : MulAut M24) (hr : orderOf r = 2) :
    ∃ x : M24, r = MulAut.conj x ∧ orderOf x = 2 := by
  obtain ⟨x, hx⟩ := M24OuterRestriction.conj_surjective r
  refine ⟨x, hx.symm, ?_⟩
  rw [← orderOf_injective MulAut.conj
    (MulAut.conj_injective_of_center_eq_bot center_eq_bot), hx, hr]

/-- Conjugacy identifies the full fixed subgroup with the representative centralizer. -/
theorem fixed_equiv_centralizer_of_isConj {x y : M24} (h : IsConj x y) :
    Nonempty ((MulAut.conj y).fixedSubgroup ≃* centralizer ({x} : Set M24)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he : MulAut.conj y = MulAut.congr (MulAut.conj g) (MulAut.conj x) := by
    rw [MulAut.congr_conj]
    exact congrArg MulAut.conj hg.symm
  rw [he]
  exact ⟨(MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj x)).symm.trans
    (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj x))⟩

/-- Exhaustive coverage of involutory automorphisms by the two full marked centralizers. -/
theorem fixedSubgroup_alternative (r : MulAut M24) (hr : orderOf r = 2) :
    (∃ g, r = MulAut.conj g) ∧
      (Nonempty (r.fixedSubgroup ≃* centralizer2A) ∨
        Nonempty (r.fixedSubgroup ≃* centralizer2B)) := by
  obtain ⟨x, rfl, hx⟩ := exists_inner_involution r hr
  refine ⟨⟨x, rfl⟩, ?_⟩
  rcases involution_classes x hx with h | h
  · exact Or.inl (fixed_equiv_centralizer_of_isConj h)
  · exact Or.inr (fixed_equiv_centralizer_of_isConj h)

end Sporadic.Mathieu.M24InvolutionCentralizers
