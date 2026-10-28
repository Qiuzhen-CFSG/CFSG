module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.RankOneRows.ModelDisplacement
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.RankOneRows.LinearClosure
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# The unrestricted rank-one B.5.1 row reduction

The original moved section is all of V. Its marked involution therefore has
rank exactly one on that space. Doubled SL3 and natural-plus-dual rows have
even displacement, so are impossible. A repeated binary SL4 or SL5 row must
have multiplicity one; the full binary linear normal-closure calculation then
proves every G.6.4 conclusion. Only the genuine irreducible quotient-action
row still needs central-kernel reconstruction.

Source: Aschbacher–Smith G.6.4, printed p.346, using B.5.1(1), p.99.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

private noncomputable def repeatedOneEquiv
    {D X : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) D X) : ActionEquiv (repeated σ 1) σ where
  groupEquiv := MulEquiv.refl _
  linearEquiv :=
    { toFun := fun v => v 0
      invFun := fun x _ => x
      left_inv := fun v => funext fun _i => congrArg v (Subsingleton.elim _ _)
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  intertwines _ _ := rfl

/-- This is a source row deduction with the same original moved section and
quotient action; it has no normalized-cubic hypothesis. -/
theorem Hypotheses.quasisimple_rank_one_rows
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (hq : IsQuasisimple (generalizedFitting (normalClosure ({a} : Set G))))
    (d : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G)))) :
    Conclusion ρ a ∨
      (d.sectionData.space.toSubmodule = ⊤ ∧
        IsIrrPlus (ρ.comp (normalClosure ({a} : Set G)).subtype)
          (generalizedFitting (normalClosure ({a} : Set G))) d.sectionData.space.toSubmodule ∧
        Function.Injective d.sectionData.action ∧
        IsIrreducible (d.sectionData.action.comp
          (generalizedFitting (normalClosure ({a} : Set G))).subtype) ∧
        ProjectiveLine.IrreducibleActionCase d.sectionData.action
          (generalizedFitting (normalClosure ({a} : Set G))) ⊤) := by
  let := h.finite_group
  let := h.finite_module
  let K := normalClosure ({a} : Set G)
  let L := generalizedFitting K
  let σ := ρ.comp K.subtype
  let t : K := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  have hspace := h.rank_one_quasisimple_section_top ht hq d.sectionData
  have hcost : Module.finrank (ZMod 2)
      (LinearMap.range (d.sectionData.space.toRepresentation t - LinearMap.id)) = 1 := by
    have he := (fixedCodim_subrepresentation_eq_iff σ d.sectionData.space (zpowers t)).mpr
      (by rw [hspace]; simp)
    simp only [fixedCodim_zpowers_eq_displacement_rank] at he
    exact he.trans ht
  cases d.clause_one with
  | irreducible hip hf hir hs _ =>
    right
    refine ⟨hspace,hip,hf,hir,?_⟩
    rwa [h.normalClosure_section_generated ht d.sectionData] at hs
  | doubleThree F whole e _ _ =>
    let tL : L := ⟨t,by change t ∈ generalizedFitting K; rw [whole]; trivial⟩
    have he := (e.displacement_rank tL).symm.trans hcost
    have hd := repeated_displacement_rank (linearNatural F 3) 2 (e.groupEquiv tL)
    omega
  | naturalDual n _ whole he =>
    obtain ⟨e⟩ := he
    let tL : L := ⟨t,by change t ∈ generalizedFitting K; rw [whole]; trivial⟩
    have he := (e.displacement_rank tL).symm.trans hcost
    have hd := naturalPlusDual_displacement_rank n (e.groupEquiv tL)
    omega
  | repeatedNatural n r hn _ _ whole he =>
    obtain ⟨e⟩ := he
    let tL : L := ⟨t,by change t ∈ generalizedFitting K; rw [whole]; trivial⟩
    have he := (e.displacement_rank tL).symm.trans hcost
    have hd := repeated_displacement_rank (linearNatural BinaryField.two n) r (e.groupEquiv tL)
    have hr : r = 1 := Nat.eq_one_of_mul_eq_one_right (hd.symm.trans he)
    subst r
    let e₁ := repeatedOneEquiv (linearNatural BinaryField.two n)
    let E : V ≃ₗ[ZMod 2] d.sectionData.space.toSubmodule :=
      Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ hspace.symm)
    let g : K ≃* L := topEquiv.symm.trans (MulEquiv.subgroupCongr whole.symm)
    let f : ActionEquiv σ (linearNatural BinaryField.two n) :=
      { groupEquiv := g.trans e.groupEquiv
        linearEquiv := E.trans (e.linearEquiv.trans e₁.linearEquiv)
        intertwines := fun k v => by
          have hh := congrArg e₁.linearEquiv (e.intertwines (g k) (E v))
          exact hh }
    left
    exact h.conclusion_of_binary_linear_normalClosure
      (by rcases hn with rfl | rfl <;> decide)
      (by rcases hn with rfl | rfl <;> decide) f
end CFSG.Quasithin.ChapterG.Section06
