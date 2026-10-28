module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Preparation
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Reducing the classifier to its actual component and product modules

The supplied PSL₃(2) isomorphism makes C quasisimple. If F*(D) is
quasisimple, containment and component maximality give C = F*(D).
In the outer A₆–C₃ case, the displayed product is normal with cyclic quotient.
Perfectness puts C inside that product, contradicting its order 1080, which
is not divisible by 168. No whole-space splitting from the outer case is used.

Together with the trivial and S₃ exclusions, this leaves the full B.5.1
conclusion on C, the two-factor module case, or the hyperplane module case.
Their module comparison and splitting remain separate obligations.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.6,
printed p.105, and the proof of 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier
open ChapterB ChapterB.QuasisimpleSource

variable {D : Type*} [Group D] [Finite D] {C : Subgroup D}

omit [Finite D] in
/-- The actual matrix isomorphism supplies quasisimplicity. -/
theorem component_quasisimple (e : C ≃* Matrix.PSL3Two.PSL) : IsQuasisimple C := by
  let : IsQuasisimple Matrix.PSL3Two.SL :=
    { toIsPerfect := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  exact IsQuasisimple.of_mulEquiv (Matrix.PSL3Two.equiv.trans e.symm)

/-- A normal PSL₃(2) is the whole generalized Fitting subgroup when it is quasisimple. -/
theorem component_eq_fitting [C.Normal] (e : C ≃* Matrix.PSL3Two.PSL)
    (hf : IsQuasisimple (generalizedFitting D)) : C = generalizedFitting D := by
  have hc : IsComponent D C := ⟨(inferInstance : C.Normal).isSubnormal, component_quasisimple e⟩
  exact hc.eq_of_le ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hf⟩
    (component_le_generalizedFitting D C hc)

omit [Finite D] in
private theorem normalizes_of_automorphism (S : Subgroup D) (t : D)
    (α : MulAut S) (hα : ∀ a : S, (α a : D) = t * a * t⁻¹) :
    t ∈ normalizer (S : Set D) := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    rw [← hα ⟨x, hx⟩]
    exact (α ⟨x, hx⟩).property
  · intro hx
    let y : S := ⟨t * x * t⁻¹, hx⟩
    have he := hα (α.symm y)
    rw [α.apply_symm_apply] at he
    have hx' : x = (α.symm y : D) := (MulAut.conj t).injective he
    rw [hx']
    exact (α.symm y).property

omit [Finite D] in
/-- The outer group shape cannot contain a perfect subgroup of order 168. -/
theorem no_outerSixThree (e : C ≃* Matrix.PSL3Two.PSL)
    (c : OuterSixThreeShape D) : False := by
  let : IsQuasisimple C := component_quasisimple e
  let P := c.first ⊔ c.second
  let : P.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← c.generates]
    refine sup_le P.le_normalizer (zpowers_le.mpr ?_)
    obtain ⟨a, ha, _⟩ := c.firstOuter
    obtain ⟨b, hb, _⟩ := c.secondOuter
    exact normalizer_inf_normalizer_le_normalizer_sup _ _
      ⟨normalizes_of_automorphism _ _ a ha, normalizes_of_automorphism _ _ b hb⟩
  let : IsCyclic (D ⧸ P) := by
    let q := QuotientGroup.mk' P
    apply isCyclic_iff_exists_zpowers_eq_top.mpr
    refine ⟨q c.element, ?_⟩
    have h := congrArg (Subgroup.map q) c.generates
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      MonoidHom.map_zpowers, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    exact h
  have hCP : C ≤ P := le_of_isPerfect_of_solvable_quotient C P
  have hd := card_dvd_of_le hCP
  have hc : Nat.card C = 168 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hp : Nat.card P = 1080 := by
    rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod,
      Nat.card_congr c.firstEquiv.toEquiv, Nat.card_congr c.secondEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)]
  rw [hc, hp] at hd
  norm_num at hd

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

/-- Preserve all module clauses while eliminating the incompatible group cases. -/
theorem source_cases [C.Normal] (e : C ≃* Matrix.PSL3Two.PSL)
    (h : SourceInduction.NontrivialAdequateAlternative ρ) :
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C) ∨
      Nonempty (SourceInduction.SourceTwoFactorCase ρ) ∨
      Nonempty (SourceInduction.HyperplaneCase ρ) := by
  cases h with
  | quasisimple hf c =>
    left
    rw [component_eq_fitting e hf]
    exact ⟨c⟩
  | symmetricThree c => exact (no_symmetricThree e c).elim
  | twoFactors c => exact Or.inr (Or.inl ⟨c⟩)
  | outerSixThree c => exact (no_outerSixThree e c).elim
  | hyperplane c => exact Or.inr (Or.inr ⟨c⟩)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier
