module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The linear steps in the HS application of B.4.8(2)

An irreducible natural quotient and a fixed line make a module indecomposable
as soon as that fixed line has no invariant complement. For an involution,
its moved subspace is the range of its single displacement operator. Thus
the genuine B.4.8(2) equality supplies the vector preimages required by the
literal group-theoretic fusion lemma.

Source: Aschbacher–Smith B.4.8(2), printed p.91 / PDF p.102, and I.2.2(5),
printed p.412 / PDF p.423.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Nonsplit

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

theorem indecomposable_of_no_fixed_complement
    (σ : Representation (ZMod 2) D V)
    (hline : Module.finrank (ZMod 2) σ.invariants = 1)
    (hnatural : ActionEquiv (reducedAction σ) (linearNatural BinaryField.two 3))
    (hn : ∀ W : Subrepresentation σ, ¬ IsCompl σ.invariants W.toSubmodule) :
    IsIndecomposable σ := by
  have hatom : IsAtom σ.invariants := Submodule.isAtom_iff_finrank_eq_one.mpr hline
  let : IsIrreducible (reducedAction σ) :=
    irreducible_of_equiv hnatural (linearNatural_irreducible BinaryField.two (by decide))
  let : Nontrivial (V ⧸ σ.invariants) :=
    Subrepresentation.irreducible_module_nontrivial (reducedAction σ)
  let : Nontrivial V := (Submodule.mkQ_surjective σ.invariants).nontrivial
  have htop (W : Subrepresentation σ) (hw : σ.invariants ⊔ W.toSubmodule = ⊤) : W = ⊤ := by
    rcases hatom.le_iff.mp (show σ.invariants ⊓ W.toSubmodule ≤ σ.invariants from inf_le_left)
      with h | h
    · exact (hn W ⟨disjoint_iff.mpr h, codisjoint_iff.mpr hw⟩).elim
    · apply Subrepresentation.toSubmodule_injective
      have hc : σ.invariants ≤ W.toSubmodule := by
        rw [← h]; exact inf_le_right
      change W.toSubmodule = ⊤
      simpa only [sup_of_le_right hc] using hw
  refine ⟨inferInstance, fun A B hab => ?_⟩
  rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient (fixed σ) A with ha | ha
  · have hB : B = ⊤ := htop B (top_unique (by
      rw [← hab.sup_eq_top]
      exact sup_le_sup ha le_rfl))
    left
    apply Subrepresentation.toSubmodule_injective
    have hd := hab.disjoint
    rw [hB] at hd
    exact disjoint_top.mp hd
  · have hA := htop A ha
    right
    apply Subrepresentation.toSubmodule_injective
    have hd := hab.disjoint
    rw [hA] at hd
    exact disjoint_top.mp hd.symm

/-- For an involutory actor the commutator subspace is the range of its
single displacement map, so the B.4.8 equality supplies an actual preimage. -/
theorem displacement_of_moved_eq_fixed
    (σ : Representation (ZMod 2) D V) (a : D) (ha : orderOf a = 2)
    (hm : moved σ (zpowers a) = fixedSpace σ (zpowers a))
    (v : V) (hv : σ a v = v) : ∃ w : V, σ a w - w = v := by
  classical
  have hle : moved σ (zpowers a) ≤ LinearMap.range (σ a - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, w, _, rfl⟩
    have hfin : IsOfFinOrder a := orderOf_pos_iff.mp (by omega)
    have hg' := hfin.mem_zpowers_iff_mem_range_orderOf.mp hg
    rw [ha] at hg'
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hg'
    have hlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · simp only [pow_zero, map_one, Module.End.one_apply, sub_self]
      exact Submodule.zero_mem _
    · exact ⟨w, by simp⟩
  exact hle (hm.symm ▸ ((mem_fixedSpace_zpowers_iff σ a v).mpr hv))
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Nonsplit
