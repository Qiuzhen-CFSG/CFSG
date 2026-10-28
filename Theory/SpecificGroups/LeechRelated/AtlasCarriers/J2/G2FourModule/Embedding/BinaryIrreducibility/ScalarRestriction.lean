module

public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Irreducibility after restricting scalars

A nonzero invariant subspace over a smaller field spans the whole module over
an irreducible larger field. Hence the action on that subspace is faithful when
the original action is. A proper minimal subspace has a scalar translate distinct
from itself; minimality and equal dimensions make the two translates disjoint.
Its dimension is therefore at most half the total smaller-field dimension.

Consequently a lower bound on faithful representation degrees can establish
irreducibility after scalar restriction. The consumer in `BinaryIrreducibility`
uses this for the Hall--Janko restriction in Aschbacher--Smith, K.4.5, p.460.
No separability, simplicity or semisimplicity hypothesis is needed.
-/

@[expose] public noncomputable section
namespace Representation
variable {k K G V : Type*} [Field k] [Field K] [Algebra k K] [Monoid G]
  [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
  (ρ : Representation K G V) (σ : Representation k G V)
  (hcompat : ∀ g v, σ g v = ρ g v)

private def scalarSpan (S : Subrepresentation σ) : Subrepresentation ρ where
  toSubmodule := Submodule.span K (S : Set V)
  apply_mem_toSubmodule g v hv := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      apply Submodule.subset_span
      rw [← hcompat]
      exact S.apply_mem_toSubmodule g hv
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [map_add] using (Submodule.span K (S : Set V)).add_mem ihx ihy
    | smul a x hx ih =>
      simpa only [map_smul] using (Submodule.span K (S : Set V)).smul_mem a ih

include hcompat

omit [Algebra k K] [IsScalarTower k K V] in
private theorem scalarSpan_eq_top [IsIrreducible ρ]
    (S : Subrepresentation σ) (hS : S ≠ ⊥) :
    Submodule.span K (S : Set V) = ⊤ := by
  have hn : scalarSpan ρ σ hcompat S ≠ ⊥ := by
    intro h
    apply hS
    apply Subrepresentation.toSubmodule_injective
    apply eq_bot_iff.mpr
    intro v hv
    have hm : v ∈ scalarSpan ρ σ hcompat S := Submodule.subset_span hv
    rw [h] at hm
    exact hm
  exact congrArg Subrepresentation.toSubmodule ((eq_bot_or_eq_top
    (scalarSpan ρ σ hcompat S)).resolve_left hn)

omit [Algebra k K] [IsScalarTower k K V] in
/-- A nonzero submodule over the smaller field still detects the group action. -/
theorem injective_subrepresentation_of_scalar_irreducible [IsIrreducible ρ]
    (hρ : Function.Injective ρ) (S : Subrepresentation σ) (hS : S ≠ ⊥) :
    Function.Injective S.toRepresentation := by
  intro g h hgh
  apply hρ
  apply LinearMap.ext_on (scalarSpan_eq_top ρ σ hcompat S hS)
  intro v hv
  have he := congrArg Subtype.val (LinearMap.congr_fun hgh ⟨v, hv⟩)
  change σ g v = σ h v at he
  simpa only [hcompat] using he

/-- A proper minimal invariant subspace over the smaller field has a disjoint
scalar translate, so it has at most half the total dimension. -/
theorem twice_finrank_le_of_scalar_irreducible [IsIrreducible ρ]
    [FiniteDimensional k V] (S : Subrepresentation σ) (hS : IsAtom S)
    (hproper : S ≠ ⊤) :
    2 * Module.finrank k S.toSubmodule ≤ Module.finrank k V := by
  classical
  have hex : ∃ a : K, ∃ v : V, v ∈ S ∧ a • v ∉ S := by
    by_contra! h
    let T : Subrepresentation ρ := {
      toSubmodule := {
        __ := S.toSubmodule.toAddSubmonoid
        smul_mem' := h }
      apply_mem_toSubmodule := by
        intro g v hv
        rw [← hcompat]
        exact S.apply_mem_toSubmodule g hv }
    have hT : T ≠ ⊥ := by
      intro he
      apply hS.ne_bot
      ext v
      change v ∈ T ↔ v ∈ (⊥ : Subrepresentation σ)
      rw [he]
      rfl
    have ht := (eq_bot_or_eq_top T).resolve_left hT
    apply hproper
    ext v
    change v ∈ T ↔ v ∈ (⊤ : Subrepresentation σ)
    rw [ht]
    rfl
  obtain ⟨a, v, hv, hav⟩ := hex
  have ha : a ≠ 0 := by
    rintro rfl
    apply hav
    change 0 • v ∈ S.toSubmodule
    simpa only [zero_smul] using S.toSubmodule.zero_mem
  let e : V ≃ₗ[k] V := (LinearEquiv.smulOfNeZero K V a ha).restrictScalars k
  let T : Subrepresentation σ := {
    toSubmodule := S.toSubmodule.map e.toLinearMap
    apply_mem_toSubmodule := by
      intro g x hx
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨σ g y, S.apply_mem_toSubmodule g hy, ?_⟩
      change a • σ g y = σ g (a • y)
      simp only [hcompat, map_smul] }
  have hdim : Module.finrank k T.toSubmodule = Module.finrank k S.toSubmodule :=
    e.finrank_map_eq S.toSubmodule
  have hnotle : ¬ S ≤ T := by
    intro hle
    have heq : S.toSubmodule = T.toSubmodule :=
      Submodule.eq_of_le_of_finrank_eq hle hdim.symm
    apply hav
    change a • v ∈ S.toSubmodule
    rw [heq]
    exact ⟨v, hv, rfl⟩
  have hinf : S.toSubmodule ⊓ T.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule ((hS.not_le_iff_disjoint.mp hnotle).eq_bot)
  have hr := Submodule.finrank_sup_add_finrank_inf_eq S.toSubmodule T.toSubmodule
  rw [hinf, finrank_bot, add_zero, hdim] at hr
  have hb := (S.toSubmodule ⊔ T.toSubmodule).finrank_le
  omega

/-- An irreducible scalar extension remains irreducible if no faithful
representation of at most half the smaller-field dimension exists. -/
theorem irreducible_of_scalar_irreducible_of_no_small_faithful [IsIrreducible ρ]
    [FiniteDimensional k V] (hρ : Function.Injective ρ)
    (hexclude : ∀ (S : Subrepresentation σ),
      2 * Module.finrank k S.toSubmodule ≤ Module.finrank k V →
      ¬ Function.Injective S.toRepresentation) : IsIrreducible σ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨S, hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional σ
  have hatom := (Subrepresentation.irreducible_iff_isAtom S).mp hS
  have htop : S = ⊤ := by
    by_contra hn
    exact hexclude S (twice_finrank_le_of_scalar_irreducible ρ σ hcompat S hatom hn)
      (injective_subrepresentation_of_scalar_irreducible ρ σ hcompat hρ S hatom.ne_bot)
  rw [htop] at hatom
  exact isSimpleOrder_iff_isAtom_top.mpr hatom
end Representation
