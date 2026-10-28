module
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.CompleteReducibility
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Dimensions supplied by finite simple generating families

For a finite family of maps from irreducible representations, each new image
is either already contained in the preceding sum or disjoint from it. Thus
the dimension of the generated module is the sum of dimensions of a subfamily.
A section of a completely reducible representation is an equivariant quotient,
by extending its quotient map across the inclusion of its numerator.

The consumer is the five-root Cartan module in Fong--Seitz I (6C), p.40.
Neither independence of the generators nor an exact ambient dimension is assumed.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped MonoidAlgebra
namespace Representation
variable {k H V W : Type*} [Field k] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A section of a completely reducible representation is its equivariant quotient. -/
theorem section_surjection_of_completelyReducible (ρ : Representation k H V)
    (U : Subrepresentation ρ) (N : Subrepresentation U.toRepresentation)
    (hρ : ρ.IsCompletelyReducible) :
    ∃ p : ρ.IntertwiningMap N.quotientRepresentation, Function.Surjective p := by
  let : IsSemisimpleModule k[H] ρ.asModule := hρ
  let j : U.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := U.toSubmodule.subtype
    isIntertwining' _ := rfl }
  let q : U.toRepresentation.IntertwiningMap N.quotientRepresentation := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' _ := rfl }
  let jm := IntertwiningMap.equivLinearMapAsModule _ _ j
  let qm := IntertwiningMap.equivLinearMapAsModule _ _ q
  obtain ⟨pm,hpm⟩ := IsSemisimpleModule.extension_property jm
    (show Function.Injective jm from Subtype.val_injective) qm
  let p := (IntertwiningMap.equivLinearMapAsModule ρ N.quotientRepresentation).symm pm
  refine ⟨p,?_⟩
  intro y
  obtain ⟨u,rfl⟩ := N.toSubmodule.mkQ_surjective y
  exact ⟨u.val,LinearMap.congr_fun hpm u⟩

private theorem simple_range {ρ : Representation k H V} {σ : Representation k H W}
    [ρ.IsIrreducible] (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) : IsAtom f.range := by
  have hi := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let q : ρ.IntertwiningMap f.range.toRepresentation := {
    toLinearMap := f.toLinearMap.rangeRestrict
    isIntertwining' g := by ext x; exact f.isIntertwining _ _ g x }
  have hq : Function.Bijective q :=
    ⟨fun _ _ hh => hi (congrArg Subtype.val hh), fun ⟨_,x,hx⟩ => ⟨x,Subtype.ext hx⟩⟩
  apply (Subrepresentation.irreducible_iff_isAtom f.range).mp
  rw [irreducible_iff_isSimpleModule_asModule]
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (IntertwiningMap.equivLinearMapAsModule _ _ q) hq).mp inferInstance

/-- A finite sum of simple images has the dimension of a subfamily of its sources.
No independence or inequivalence of the sources is assumed. -/
theorem finrank_simple_generators [FiniteDimensional k W]
    {ι : Type*} (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)]
    (ρ : ∀ i, Representation k H (V i)) (σ : Representation k H W)
    (hir : ∀ i, (ρ i).IsIrreducible)
    (f : ∀ i, (ρ i).IntertwiningMap σ) (s : Finset ι) :
    ∃ t ⊆ s, Module.finrank k (⨆ i ∈ s, (f i).range).toSubmodule =
      ∑ i ∈ t, Module.finrank k (V i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅,Finset.Subset.refl _,by simp; rfl⟩
  | @insert i s hi ih =>
    obtain ⟨t,ht,hd⟩ := ih
    let A : Subrepresentation σ := ⨆ j ∈ s, (f j).range
    let := hir i
    by_cases hle : (f i).range ≤ A
    · refine ⟨t,ht.trans (Finset.subset_insert _ _),?_⟩
      have he : (⨆ j ∈ insert i s, (f j).range) = A := by
        apply le_antisymm
        · refine iSup_le fun j => iSup_le fun hj => ?_
          rcases Finset.mem_insert.mp hj with he | hj
          · subst j; exact hle
          · exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
        · exact iSup_le fun j => iSup_le fun hj =>
            le_iSup_of_le j (le_iSup_of_le (Finset.mem_insert_of_mem hj) le_rfl)
      rw [he]; exact hd
    have hn : f i ≠ 0 := by
      intro hz
      apply hle
      rw [hz]
      intro v hv
      obtain ⟨x,rfl⟩ := hv
      exact A.toSubmodule.zero_mem
    have ha := simple_range (f i) hn
    have hdis : Disjoint (f i).range A := ha.not_le_iff_disjoint.mp hle
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (f i).range.toSubmodule A.toSubmodule
    have hb : (f i).range.toSubmodule ⊓ A.toSubmodule = ⊥ :=
      congrArg Subrepresentation.toSubmodule hdis.eq_bot
    rw [hb,finrank_bot,add_zero] at hdim
    have hfi := (IsIrreducible.injective_or_eq_zero (f i)).resolve_right hn
    have hfd : Module.finrank k (f i).range.toSubmodule = Module.finrank k (V i) :=
      (LinearEquiv.ofInjective (f i).toLinearMap hfi).finrank_eq.symm
    refine ⟨insert i t,Finset.insert_subset_insert i ht,?_⟩
    have hit : i ∉ t := fun hh => hi (ht hh)
    rw [Finset.sum_insert hit]
    let B : Subrepresentation σ := {
      toSubmodule := (f i).range.toSubmodule ⊔ A.toSubmodule
      apply_mem_toSubmodule g v hv := by
        obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add]
        exact Submodule.mem_sup.mpr ⟨_,(f i).range.apply_mem_toSubmodule g hx,
          _,A.apply_mem_toSubmodule g hy,rfl⟩ }
    have he : (⨆ j ∈ insert i s, (f j).range) = B := by
      apply le_antisymm
      · refine iSup_le fun j => iSup_le fun hj => ?_
        rcases Finset.mem_insert.mp hj with he | hj
        · subst j
          exact (show (f i).range.toSubmodule ≤ B.toSubmodule from le_sup_left)
        · exact (show (f j).range ≤ A from le_iSup_of_le j (le_iSup_of_le hj le_rfl)).trans
            (show A.toSubmodule ≤ B.toSubmodule from le_sup_right)
      · change (f i).range.toSubmodule ⊔ A.toSubmodule ≤ _
        apply sup_le
        · exact (show (f i).range ≤ ⨆ j ∈ insert i s, (f j).range from
            le_iSup_of_le i (le_iSup_of_le (Finset.mem_insert_self _ _) le_rfl))
        · exact (show A ≤ ⨆ j ∈ insert i s, (f j).range from
            iSup_le fun j => iSup_le fun hj =>
              le_iSup_of_le j (le_iSup_of_le (Finset.mem_insert_of_mem hj) le_rfl))
    rw [he]
    change Module.finrank k ↥((f i).range.toSubmodule ⊔ A.toSubmodule) = _
    rw [hdim,hfd]
    exact congrArg (Module.finrank k (V i) + ·) hd
end Representation
