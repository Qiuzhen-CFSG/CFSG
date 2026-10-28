module

public import Theory.Representation.BinaryOffender.Homogeneous.QuotientOrbit
public import Theory.Representation.CubicClifford.Inertia.Isotypic
public import Theory.Representation.SimpleCopies

/-!
# Simple types and independent families

Distinct simple types lie in distinct isotypic components. Independence of
those components therefore proves independence of the whole family, even
when the ambient representation is reducible. Intersecting its sum with one
component recovers the corresponding summand.

These are the semisimple geometry steps of Aschbacher–Smith, Lemma A.1.42,
printed p.32. No irreducibility of the ambient orbit span is assumed.
-/

@[expose] public section
noncomputable section
open scoped MonoidAlgebra
namespace Representation.BinaryOffender.Homogeneous

variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) E W}

theorem sameModule_iff_repEquiv (A B : Subrepresentation σ) :
    SameModule A B ↔ Nonempty (A.toRepresentation ≃ₗ B.toRepresentation) := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨⟨e, fun g => LinearMap.ext (he g)⟩⟩
  · rintro ⟨e⟩
    exact ⟨e.toLinearEquiv, fun g v => LinearMap.congr_fun (e.isIntertwining' g) v⟩

theorem sameModule_iff_linearEquiv (A B : Subrepresentation σ) :
    SameModule A B ↔ Nonempty (A.asSubmodule ≃ₗ[(ZMod 2)[E]] B.asSubmodule) :=
  (sameModule_iff_repEquiv A B).trans
    (isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv A B)

theorem SameModule.refl (A : Subrepresentation σ) : SameModule A A :=
  ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem SameModule.symm {A B : Subrepresentation σ} (h : SameModule A B) : SameModule B A :=
  (sameModule_iff_repEquiv B A).mpr ⟨((sameModule_iff_repEquiv A B).mp h).some.symm⟩

theorem SameModule.trans {A B C : Subrepresentation σ}
    (h : SameModule A B) (h' : SameModule B C) : SameModule A C :=
  (sameModule_iff_repEquiv A C).mpr
    ⟨((sameModule_iff_repEquiv A B).mp h).some.trans
      ((sameModule_iff_repEquiv B C).mp h').some⟩

theorem SameModule.irreducible {A B : Subrepresentation σ}
    (h : SameModule A B) (hA : IsIrreducible A.toRepresentation) :
    IsIrreducible B.toRepresentation :=
  (RepEquiv.irreducible_euqiv ((sameModule_iff_repEquiv A B).mp h).some).mp hA

theorem simple_asSubmodule (A : Subrepresentation σ)
    (hA : IsIrreducible A.toRepresentation) : IsSimpleModule (ZMod 2)[E] A.asSubmodule := by
  apply isSimpleModule_iff_isAtom.mpr
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff A).mpr
    ((Subrepresentation.irreducible_iff_isAtom A).mp hA)

/-- Forgetting the action preserves arbitrary sums, not just finite sums. -/
theorem toSubmodule_iSup {ι : Sort*} (A : ι → Subrepresentation σ) :
    (⨆ i, A i).toSubmodule = ⨆ i, (A i).toSubmodule := by
  let B : Subrepresentation σ := ⟨⨆ i, (A i).toSubmodule, by
    intro g v hv
    exact Submodule.iSup_induction _ (motive := fun w => σ g w ∈ ⨆ i, (A i).toSubmodule)
      hv (fun i w hw => le_iSup (fun i => (A i).toSubmodule) i
        ((A i).apply_mem_toSubmodule g hw))
      (by simp) (fun _ _ h h' => by simpa only [map_add] using Submodule.add_mem _ h h')⟩
  apply le_antisymm
  · exact (iSup_le fun i => show A i ≤ B from le_iSup (fun i => (A i).toSubmodule) i)
  · exact iSup_le fun i => show A i ≤ ⨆ j, A j from le_iSup A i

section RingGeometry
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

private theorem component_ne {A B : Submodule R M} [IsSimpleModule R A]
    [IsSimpleModule R B] (hne : ¬ Nonempty (A ≃ₗ[R] B)) :
    isotypicComponent R M A ≠ isotypicComponent R M B := by
  intro h
  apply hne
  apply isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R M B) A
  rw [← h]
  exact A.le_isotypicComponent

/-- A simple type is disjoint from the sum of all prescribed different types. -/
theorem component_disjoint_sum (A : Submodule R M) [IsSimpleModule R A]
    {ι : Sort*} (B : ι → Submodule R M) (hB : ∀ i, IsSimpleModule R (B i))
    (hne : ∀ i, ¬ Nonempty (A ≃ₗ[R] B i)) :
    Disjoint (isotypicComponent R M A) (⨆ i, B i) := by
  apply (sSupIndep_isotypicComponents R M
    (show isotypicComponent R M A ∈ isotypicComponents R M from ⟨A, inferInstance, rfl⟩)).mono_right
  refine iSup_le fun i => ?_
  have := hB i
  exact (B i).le_isotypicComponent.trans (le_sSup
    ⟨⟨B i, inferInstance, rfl⟩, fun h => component_ne (hne i) h.symm⟩)

/-- Pairwise nonisomorphic simple summands form an independent entire family. -/
theorem simple_family_independent {ι : Sort*} (A : ι → Submodule R M)
    (hA : ∀ i, IsSimpleModule R (A i))
    (hne : ∀ i j, i ≠ j → ¬ Nonempty (A i ≃ₗ[R] A j)) : iSupIndep A := by
  intro i
  have := hA i
  apply (component_disjoint_sum (A i) (fun j : {j // j ≠ i} => A j.val)
    (fun j => hA j.val) (fun j => hne i j.val (Ne.symm j.property))).mono_left
    (A i).le_isotypicComponent |>.mono_right
  exact iSup_le fun j => iSup_le fun hj => le_iSup (fun j : {j // j ≠ i} => A j.val) ⟨j,hj⟩

/-- In a sum with no other copy of its type, a summand is its full component. -/
theorem component_inf_sum_eq {ι : Type*} (A : ι → Submodule R M)
    (hA : ∀ i, IsSimpleModule R (A i)) (i : ι)
    (hne : ∀ j, j ≠ i → ¬ Nonempty (A i ≃ₗ[R] A j)) :
    (⨆ j, A j) ⊓ isotypicComponent R M (A i) = A i := by
  classical
  have := hA i
  have hd := component_disjoint_sum (A i) (fun j : {j // j ≠ i} => A j.val)
    (fun j => hA j.val) (fun j => hne j.val j.property)
  have hs : (⨆ j, A j) = A i ⊔ ⨆ j : {j // j ≠ i}, A j.val := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      by_cases h : j = i
      · subst j; exact le_sup_left
      · exact (le_iSup (fun j : {j // j ≠ i} => A j.val) ⟨j,h⟩).trans le_sup_right
    · exact sup_le (le_iSup A i) (iSup_le fun j => le_iSup A j.val)
  rw [hs, sup_inf_assoc_of_le _ (A i).le_isotypicComponent, hd.symm.eq_bot, sup_bot_eq]
end RingGeometry

/-- Pairwise distinct simple types are independent as actual binary subspaces. -/
theorem independent_of_pairwise_not_sameModule {ι : Sort*} (A : ι → Subrepresentation σ)
    (hA : ∀ i, IsIrreducible (A i).toRepresentation)
    (hne : ∀ i j, i ≠ j → ¬ SameModule (A i) (A j)) :
    iSupIndep (fun i => (A i).toSubmodule) := by
  have hi := simple_family_independent (fun i => (A i).asSubmodule)
    (fun i => simple_asSubmodule (A i) (hA i))
    (fun i j hij h => hne i j hij ((sameModule_iff_linearEquiv _ _).mpr h))
  intro i
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro v hv
  apply show v = 0 from ?_
  have hsum : v ∈ (⨆ j, ⨆ (_ : j ≠ i), A j).toSubmodule := by
    rw [toSubmodule_iSup]
    simp_rw [toSubmodule_iSup]
    exact hv.2
  have hsum' : σ.asModuleEquiv.symm v ∈ ⨆ j, ⨆ (_ : j ≠ i), (A j).asSubmodule := by
    have hm : σ.asModuleEquiv.symm v ∈
        (⨆ j, ⨆ (_ : j ≠ i), A j).asSubmodule := hsum
    change σ.asModuleEquiv.symm v ∈
      Subrepresentation.subrepresentationSubmoduleOrderIso (⨆ j, ⨆ (_ : j ≠ i), A j) at hm
    simpa only [OrderIso.map_iSup, Subrepresentation.subrepresentationSubmoduleOrderIso_apply] using hm
  exact congrArg σ.asModuleEquiv
    (show σ.asModuleEquiv.symm v = 0 from
      (show σ.asModuleEquiv.symm v ∈ (⊥ : Submodule (ZMod 2)[E] σ.asModule) from
        (hi i).eq_bot ▸ ⟨hv.1, hsum'⟩))

/-- The homogeneous part in the span of pairwise different simple types is
exactly the chosen member. -/
theorem homogeneousPart_family {ι : Type*} (A : ι → Subrepresentation σ)
    (hA : ∀ i, IsIrreducible (A i).toRepresentation) (i : ι)
    (hne : ∀ j, j ≠ i → ¬ SameModule (A i) (A j)) :
    homogeneousPart (A i) (⨆ j, (A j).toSubmodule) = (A i).toSubmodule := by
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => ?_
    have hb : B ≤ ⨆ j, A j := by
      change B.toSubmodule ≤ (⨆ j, A j).toSubmodule
      rw [toSubmodule_iSup]
      exact hB.1
    have hb' : B.asSubmodule ≤ ⨆ j, (A j).asSubmodule := by
      change B.asSubmodule ≤ Subrepresentation.subrepresentationSubmoduleOrderIso (⨆ j, A j) at hb
      simpa only [OrderIso.map_iSup, Subrepresentation.subrepresentationSubmoduleOrderIso_apply] using hb
    have hc : B.asSubmodule ≤ isotypicComponent (ZMod 2)[E] σ.asModule (A i).asSubmodule :=
      le_sSup ((sameModule_iff_linearEquiv _ _).mp hB.2.symm)
    have he := component_inf_sum_eq (fun j => (A j).asSubmodule)
      (fun j => simple_asSubmodule _ (hA j)) i
      (fun j hj h => hne j hj ((sameModule_iff_linearEquiv _ _).mpr h))
    exact show B.asSubmodule ≤ (A i).asSubmodule from he ▸ le_inf hb' hc
  · exact le_iSup_of_le (A i) (le_iSup_of_le ⟨le_iSup (fun j => (A j).toSubmodule) i, SameModule.refl _⟩ le_rfl)

end Representation.BinaryOffender.Homogeneous
