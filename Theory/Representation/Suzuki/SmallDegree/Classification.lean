module

public import Theory.Representation.Suzuki.SmallDegree.Classification.SpecialSupport
public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct
public import Theory.Representation.PRegularSimpleCount
public import Theory.SpecificGroups.Suzuki.PRegularClasses

/-!
# Classification by the concrete Suzuki Frobenius tensors

A family of `q` pairwise inequivalent simple modules exhausts the irreducible
modules when the actual group has at most `q` odd-order conjugacy classes.
Here `q = 2^(2*m+1)`, the cardinality of the concrete support type. Adding a
hypothetical missing irreducible would contradict the modular simple-family
bound. Transport along a basis handles arbitrary carrier universes, and the
nonidentity central root excludes the empty support for faithful actions.

The root fixed-line and cyclicity proofs supply simplicity and distinctness;
the concrete torus partition supplies the odd-order class bound. Thus every
finite-dimensional irreducible over an algebraically closed extension of the
defining field has a unique support, with an actual representation equivalence.
Faithful representations have nonempty support. All results include `m = 1`,
and the tensor family includes both empty and full support. The conditional
counting APIs are retained alongside the unconditional assembly.

Sources: GLS3, 2.8.2--2.8.8; Guralnick--Malle, *Classification of 2F-modules,
II*, §3.1, equation (3.2), and Lemma 8.3. We use the `2*m+1` ordinary
Frobenius positions in the published concrete model.
-/

public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural
universe u

variable {m : ℕ} {K : Type u} [Field K] [Algebra (F m) K]
  [IsAlgClosed K] [CharP K 2]

private theorem exists_tensorRep_equiv_sameUniverse
    (hirr : ∀ I : Support m, IsIrreducible (tensorRep m K I))
    (hdist : ∀ I J : Support m,
      Nonempty ((tensorRep m K I).Equiv (tensorRep m K J)) → I = J)
    (hbound : Nat.card (ConjClasses.mk '' {g : SuzukiMatrixGroup m | ¬ 2 ∣ orderOf g}) ≤
      Nat.card (Support m))
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : IsIrreducible τ) :
    ∃ I : Support m, Nonempty (τ.Equiv (tensorRep m K I)) := by
  classical
  by_contra! hnone
  let M : Option (Support m) → Type u := fun i =>
    match i with
    | none => V
    | some I => TensorSpace m K I
  let addM : ∀ i, AddCommGroup (M i) := fun i => by cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module K (M i) := fun i => by cases i <;> dsimp [M] <;> infer_instance
  let rep : ∀ i, Representation K (SuzukiMatrixGroup m) (M i) := fun i =>
    match i with
    | none => τ
    | some I => tensorRep m K I
  have finM : ∀ i, FiniteDimensional K (M i) := by
    intro i
    cases i <;> dsimp [M] <;> infer_instance
  have irr : ∀ i, IsIrreducible (rep i) := by
    intro i
    cases i with
    | none => exact hτ
    | some I => exact hirr I
  have hne : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro e
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some I => exact (hnone I).false e
    | some I =>
      cases j with
      | none => exact (hnone I).false e.symm
      | some J => exact hij (congrArg some (hdist I J ⟨e⟩))
  have hc := Representation.irreducible_family_card_le_pRegularConjClasses M rep 2 hne
  have hh := hc.trans hbound
  simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hh
  omega

/-- Simplicity and distinctness of the literal tensors, together with the
odd-order class bound, give actual intertwining equivalences for all irreducibles. -/
theorem exists_tensorRep_equiv_of_simple_distinct_class_bound
    (hirr : ∀ I : Support m, IsIrreducible (tensorRep m K I))
    (hdist : ∀ I J : Support m,
      Nonempty ((tensorRep m K I).Equiv (tensorRep m K J)) → I = J)
    (hbound : Nat.card (ConjClasses.mk '' {g : SuzukiMatrixGroup m | ¬ 2 ∣ orderOf g}) ≤
      2 ^ (2 * m + 1))
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : IsIrreducible τ) :
    ∃ I : Support m, Nonempty (τ.Equiv (tensorRep m K I)) := by
  classical
  let b : V ≃ₗ[K] (Fin (Module.finrank K V) → K) := (Module.finBasis K V).equivFun
  let σ : Representation K (SuzukiMatrixGroup m) (Fin (Module.finrank K V) → K) :=
    b.conjRingEquiv.toMonoidHom.comp τ
  let e : τ.Equiv σ := .mk b (by
    intro g
    ext x
    simp [σ, LinearEquiv.conjRingEquiv])
  have hσ : IsIrreducible σ :=
    (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv e)).mp hτ
  obtain ⟨I, ⟨f⟩⟩ := exists_tensorRep_equiv_sameUniverse hirr hdist
    (by simpa only [support_card] using hbound) σ hσ
  exact ⟨I, ⟨e.trans f⟩⟩

/-- The same counting argument gives a unique support, not merely a degree. -/
theorem existsUnique_tensorRep_equiv_of_simple_distinct_class_bound
    (hirr : ∀ I : Support m, IsIrreducible (tensorRep m K I))
    (hdist : ∀ I J : Support m,
      Nonempty ((tensorRep m K I).Equiv (tensorRep m K J)) → I = J)
    (hbound : Nat.card (ConjClasses.mk '' {g : SuzukiMatrixGroup m | ¬ 2 ∣ orderOf g}) ≤
      2 ^ (2 * m + 1))
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : IsIrreducible τ) :
    ∃! I : Support m, Nonempty (τ.Equiv (tensorRep m K I)) := by
  obtain ⟨I, ⟨e⟩⟩ :=
    exists_tensorRep_equiv_of_simple_distinct_class_bound hirr hdist hbound τ hτ
  refine ⟨I, ⟨e⟩, ?_⟩
  rintro J ⟨f⟩
  exact hdist J I ⟨f.symm.trans e⟩

/-- The faithful consumer obtains a nonempty support from the same independent
inputs. The extra nonemptiness premise in small-degree recognition is discharged. -/
theorem exists_nonempty_tensorRep_equiv_of_simple_distinct_class_bound
    (hirr : ∀ I : Support m, IsIrreducible (tensorRep m K I))
    (hdist : ∀ I J : Support m,
      Nonempty ((tensorRep m K I).Equiv (tensorRep m K J)) → I = J)
    (hbound : Nat.card (ConjClasses.mk '' {g : SuzukiMatrixGroup m | ¬ 2 ∣ orderOf g}) ≤
      2 ^ (2 * m + 1))
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : IsIrreducible τ)
    (hfaith : Function.Injective τ) :
    ∃ I : Support m, I.Nonempty ∧ Nonempty (τ.Equiv (tensorRep m K I)) := by
  obtain ⟨I, ⟨e⟩⟩ :=
    exists_tensorRep_equiv_of_simple_distinct_class_bound hirr hdist hbound τ hτ
  exact ⟨I, support_nonempty_of_faithful_equiv τ hfaith e, ⟨e⟩⟩

/-- Every finite-dimensional irreducible over an algebraically closed extension
of the defining field is an actual concrete Suzuki Frobenius tensor. -/
theorem exists_tensorRep_equiv (hm : 1 ≤ m)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : IsIrreducible τ) :
    ∃ I : Support m, Nonempty (τ.Equiv (tensorRep m K I)) :=
  exists_tensorRep_equiv_of_simple_distinct_class_bound
    (tensorRep_irreducible hm) (fun _ _ => tensorRep_equiv_imp_eq hm)
    (suzuki_odd_conjClasses_card_le m hm) τ hτ

/-- The support of an irreducible Suzuki representation is uniquely determined
by its actual equivalence class, including the trivial representation. -/
theorem existsUnique_tensorRep_equiv (hm : 1 ≤ m)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : IsIrreducible τ) :
    ∃! I : Support m, Nonempty (τ.Equiv (tensorRep m K I)) :=
  existsUnique_tensorRep_equiv_of_simple_distinct_class_bound
    (tensorRep_irreducible hm) (fun _ _ => tensorRep_equiv_imp_eq hm)
    (suzuki_odd_conjClasses_card_le m hm) τ hτ

/-- A faithful irreducible has a nonempty tensor support on the original
Suzuki matrix group, as required by small-degree recognition. -/
theorem exists_nonempty_tensorRep_equiv (hm : 1 ≤ m)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : IsIrreducible τ)
    (hfaith : Function.Injective τ) :
    ∃ I : Support m, I.Nonempty ∧ Nonempty (τ.Equiv (tensorRep m K I)) :=
  exists_nonempty_tensorRep_equiv_of_simple_distinct_class_bound
    (tensorRep_irreducible hm) (fun _ _ => tensorRep_equiv_imp_eq hm)
    (suzuki_odd_conjClasses_card_le m hm) τ hτ hfaith

end Representation.SuzukiSmallDegree
