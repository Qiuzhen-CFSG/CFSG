module

public import Theory.SpecificGroups.SymplecticFour.Flag
public import Theory.Representation.FirstCohomologySymplecticFour.Generation

/-!
# The eight matrix root subgroups of symplectic four-space

Each standard root family is an injective additive parametrization. Its image
is already a subgroup, so the closure used by the chapter interfaces has exactly
one field element as parameter and has the same order as the field. All eight
families use the original matrices from the root-generation theorem.

The multiplication calculation is the one used in
`FirstCohomologySymplecticFour.LargeField`; it is exposed here independently of
cohomology for the root-normalizer and torus calculations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3c),
printed p.250 (PDF p.261); the standard type-C₂ matrix root parametrizations.
-/

@[expose] public section

open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootSubgroup
variable {F : Type*} [Field F]

/-- Addition of parameters is multiplication in each matrix root family. -/
theorem element_add (r : Fin 8) (s t : F) :
    rootElement r s * rootElement r t = rootElement r (s + t) := by
  apply Subtype.ext
  change rootMatrix r s * rootMatrix r t = rootMatrix r (s + t)
  fin_cases r <;>
    simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.single_add] <;> abel_nf <;> simp

/-- The zero parameter gives the identity matrix. -/
theorem element_zero (r : Fin 8) : rootElement r (0 : F) = 1 := by
  apply Subtype.ext
  fin_cases r <;> simp [rootElement, rootMatrix, Matrix.single_zero]

/-- The additive field, with multiplicative notation, embedded in the matrix group. -/
def parameter (r : Fin 8) : Multiplicative F →* Sp F where
  toFun t := rootElement r t.toAdd
  map_one' := element_zero r
  map_mul' s t := (element_add r s.toAdd t.toAdd).symm

/-- A distinguished matrix entry recovers the root parameter. -/
theorem element_injective (r : Fin 8) : Function.Injective (rootElement (K := F) r) := by
  intro s t h
  let i : Fin 2 ⊕ Fin 2 :=
    ![.inl 0, .inr 0, .inl 1, .inr 1, .inl 0, .inr 0, .inl 0, .inl 1] r
  let j : Fin 2 ⊕ Fin 2 :=
    ![.inr 0, .inl 0, .inr 1, .inl 1, .inr 1, .inl 1, .inl 1, .inl 0] r
  have hh := congrArg (fun g : Sp F => g.val i j) h
  fin_cases r <;> simpa [i, j, rootElement, rootMatrix, Matrix.single, Matrix.fromBlocks]
    using hh

/-- The root parametrization is an embedding. -/
theorem parameter_injective (r : Fin 8) : Function.Injective (parameter (F := F) r) :=
by
  intro s t h
  have hh : s.toAdd = t.toAdd := element_injective (F := F) r h
  exact congrArg (Multiplicative.ofAdd : F → Multiplicative F) hh

/-- The actual matrix root subgroup, in the convention used by the chapter interfaces. -/
def group (r : Fin 8) : Subgroup (Sp F) :=
  closure (Set.range (rootElement (K := F) r))

/-- No extra elements are added by taking the subgroup closure. -/
theorem group_eq_range (r : Fin 8) : group (F := F) r = (parameter r).range := by
  apply le_antisymm
  · apply (closure_le _).2
    rintro _ ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩
  · rintro _ ⟨t, rfl⟩
    exact subset_closure ⟨t.toAdd, rfl⟩

/-- Membership retains an actual matrix parameter. -/
theorem mem_group_iff (r : Fin 8) (g : Sp F) :
    g ∈ group r ↔ ∃ t : F, rootElement r t = g := by
  rw [group_eq_range]
  rfl

/-- The actual root subgroup is isomorphic to the additive field. -/
noncomputable def equiv (r : Fin 8) : Multiplicative F ≃* group (F := F) r :=
  (MonoidHom.ofInjective (parameter_injective r)).trans
    (MulEquiv.subgroupCongr (group_eq_range r).symm)

/-- Every root subgroup has exactly the field order. -/
theorem card (r : Fin 8) : Nat.card (group (F := F) r) = Nat.card F :=
  (Nat.card_congr (equiv r).toEquiv).symm

end Theory.SpecificGroups.SymplecticFour.RootSubgroup
