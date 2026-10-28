module

public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction.FixedLifts
public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction.RootQuotient
public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction.DerivedBound
public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction.TrivialActionCentrality

/-!
# Nontrivial field action on the Sz(8) universal covering kernel

The canonical lift of entrywise Frobenius through a universal covering of
Sz(8) moves an element of its kernel of order four. If it fixed that kernel,
the full root-center preimage would be central in the lifted root group.
Its elementary quotient of order eight would then force derived order at
most eight, contradicting the derived order 32 obtained by Sylow transfer.
All maps retain the actual Suzuki matrix identification.

The resulting witness also proves nontriviality of the literal canonical
multiplier action. The chosen matrix identification, universal covering,
and kernel order remain the earlier inputs supplied by a consumer.

Source: GLS3 section 6.3, Sz(8) case, printed p.337; Aschbacher--Smith
I.2.2(7a), printed p.412 of `refs/quasithin.pdf`.
-/

namespace BenderSuzuki.MatrixGroups.MultiplierFieldAction
open Theory.GroupTheory

universe u
variable {S U : Type u}
variable [Group S] [Finite S] [IsQuasisimple S]
variable [Group U] [Finite U] [IsQuasisimple U]

/-- The literal canonical multiplier action satisfies the cubic relation. -/
public theorem multiplierAction_cube
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f) :
    Covering.multiplierAction f hf
      (MulAut.congr e.symm (suzukiFieldAutomorphism 1)) ^ 3 = 1 := by
  rw [← map_pow, ← map_pow, suzukiFieldAutomorphism_one_cube, map_one, map_one]

/-- Triviality of the literal multiplier action gives the exact fixed-subgroup
preimage needed in the source's Sylow-center argument. -/
public theorem fixedSubgroup_of_multiplierAction_eq_one
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (htrivial : Covering.multiplierAction f hf
      (MulAut.congr e.symm (suzukiFieldAutomorphism 1)) = 1) :
    (liftedField e f hf).fixedSubgroup =
      (suzukiFieldAutomorphism 1).fixedSubgroup.comap (matrixProjection e f) := by
  apply liftedField_fixedSubgroup e f hf hfour
  intro k
  exact congrArg (fun a : MulAut f.toMonoidHom.ker => (a k : U)) htrivial

/-- The canonical lift of the actual Sz(8) field automorphism moves an element
of the universal covering kernel. This completes the contradiction in GLS3
section 6.3, p.337, using only the chosen cover and its kernel order. -/
public theorem exists_moved_kernel_element
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    ∃ x : f.toMonoidHom.ker,
      hf.liftMulAut (MulAut.congr e.symm (suzukiFieldAutomorphism 1)) x ≠ (x : U) := by
  by_contra hfixed
  push Not at hfixed
  exact rootCenterPreimage_not_le_center e f hfour
    (rootCenterPreimage_le_center_of_liftedField_fixed e f hf hfour hfixed)

/-- The literal canonical multiplier action of the Sz(8) field automorphism
is nontrivial, discharging the field-action premise used in I.2.2(7a). -/
public theorem multiplierAction_ne_one
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    Covering.multiplierAction f hf
      (MulAut.congr e.symm (suzukiFieldAutomorphism 1)) ≠ 1 := by
  intro htrivial
  obtain ⟨x, hx⟩ := exists_moved_kernel_element e f hf hfour
  exact hx (congrArg (fun a : MulAut f.toMonoidHom.ker => (a x : U)) htrivial)

end BenderSuzuki.MatrixGroups.MultiplierFieldAction
