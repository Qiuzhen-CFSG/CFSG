module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Action
public import Mathlib.Algebra.Group.Action.TransferInstance

/-!
# A fixed simple copy for type inertia

Type inertia acts on the actual copies of a seed inside its orbit span.
These copies are equivalent to the ring-theoretic copies in that submodule.
Their odd cardinality gives a fixed copy under a two-group; the inertia
criterion then proves homogeneity in the selected copy's own orbit span.

Source: Aschbacher–Smith, Lemma A.1.42(2), printed p.32.
-/
@[expose] public section
noncomputable section
open scoped MonoidAlgebra
namespace Representation.BinaryOffender.Homogeneous

private def copiesWithinEquiv {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (S U : Submodule R M) :
    SimpleCopies.Copies R S U ≃
      {A : Submodule R M // A ≤ U ∧ Nonempty (S ≃ₗ[R] A)} where
  toFun A := ⟨A.val.map U.subtype, U.map_subtype_le _,
    ⟨A.property.some.trans (A.val.equivMapOfInjective _ U.subtype_injective)⟩⟩
  invFun A := ⟨A.val.comap U.subtype,
    ⟨A.property.2.some.trans (Submodule.comapSubtypeEquivOfLe A.property.1).symm⟩⟩
  left_inv A := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective U.subtype_injective _
  right_inv A := by
    apply Subtype.ext
    change (A.val.comap U.subtype).map U.subtype = A.val
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr A.property.1]

variable {E W P : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) E W} [Group P]
namespace TypeAction
variable (c : TypeAction σ P)

/-- Actual copies of S lying in its orbit span. -/
def Copies (S : Subrepresentation σ) :=
  {A : Subrepresentation σ // A ≤ c.span S ∧ SameModule S A}

/-- Identify the copies used by inertia with the ring-theoretic counting set. -/
private def copiesEquiv (S : Subrepresentation σ) : c.Copies S ≃
    SimpleCopies.Copies (ZMod 2)[E] S.asSubmodule (c.span S).asSubmodule := by
  refine (show c.Copies S ≃
      {A : Submodule (ZMod 2)[E] σ.asModule //
        A ≤ (c.span S).asSubmodule ∧ Nonempty (S.asSubmodule ≃ₗ[(ZMod 2)[E]] A)} from ?_).trans
    (copiesWithinEquiv S.asSubmodule (c.span S).asSubmodule).symm
  exact {
    toFun := fun A => ⟨A.val.asSubmodule, A.property.1,
      (sameModule_iff_linearEquiv _ _).mp A.property.2⟩
    invFun := fun A => ⟨Subrepresentation.ofSubmodule' A.val, A.property.1,
      (sameModule_iff_linearEquiv _ _).mpr A.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Inertia acts by the original conjugation on actual copies, with no fixed
member assumed. -/
@[instance_reducible] def copiesAction (S : Subrepresentation σ) : MulAction (c.inertia S) (c.Copies S) where
  smul t A := ⟨c.conjugate t.val A.val, by
    constructor
    · exact (c.conjugate t.val).monotone A.property.1 |>.trans (c.conjugate_span t.val S).le
    · exact t.property.trans ((c.same t.val S A.val).mp A.property.2)⟩
  one_smul A := Subtype.ext (c.one A.val)
  mul_smul t u A := Subtype.ext (c.mul t.val u.val A.val)

theorem inertia_eq_of_sameModule {S A : Subrepresentation σ} (he : SameModule S A) :
    c.inertia S = c.inertia A := by
  ext t
  constructor
  · intro ht
    exact he.symm.trans (ht.trans ((c.same t S A).mp he))
  · intro ht
    exact he.trans (ht.trans ((c.same t A S).mp he.symm))

/-- A two-group has a homogeneous simple copy of the seed's actual type in
the seed's orbit span. The selected orbit span may be smaller. -/
theorem exists_homogeneous_copy [Finite W] (hP : IsPGroup 2 P)
    (S : Subrepresentation σ) (hS : IsIrreducible S.toRepresentation) :
    ∃ A : Subrepresentation σ, A ≤ c.span S ∧ SameModule S A ∧
      IsIrreducible A.toRepresentation ∧
      homogeneousPart A (c.span A).toSubmodule = A.toSubmodule := by
  let : Finite σ.asModule := Finite.of_equiv W σ.asModuleEquiv.symm.toEquiv
  let := simple_asSubmodule S hS
  let := c.copiesAction S
  let e := c.copiesEquiv S
  let : MulAction (c.inertia S)
      (SimpleCopies.Copies (ZMod 2)[E] S.asSubmodule (c.span S).asSubmodule) :=
    e.symm.mulAction (c.inertia S)
  have hne : Nonempty (SimpleCopies.Copies (ZMod 2)[E]
      S.asSubmodule (c.span S).asSubmodule) :=
    ⟨e ⟨S, c.le_span S, SameModule.refl S⟩⟩
  obtain ⟨U, hU⟩ := SimpleCopies.exists_fixed_copy (hP.to_subgroup (c.inertia S)) hne
  let A := e.symm U
  have hirr := A.property.2.irreducible hS
  refine ⟨A.val, A.property.1, A.property.2, hirr,
    (c.homogeneous_iff_inertia_fixes A.val hirr).mpr ?_⟩
  intro t ht
  have ht' : t ∈ c.inertia S := (c.inertia_eq_of_sameModule A.property.2).symm ▸ ht
  have hu := congrArg e.symm (hU ⟨t, ht'⟩)
  change e.symm (e ((⟨t,ht'⟩ : c.inertia S) • A)) = A at hu
  have hf : (⟨t,ht'⟩ : c.inertia S) • A = A := by
    exact (e.symm_apply_apply _).symm.trans hu
  exact congrArg Subtype.val hf

end TypeAction
end Representation.BinaryOffender.Homogeneous
