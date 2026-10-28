module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.Envelope

/-!
# Pulling concrete models back through the scalar quotient

The inverse image of a solvable subgroup under a homomorphism with solvable
kernel is solvable. Consequently kernel models compose through the scalar
projection. In the normal-layer case we pull the subgroup back inside the full
preimage and use the actual quotient equivalence to retain the solvable outer
layer. This does not assert maximal-subgroup coverage.

Source obligation: Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed
pp.4 and 482 of `refs/quasithin.pdf`; GLS3, §2.7 for the scalar quotient.
-/

public noncomputable section
namespace CFSG.Quasithin.MainConverse.UnitaryFourIrreducible

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

private theorem solvable_subgroupComap_kernel {G H : Type} [Group G] [Group H]
    (f : G →* H) [Group.IsSolvable f.ker] (L : Subgroup H) :
    Group.IsSolvable (f.subgroupComap L).ker := by
  let k : (f.subgroupComap L).ker →* f.ker :=
    { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply Group.isSolvable_of_isSolvable_injective (f := k)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : f.ker => z.val) h

private theorem solvable_comap {G H : Type} [Group G] [Group H]
    (f : G →* H) [Group.IsSolvable f.ker] (L : Subgroup H)
    [Group.IsSolvable L] : Group.IsSolvable (L.comap f) := by
  let q := f.subgroupComap L
  let : Group.IsSolvable q.ker := solvable_subgroupComap_kernel f L
  exact Group.isSolvable_of_ker_le_range q.ker.subtype q (by simp)

/-- Compose the concrete map, retaining both solvable kernels. -/
theorem HasSolvableKernelModel.pullback {G H : Type} [Group G] [Group H]
    (h : HasSolvableKernelModel H) (f : G →* H) [Group.IsSolvable f.ker] :
    HasSolvableKernelModel G := by
  rcases h with ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
  · let := hg
    exact Or.inl ⟨g.comp f, solvable_comap f g.ker⟩
  · let := hg
    exact Or.inr (Or.inl ⟨g.comp f, solvable_comap f g.ker⟩)
  · let := hg
    exact Or.inr (Or.inr ⟨g.comp f, solvable_comap f g.ker⟩)

/-- A projective kernel model lifts through the entire scalar kernel. -/
theorem fullPreimage_hasSolvableKernelModel_of_projective {n : ℕ}
    (U : Subgroup (Carrier n)) (h : HasSolvableKernelModel U) :
    HasSolvableKernelModel (fullPreimage U) := by
  let := preimageProjection_kernel_isSolvable U
  exact h.pullback (preimageProjection U)

/-- Pull back relative normality and identify the actual outer quotient. -/
theorem fullPreimage_hasSolvableLayersModel_of_projective {n : ℕ}
    (U : Subgroup (Carrier n)) (h : HasSolvableLayersModel U) :
    HasSolvableLayersModel (fullPreimage U) := by
  let := preimageProjection_kernel_isSolvable U
  cases h with
  | direct model =>
    exact .direct (fullPreimage_hasSolvableKernelModel_of_projective U model)
  | normal L outer model =>
    let := outer
    let K := L.comap (preimageProjection U)
    have houter : Group.IsSolvable (fullPreimage U ⧸ K) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (preimageQuotientEquiv U L).toMonoidHom)
        (preimageQuotientEquiv U L).injective
    let := solvable_subgroupComap_kernel (preimageProjection U) L
    exact .normal K houter (model.pullback ((preimageProjection U).subgroupComap L))

/-- The solvable projective case includes the scalar extension. -/
theorem fullPreimage_hasSolvableLayersModel_of_solvable {n : ℕ}
    (U : Subgroup (Carrier n)) [Group.IsSolvable U] :
    HasSolvableLayersModel (fullPreimage U) :=
  fullPreimage_hasSolvableLayersModel_of_projective U
    (.direct (HasSolvableKernelModel.of_solvable U))

end CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
