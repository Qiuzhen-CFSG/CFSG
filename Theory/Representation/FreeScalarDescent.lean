module

public import Theory.Representation.ScalarDescent
public import Theory.Representation.FreeBasis

/-!
# Scalar descent of free representations

For a finite group and a finite-dimensional representation over a field, freeness
over the group algebra descends through an arbitrary coefficient field extension.
There is no restriction on the characteristic, even when it divides the group
order. This supplies the descent step used in ABG, Chapter II, Section 8, Lemma 4.

Choose a finite group-algebra basis after extension and compare the representation
with the free representation on that index set. The canonical field bases from
`FreeBasis` identify the scalar extension of a free representation with the free
representation over the larger field: both actions permute the group coordinate
by left multiplication. Apply `repEquiv_of_extendScalars` to descend the resulting
equivalence of finite-dimensional representations, then transport the free
group-algebra basis back. No semisimplicity or averaging argument is used.
-/

open scoped TensorProduct

noncomputable section

namespace Representation

private def extendScalarsFreeEquiv
    {F E A : Type*} [Field F] [Field E] [Algebra F E] [Group A]
    (indices : Type*) :
    extendScalars E (free F A indices) ≃ₗ free E A indices := by
  let sourceBasis := (freeBasis F A indices).baseChange E
  let targetBasis := freeBasis E A indices
  let equivalence := sourceBasis.equiv targetBasis (_root_.Equiv.refl _)
  refine ⟨equivalence, fun element => ?_⟩
  apply sourceBasis.ext
  intro index
  rcases index with ⟨index, actor⟩
  change equivalence ((extendScalars E (free F A indices)) element
    (sourceBasis (index, actor))) =
      free E A indices element (equivalence (sourceBasis (index, actor)))
  have action : (extendScalars E (free F A indices)) element
      (sourceBasis (index, actor)) = sourceBasis (index, element * actor) := by
    simp [sourceBasis, Module.Basis.baseChange_apply, extendScalars_apply,
      LinearMap.baseChange_tmul]
  rw [action]
  simp [equivalence, targetBasis, Module.Basis.equiv_apply]

/-- Group-algebra freeness of a finite-dimensional representation descends through
any coefficient field extension, including in modular characteristic. -/
public theorem free_asModule_of_extendScalars
    {F E A V : Type*} [Field F] [Field E] [Algebra F E]
    [Group A] [Finite A] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (rho : Representation F A V)
    (hfree : Module.Free (MonoidAlgebra E A) (extendScalars E rho).asModule) :
    Module.Free (MonoidAlgebra F A) rho.asModule := by
  classical
  let := hfree
  let : Module.Finite (MonoidAlgebra E A) (extendScalars E rho).asModule :=
    Module.Finite.of_restrictScalars_finite E _ _
  let indices := Module.Free.ChooseBasisIndex (MonoidAlgebra E A)
    (extendScalars E rho).asModule
  let basis := Module.Free.chooseBasis (MonoidAlgebra E A) (extendScalars E rho).asModule
  let equivalence := basis.equiv (freeAsModuleBasis E A indices) (_root_.Equiv.refl _)
  let extendedEquiv := repEquivOfModuleEquiv (extendScalars E rho)
    (free E A indices) equivalence
  let : Finite indices := inferInstance
  let : FiniteDimensional F (indices →₀ MonoidAlgebra F A) :=
    Module.Finite.of_basis (freeBasis F A indices)
  obtain ⟨descended⟩ := repEquiv_of_extendScalars rho (free F A indices)
    ⟨extendedEquiv.trans (extendScalarsFreeEquiv indices).symm⟩
  let moduleMap := RepMap.equivLinearMapAsModule _ _ descended.symm.toRepMap
  let moduleEquiv := LinearEquiv.ofBijective moduleMap descended.symm.bijective
  exact Module.Free.of_equiv' (free_asModule_free F A indices) moduleEquiv

end Representation
