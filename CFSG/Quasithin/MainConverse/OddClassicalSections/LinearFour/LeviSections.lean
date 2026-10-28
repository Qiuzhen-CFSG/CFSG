module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.LinearThree
public import Theory.SpecificGroups.PSL3Three.Simplicity
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel

/-!
# Simple sections of the three-dimensional Levi factor over F₃

Every simple section of PSL₃(3) is either prime cyclic or PSL₃(3) itself:
a proper subgroup is solvable, while a surjection from the whole simple
group onto a nontrivial group is injective. The canonical central quotient
identifies SL₃(3) with PSL₃(3). The determinant then removes the abelian
outer layer in GL₃(3), leaving the same two possibilities.

These are the Levi-factor calculations for the PSL₄(3) proper-section
argument in Aschbacher–Smith, Theorem 0.1.2(4), printed p.4. They do not
assert that every proper subgroup of PSL₄(3) lies in a parabolic.
-/

namespace CFSG.Quasithin.MainConverse.LinearFour

open CFSG.KnownSimple

private theorem injective_of_simple_surjective
    {H S : Type*} [Group H] [IsSimpleGroup H] [Group S] [Nontrivial S]
    (f : H →* S) (hf : Function.Surjective f) : Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨x, rfl⟩ := hf s
    exact False.elim (hs (show x ∈ f.ker from h ▸ Subgroup.mem_top x))

/-- The two actual carrier possibilities for a simple section of PSL₃(3). -/
public theorem psl3_simpleSection
    (U : Subgroup Matrix.PSL3Three.PSL)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : U →* S) (hf : Function.Surjective f) :
    IsPrimeCyclicCarrier S ∨ Nonempty (S ≃* Matrix.PSL3Three.PSL) := by
  by_cases hU : U = ⊤
  · let e : U ≃* Matrix.PSL3Three.PSL :=
      (MulEquiv.subgroupCongr hU).trans Subgroup.topEquiv
    let := isSimpleGroup_psl3_three
    let : IsSimpleGroup U := e.isSimpleGroup
    exact Or.inr ⟨(MulEquiv.ofBijective f
      ⟨injective_of_simple_surjective f hf, hf⟩).symm.trans e⟩
  · let := Matrix.PSL3Three.isSolvable_of_ne_top U hU
    let : Group.IsSolvable S := Group.isSolvable_of_surjective hf
    exact Or.inl (primeCyclic_of_solvable_simple S)

/-- A faithful map into SL₃(3) suffices; the quotient is an actual simple image. -/
public theorem sl3_simpleSection
    {H S : Type*} [Group H] [Group S] [IsSimpleGroup S]
    (j : H →* Matrix.PSL3Three.SL) (hj : Function.Injective j)
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsPrimeCyclicCarrier S ∨ Nonempty (S ≃* Matrix.PSL3Three.PSL) := by
  let k := Matrix.PSL3Three.equiv.toMonoidHom.comp j
  have hk : Function.Injective k := Matrix.PSL3Three.equiv.injective.comp hj
  let e := Subgroup.equivMapOfInjective U k hk
  exact psl3_simpleSection (U.map k) (f.comp e.symm.toMonoidHom)
    (hf.comp e.symm.surjective)

/-- Every simple section of GL₃(3) is prime cyclic or the concrete PSL₃(3). -/
public theorem gl3_simpleSection
    (U : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)))
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : U →* S) (hf : Function.Surjective f) :
    IsPrimeCyclicCarrier S ∨ Nonempty (S ≃* Matrix.PSL3Three.PSL) := by
  let d := Matrix.GeneralLinearGroup.det (n := Fin 3) (R := ZMod 3)
  rcases Subgroup.simple_section_normal_or_quotient d.ker U f hf with
    ⟨W, g, hg⟩ | ⟨W, g, hg⟩
  · let e := (Matrix.SpecialLinearGroup.determinantKernelEquiv
      (Fin 3) (ZMod 3)).symm
    exact sl3_simpleSection e.toMonoidHom e.injective W g hg
  · let e := QuotientGroup.quotientKerEquivRange d
    let : Group.IsSolvable
        (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3) ⧸ d.ker) :=
      Group.isSolvable_of_isSolvable_injective e.injective
    let : Group.IsSolvable S := Group.isSolvable_of_surjective hg
    exact Or.inl (primeCyclic_of_solvable_simple S)

/-- The explicitly identified Levi sections are in the constructed catalogue. -/
public theorem gl3_simpleSection_constructed
    {H S : Type*} [Group H] [Group S] [IsSimpleGroup S]
    (j : H →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 3))
    (hj : Function.Injective j)
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  let e := Subgroup.equivMapOfInjective U j hj
  rcases gl3_simpleSection (U.map j) (f.comp e.symm.toMonoidHom)
      (hf.comp e.symm.surjective) with hc | hS
  · exact .cyclic hc
  · obtain ⟨eS⟩ := hS
    exact .classical (.linear 3 3
      ⟨Nat.prime_three.isPrimePow, by decide, by omega⟩
      ⟨ZMod 3, inferInstance, inferInstance, by simp, ⟨eS⟩⟩)

end CFSG.Quasithin.MainConverse.LinearFour
