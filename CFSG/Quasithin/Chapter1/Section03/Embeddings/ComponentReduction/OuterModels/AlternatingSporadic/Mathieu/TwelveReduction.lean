module

public import Theory.GroupTheory.SylowOuterAutomorphisms
public import Theory.GroupTheory.CyclicNormalOddQuotient
public import Theory.Mathieu.M12.Properties.SylowAutomorphisms

/-!
# Reducing the M₁₂ outer restriction to its Sylow automorphisms

The established calculation on the actual Witt-design group shows that an
automorphism fixing the marked Sylow two-subgroup is inner. Thus it suffices
to prove that the automorphism group of that 64-element subgroup is a
two-group. The latter calculation is an explicit premise here.

Source: the outer-group inspection on printed p.510 of Aschbacher–Smith,
combined 1 March 2004 manuscript; GLS3, Table 5.3b.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair

/-- The only remaining input for this Sylow route is the small subgroup's automorphism bound. -/
theorem m12_outer_isPGroup_two_of_sylow_aut
    (h : IsPGroup 2 (MulAut sylowCandidate)) : IsPGroup 2 (MulAut.Outer M12) := by
  apply MulAut.isPGroup_outer_of_sylow_aut commonSylow h
  intro a ha
  rcases SylowAutomorphisms.eq_one_or_conj_of_fixes_sylow a ha with rfl | rfl
  · exact (MulAut.innerSubgroup M12).one_mem
  · exact ⟨z, rfl⟩

/-- Transport of the conditional M₁₂ calculation through the actual model equivalence. -/
theorem m12_model_outer_cyclicNormalOddQuotient_of_sylow_aut
    {S : Type*} [Group S] (e : S ≃* M12)
    (h : IsPGroup 2 (MulAut sylowCandidate)) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  exact (hasCyclicNormalOddQuotient_of_isPGroup_two
    (m12_outer_isPGroup_two_of_sylow_aut h)).of_injective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
