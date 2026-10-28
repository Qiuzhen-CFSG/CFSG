module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Reduction
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# Established model cases for the outer-group inspection

For the concrete Suzuki model, full inner–field coverage makes Out(Sz)
a quotient of the cyclic defining-field Galois group. For A₆, the proved
outer order four makes every odd subgroup trivial. These are actual model
calculations used in the two inspections on printed p.510; they do not
assert that the remaining Theorem C models have been treated.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 1.3.4;
the Suzuki coverage is the GLS3 2.5.12 input cited in `Suzuki.OuterIndex`.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups

/-- The full outer group of the concrete Suzuki model is cyclic. -/
theorem suzuki_outer_isCyclic (m : ℕ) (hm : 1 ≤ m) :
    IsCyclic (MulAut.Outer (SuzukiMatrixGroup m)) := by
  let I := MulAut.innerSubgroup (SuzukiMatrixGroup m)
  let f := (QuotientGroup.mk' I).comp (suzukiFieldAutHom m)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective I q
    obtain ⟨g, σ, rfl⟩ := suzukiAut_eq_inner_mul_field m hm a
    refine ⟨σ, ?_⟩
    have hg : QuotientGroup.mk' I (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    change QuotientGroup.mk' I (suzukiFieldAutHom m σ) = _
    rw [map_mul, hg, one_mul, suzukiFieldAutHom_apply]
  exact isCyclic_of_surjective f hf

/-- The Suzuki case of the first inspection. -/
theorem suzuki_outer_cyclicNormalOddQuotient (m : ℕ) (hm : 1 ≤ m) :
    HasCyclicNormalOddQuotient (MulAut.Outer (SuzukiMatrixGroup m)) := by
  let := suzuki_outer_isCyclic m hm
  exact hasCyclicNormalOddQuotient_of_isCyclic

/-- An actual Suzuki isomorphism discharges the abelian-outer case in 1.2.1(3). -/
theorem suzuki_model_outer_isMulCommutative {Q : Type*} [Group Q]
    (m : ℕ) (hm : 1 ≤ m) (e : Q ≃* SuzukiMatrixGroup m) :
    IsMulCommutative (MulAut.Outer Q) := by
  let := suzuki_outer_isCyclic m hm
  let : IsCyclic (MulAut.Outer Q) := isCyclic_of_injective (MulAut.outerCongr e).toMonoidHom
    (MulAut.outerCongr e).injective
  exact IsCyclic.isMulCommutative

/-- The exceptional alternating degree six has outer order four. -/
theorem alternating_six_outer_cyclicNormalOddQuotient :
    HasCyclicNormalOddQuotient (MulAut.Outer (alternatingGroup (Fin 6))) := by
  apply hasCyclicNormalOddQuotient_of_isPGroup_two
  exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
