module

public import Theory.SpecificGroups.PSL3.CartanActions.ResidualLinear
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.Reduction
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# A common automorphism-classification input for SL₃ and PSL₃

Coverage of the projective automorphism group by its standard subgroup gives
literal linear-field-graph factorizations on both carriers. The projective
factorization uses the proved matrix commutation laws. Each factor lifts to
SL₃, and perfectness makes the action on the central quotient injective, so
the lifted factorization equals the original special linear automorphism.
The cubic scalar quotient is retained throughout.

This proves the equivalence of the coverage interfaces, not the earlier
automorphism-classification theorem itself. Source: GLS3, Theorem 2.5.12
and §2.7; used in Aschbacher–Smith 13.8.20, printed p.954.
-/

public section

open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions.SixCommutators
namespace Matrix.PSL3.CartanActions.ActorCoverage
variable (F : Type*) [Field F]

/-- Perfectness makes the actual central-quotient action faithful. -/
theorem centerAction_injective : Function.Injective (centerAction F) := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have he : centerAction F = MulAut.centralQuotientAction (MulEquiv.refl PSL(3,F)) := by
    ext a x
    obtain ⟨y,rfl⟩ := projection_surjective F x
    change centerAction F a (QuotientGroup.mk y) =
      MulAut.centralQuotientAction (MulEquiv.refl PSL(3,F)) a
        ((MulEquiv.refl PSL(3,F)) (QuotientGroup.mk' (Subgroup.center SL(3,F)) y))
    rw [centerAction_mk, MulAut.centralQuotientAction_apply]
    rfl
  rw [he]
  exact MulAut.centralQuotientAction_injective _

/-- Standard subgroup coverage supplies the explicit projective factors. -/
theorem projectiveCoverage_of_standard_eq_top (hcover : standard F = ⊤) :
    ProjectiveCoverage F := by
  intro α
  obtain ⟨m,σ,h | h⟩ := ResidualLinear.standard_opposition_factorization α
    (by rw [hcover]; trivial)
  · exact ⟨m,σ,false, by simpa only [projectiveActor, Bool.false_eq_true,
      ↓reduceIte, mul_one] using h⟩
  · exact ⟨m,σ,true,h⟩

/-- Literal projective factors all lie in the standard subgroup. -/
theorem standard_eq_top_of_projectiveCoverage (hcover : ProjectiveCoverage F) :
    standard F = ⊤ := by
  apply top_unique
  intro α _
  obtain ⟨m,σ,ε,rfl⟩ := hcover α
  apply (standard F).mul_mem
    ((standard F).mul_mem (linearConj_mem_standard F m) (fieldAction_mem_standard F σ))
  cases ε
  · exact (standard F).one_mem
  · exact oppositionGraph_mem_standard F

/-- Lift the explicit factors through the faithful central-quotient action. -/
theorem specialCoverage_of_projectiveCoverage (hcover : ProjectiveCoverage F) :
    SpecialCoverage F := by
  intro α
  obtain ⟨m,σ,ε,h⟩ := hcover (centerAction F α)
  refine ⟨m,σ,ε,centerAction_injective F ?_⟩
  rw [centerAction_specialActor, h]

/-- One earlier projective classification input suffices for both carriers. -/
theorem specialCoverage_of_standard_eq_top (hcover : standard F = ⊤) :
    SpecialCoverage F :=
  specialCoverage_of_projectiveCoverage F
    (projectiveCoverage_of_standard_eq_top F hcover)

end Matrix.PSL3.CartanActions.ActorCoverage
