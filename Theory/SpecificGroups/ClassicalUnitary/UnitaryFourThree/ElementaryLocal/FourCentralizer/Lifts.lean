module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.ScalarKernel
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.ProjectiveTransfer

/-!
# Commutation dichotomy for projective involution lifts

The kernel of the defining SU₄(3) → PSU₄(3) map consists of fourth-root scalar
matrices. The projection in the scalar-kernel module is definitionally the
same map as `Model.project`. Its centrality makes the commutator of two
projectively commuting involution lifts have square one. Over Nine that
scalar is 1 or -1, giving literal matrix commutation or anticommutation.

Source: the classical projective conventions in GLS3, chapter 2; this is a
preliminary for the PSU₄(3) local calculation in Aschbacher–Smith,
Theorem 0.1.2(4), printed p.4 of `refs/quasithin.pdf`.
-/

public noncomputable section

open Matrix BenderSuzuki.MatrixGroups Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer

/-- The actual determinant-one isometry group before projectivization. -/
abbrev SU := (form 4).specialSubgroup

/-- Every element in the projection kernel is a central scalar. -/
theorem project_kernel_central : (project 4).ker ≤ center SU := by
  intro z hz
  obtain ⟨u, hu, huz⟩ := (IsotropicStabilizers.mem_project_kernel_iff (form 4) z).mp hz
  apply mem_center_iff.mpr
  intro g
  apply Subtype.ext
  change g.val * z.val = z.val * g.val
  rw [← huz]
  exact (GeneralLinearGroup.scalar_commute u g.val).symm

/-- Projectively commuting involution lifts have commutator of square one. -/
theorem commutator_square_eq_one (a b : SU)
    (ha : (project 4 a) ^ 2 = 1) (hab : Commute (project 4 a) (project 4 b)) :
    ⁅a, b⁆ ^ 2 = 1 := by
  exact Subgroup.commutator_square_eq_one_of_central_kernel
    (project 4) project_kernel_central a b ha hab

/-- The only possible scalar commutators of involution lifts are I and -I. -/
theorem commute_or_anticommute (a b : SU)
    (ha : (project 4 a) ^ 2 = 1) (hab : Commute (project 4 a) (project 4 b)) :
    Commute a b ∨ a.val.val * b.val.val = -(b.val.val * a.val.val) := by
  have hz : ⁅a, b⁆ ∈ (project 4).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hab.eq
  obtain ⟨u, hu, huz⟩ := (IsotropicStabilizers.mem_project_kernel_iff (form 4) _).mp hz
  have hu2 : (u : FiniteField.Nine) ^ 2 = 1 := by
    have he := congrArg (fun g : SU => g.val) (commutator_square_eq_one a b ha hab)
    change (⁅a, b⁆.val) ^ 2 = 1 at he
    rw [← huz, ← map_pow] at he
    exact congrArg (fun g : GL (Fin 4) FiniteField.Nine => g.val 0 0) he
  rcases sq_eq_one_iff.mp hu2 with hu1 | hum
  · left
    apply commutatorElement_eq_one_iff_commute.mp
    apply Subtype.ext
    rw [← huz]
    have he : u = 1 := Units.ext hu1
    rw [he, map_one]
    rfl
  · right
    have hprod : a * b = ⁅a, b⁆ * (b * a) := by
      simp only [commutatorElement_def]
      group
    have he := congrArg (fun g : SU => g.val.val) hprod
    change a.val.val * b.val.val = ⁅a, b⁆.val.val * (b.val.val * a.val.val) at he
    rw [← huz, GeneralLinearGroup.coe_scalar] at he
    simpa only [hum, map_neg, map_one, neg_mul, one_mul] using he
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer
