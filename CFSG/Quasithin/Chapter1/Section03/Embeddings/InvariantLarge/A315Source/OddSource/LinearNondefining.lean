module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.OddSource.FrattiniSquare
public import Theory.SpecificGroups.PSL3.ThreeWeightLift
public import Theory.Representation.ThreeWeightSquare.CentralQuotient
/-!
# The nondefining odd PSL₃ branch of the original intrinsic pair

Every two-power normalizer actor lifts through the actual scalar quotient
with a natural or contragredient degree-three matrix formula. Its square
fixes the nondefining p-subgroup pointwise, so the original normalizer
Frattini commutator identity gives a contradiction. The marked component,
quotient projection and ambient conjugation are unchanged throughout.
Source: Aschbacher–Smith, A.3.15 and Proposition 1.3.4, pp.50–51, 510–511.
-/
public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
variable {J : Type*} [Group J] [Finite J]
variable {κ : GroupClass} {D B : Subgroup J} {S : Sylow 2 J} {p q : ℕ}

theorem not_linear_nondefining
    (h : OddCartan.AmbientInput κ D B S p)
    (ha : SourceTransport.PairAction p (S : Subgroup J) B)
    (hq : q.Prime) (ho : Odd q) (hpq : p≠q)
    (hm : ClassicalGroup.IsPSL D 3 q) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨h.prime⟩
  let : Fact q.Prime := ⟨hq⟩
  let _ := Fintype.ofFinite F
  let _ : CharP F q := charP_of_card_eq_prime_pow (f:=1) (by
    simpa only [pow_one,Nat.card_eq_fintype_card] using hF)
  let _ : IsSimpleGroup D := h.simple
  let _ : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let _ : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  have hns : ¬ Group.IsSolvable PSL(3,F) := Group.IsPerfect.not_isSolvable _
  apply false_of_component_square h ha e
  intro P hP β hβ hstable
  obtain ⟨α,hcompat,hα,hform⟩ :=
    Matrix.PSL3.ThreeWeightLift.exists_two_power_lift F hns hq ho hF β hβ
  exact Representation.ThreeWeightSquare.central_quotient_square h.large hpq
    Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective
    (Matrix.PSL3.projection F) (Matrix.PSL3.projection_surjective F)
    (by rw [Matrix.PSL3.projection_ker])
    (Matrix.PSL3.ThreeWeightLift.projection_kernel_card_ne_zero F)
    P hP α β hcompat hα hstable hform
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
