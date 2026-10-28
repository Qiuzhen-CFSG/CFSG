module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Lifts
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting.UnitaryPlane
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting.BasisReduction
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting.Restriction
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.InvolutionTransport.LinearEigenbasis
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.InvolutionTransport.UnitaryEigenbasis

/-!
# Reduction of anticommuting lift centralizers to a unitary plane

The full unitary plane over Nine has order 96. An injective restriction of
the ordinary pair centralizer to that plane therefore excludes nine from
its order. Anticommutation already implies trace zero, and the scalar
rescaling and determinant calculation connect the standard linear and
unitary eigenbasis contracts to this restriction.

The final theorem supplies both eigenbasis existence results and the
faithful restriction, proving the bound from projective-square and
anticommutation hypotheses alone. No separate trace hypothesis is needed.
The square of the second lift is retained in the public interface for
the projective four-group application, although the proof does not use it.

Source obligation: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4, repeated
as Theorem 0.1.1(4) on p.482 of `refs/quasithin.pdf`. The ordinary SU
centralizer here feeds the separate scalar-quotient transfer; all matrices
and forms retain the GLS3 chapter 2 unitary conventions.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal

namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer

open Anticommuting

/-- An actual embedding in the full unitary plane group excludes nine. -/
theorem centralizer_not_nine_dvd_of_unitary_plane_embedding
    (a b : SU)
    (f : Subgroup.centralizer ({a, b} : Set SU) →* FullUnitaryTwo)
    (hf : Function.Injective f) :
    ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer ({a, b} : Set SU)) := by
  intro h
  exact fullUnitaryTwo_not_nine_dvd (h.trans (Subgroup.card_dvd_of_injective f hf))

/-- Conditional assembly with explicit linear eigenbasis, Hermitian normalization
and faithful plane restriction inputs. -/
theorem anticommuting_lift_centralizer_not_nine_dvd_of_geometric_inputs
    (hlinear : ∀ M : GL (Fin 4) FiniteField.Nine, M ^ 2 = 1 → Matrix.trace M.val = 0 →
      ∃ P : GL (Fin 4) FiniteField.Nine,
        P * standardInvolutionGL * P⁻¹ = M)
    (hnormalize : ∀ (A : SU) (P : GL (Fin 4) FiniteField.Nine),
      P * standardInvolutionGL * P⁻¹ = A.val →
        ∃ C : (form 4).unitarySubgroup,
          C.val * standardInvolutionGL * C.val⁻¹ = A.val)
    (hrestrict : ∀ (a b : SU) (u : FiniteField.Nineˣ) (C : (form 4).unitarySubgroup),
      a.val.val * b.val.val = -(b.val.val * a.val.val) →
      C.val * standardInvolutionGL * C.val⁻¹ = GeneralLinearGroup.scalar (Fin 4) u * a.val →
      ∃ f : Subgroup.centralizer ({a, b} : Set SU) →* FullUnitaryTwo, Function.Injective f)
    (a b : SU) (ha : (project 4 a) ^ 2 = 1)
    (hab : a.val.val * b.val.val = -(b.val.val * a.val.val)) :
    ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer ({a, b} : Set SU)) := by
  obtain ⟨u, C, _, hC⟩ :=
    exists_scaled_unitary_conjugator_of_eigenbasis_inputs hlinear hnormalize a b ha hab
  obtain ⟨f, hf⟩ := hrestrict a b u C hab hC
  exact centralizer_not_nine_dvd_of_unitary_plane_embedding a b f hf

/-- The ordinary common centralizer of anticommuting special-unitary lifts of
projective involutions has order indivisible by nine. Anticommutation supplies
trace zero, so no additional trace hypothesis is required. -/
theorem anticommuting_lift_centralizer_not_nine_dvd
    (a b : SU) (ha : (project 4 a) ^ 2 = 1) (_hb : (project 4 b) ^ 2 = 1)
    (hab : a.val.val * b.val.val = -(b.val.val * a.val.val)) :
    ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer ({a, b} : Set SU)) := by
  exact anticommuting_lift_centralizer_not_nine_dvd_of_geometric_inputs
    exists_linear_conjugator_of_trace_zero exists_unitary_conjugator_of_linear
    exists_unitary_plane_embedding_of_conjugator a b ha hab

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer
