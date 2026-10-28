module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# A cyclic commutative algebra is its full endomorphism commutant

An endomorphism commuting with a commutative algebra is determined by its value
on a cyclic vector. Choose the algebra element with the same value there;
commutation extends equality to every vector. This controls all endomorphisms,
not merely a normalizer or a subgroup of known matrix units.

This elementary regular-module argument is the structural step in the literal
seed construction described in `IntrinsicAlgebra/Defs.lean`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra

section Cyclic

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Pointwise commutation on a cyclic commutative algebra determines an arbitrary
endomorphism. The cyclicity premise is surjectivity of evaluation at `v`. -/
theorem end_mem_of_commutes_of_cyclic (A : Subalgebra R (Module.End R M)) (v : M)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, Commute a b)
    (hcyclic : ∀ w : M, ∃ a ∈ A, a v = w)
    (f : Module.End R M) (hf : ∀ a ∈ A, Commute f a) : f ∈ A := by
  obtain ⟨a, ha, hav⟩ := hcyclic (f v)
  have hfa : f = a := by
    ext w
    obtain ⟨b, hb, rfl⟩ := hcyclic w
    calc
      f (b v) = b (f v) := LinearMap.congr_fun (hf b hb).eq v
      _ = b (a v) := by rw [hav]
      _ = a (b v) := (LinearMap.congr_fun (hcomm a ha b hb).eq v).symm
  exact hfa.symm ▸ ha

theorem end_commutes_iff_mem_of_cyclic (A : Subalgebra R (Module.End R M)) (v : M)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, Commute a b)
    (hcyclic : ∀ w : M, ∃ a ∈ A, a v = w) (f : Module.End R M) :
    (∀ a ∈ A, Commute f a) ↔ f ∈ A :=
  ⟨end_mem_of_commutes_of_cyclic A v hcomm hcyclic f, fun hf => hcomm f hf⟩

/-- It suffices to commute with the generating operators, once their generated
algebra is commutative and the same cyclicity certificate is known. -/
theorem end_mem_adjoin_of_commutes_of_cyclic (S : Set (Module.End R M)) (v : M)
    (hcomm : ∀ a ∈ Algebra.adjoin R S, ∀ b ∈ Algebra.adjoin R S, Commute a b)
    (hcyclic : ∀ w : M, ∃ a ∈ Algebra.adjoin R S, a v = w)
    (f : Module.End R M) (hf : ∀ a ∈ S, Commute f a) :
    f ∈ Algebra.adjoin R S :=
  end_mem_of_commutes_of_cyclic (Algebra.adjoin R S) v hcomm hcyclic f
    (fun _ ha => Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha hf)

end Cyclic

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
