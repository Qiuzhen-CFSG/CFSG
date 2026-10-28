module

public import Theory.Representation.FrobeniusFixedDescent.FixedBasis
public import Theory.Representation.EndFieldFrobenius
public import Theory.Representation.CoefficientDescent
public import Theory.Representation.InjectiveDescent

/-!
# Descent of Frobenius-invariant representations to the prime field

A finite-dimensional representation over an algebraic closure of GF(p)
which is equivalent to its coefficient Frobenius twist has a model over
GF(p), with an actual intertwining equivalence after coefficient extension.
No finiteness of the acting monoid or irreducibility is needed for descent;
irreducibility descends when present.

Compose coefficient Frobenius with the inverse of the given intertwiner.
The resulting Frobenius-semilinear map commutes with the representation.
Its fixed basis is constructed by finite orbits and polynomial orbit sums.
In this basis every action entry is Frobenius-fixed, hence belongs to the
prime field. Injective matrix descent produces the representation laws,
and the basis change gives the asserted equivalence. Tensor-product scalar
extension then transfers irreducibility back to the prime field.

Source application: Gorenstein, *Finite Groups*, §16.6, p.482, the
prime-field realization in Janko's characteristic-eleven argument.
-/

public section

open Module
namespace Representation.FrobeniusFixedDescent

variable {p : ℕ} [Fact p.Prime] {K V ι G : Type*} [Field K] [CharP K p]
  [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] [Monoid G]

omit [Fact p.Prime] [CharP K p] [DecidableEq ι] in
/-- Fixed vectors have Frobenius-fixed coordinates in a fixed basis. -/
theorem coordinate_pow_eq_of_fixed (T : V →+ V)
    (hsemi : ∀ (a : K) (v : V), T (a • v) = a ^ p • T v)
    (b : Basis ι K V) (hb : ∀ i, T (b i) = b i) {v : V} (hv : T v = v) (i : ι) :
    b.equivFun v i ^ p = b.equivFun v i := by
  have hact (c : ι → K) :
      T (b.equivFun.symm c) = b.equivFun.symm (fun j => c j ^ p) := by
    simp only [b.equivFun_symm_apply, map_sum, hsemi, hb]
  have h := congrArg (fun w => b.equivFun w i) (hact (b.equivFun v))
  simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, hv] using h.symm

/-- A commuting injective Frobenius-semilinear map constructs a prime-field model. -/
theorem exists_model_of_commuting_semilinear
    [IsAlgClosed K] [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    (ρ : Representation K G V) (b₀ : Basis ι K V)
    (T : V →+ V) (hT : Function.Injective T)
    (hsemi : ∀ (a : K) (v : V), T (a • v) = a ^ p • T v)
    (hcomm : ∀ g v, T (ρ g v) = ρ g (T v)) :
    ∃ σ : Representation (ZMod p) G (ι → ZMod p),
      Nonempty ((mapCoefficients (algebraMap (ZMod p) K) σ).Equiv ρ) := by
  classical
  obtain ⟨b, hb⟩ := exists_fixed_basis T hsemi b₀ hT
  let τ : Representation K G (ι → K) := b.equivFun.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (g : G) (i j : ι) :
      LinearMap.toMatrix' (τ g) i j = b.equivFun (ρ g (b j)) i := by
    change b.equivFun (ρ g (b.equivFun.symm (Pi.single j 1))) i = _
    have hbj : b.equivFun.symm (Pi.single j 1) = b j := by
      apply b.equivFun.injective
      simp
    rw [hbj]
  obtain ⟨σ, hσ⟩ := exists_mapCoefficients_eq_of_entries
    (algebraMap (ZMod p) K) (algebraMap (ZMod p) K).injective τ (by
      intro g i j
      rw [hτ]
      have hpow := coordinate_pow_eq_of_fixed T hsemi b hb
        (show T (ρ g (b j)) = ρ g (b j) by rw [hcomm, hb]) i
      have hbot := (Subfield.mem_bot_iff_pow_eq_self K p).mpr hpow
      obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p K).mp hbot
      exact ⟨(n : ZMod p), by simpa only [map_intCast] using hn⟩)
  refine ⟨σ, ?_⟩
  rw [hσ]
  refine ⟨Representation.Equiv.mk b.equivFun.symm (fun g => ?_)⟩
  apply LinearMap.ext
  intro v
  change b.equivFun.symm (b.equivFun (ρ g (b.equivFun.symm v))) = _
  exact b.equivFun.symm_apply_apply _

end Representation.FrobeniusFixedDescent

namespace Representation
open FrobeniusFixedDescent
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable (p : ℕ) [Fact p.Prime] {K V ι G : Type*} [Field K] [CharP K p]
  [IsAlgClosed K] [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype ι] [DecidableEq ι] [Monoid G]

/-- Frobenius invariance up to equivalence constructs a model over GF(p). -/
theorem exists_primeField_model_of_frobenius_equiv
    (ρ : Representation K G V) (b : Basis ι K V)
    (hfrob : Nonempty (ρ.Equiv (frobeniusConjugate p 1 ρ))) :
    ∃ σ : Representation (ZMod p) G (ι → ZMod p),
      Nonempty ((mapCoefficients (algebraMap (ZMod p) K) σ).Equiv ρ) := by
  classical
  obtain ⟨e⟩ := hfrob
  let F := frobeniusSemilinearEquiv (K := K) (W := V) p 1
  let T : V →+ V := e.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp
    F.toAddEquiv.toAddMonoidHom
  have hT : Function.Injective T := e.symm.toLinearEquiv.injective.comp F.injective
  have hsemi (a : K) (v : V) : T (a • v) = a ^ p • T v := by
    change e.symm.toLinearEquiv (F (a • v)) = a ^ p • e.symm.toLinearEquiv (F v)
    rw [F.map_smulₛₗ, LinearEquiv.map_smul]
    change iterateFrobeniusEquiv K p 1 a • _ = _
    rw [iterateFrobeniusEquiv_one_apply]
  have hcomm (g : G) (v : V) : T (ρ g v) = ρ g (T v) := by
    have hF : F (ρ g v) = frobeniusConjugate p 1 ρ g (F v) := by
      simp only [frobeniusConjugate, semilinearConjugate_apply]
      exact congrArg F (congrArg (ρ g) (F.symm_apply_apply v).symm)
    change e.symm.toLinearEquiv (F (ρ g v)) = ρ g (e.symm.toLinearEquiv (F v))
    rw [hF]
    exact LinearMap.congr_fun (e.symm.isIntertwining' g) (F v)
  exact exists_model_of_commuting_semilinear ρ b T hT hsemi hcomm

/-- An irreducible Frobenius-invariant representation has an irreducible prime-field model. -/
theorem exists_irreducible_primeField_model_of_frobenius_equiv
    (ρ : Representation K G V) (b : Basis ι K V) (hρ : IsIrreducible ρ)
    (hfrob : Nonempty (ρ.Equiv (frobeniusConjugate p 1 ρ))) :
    ∃ σ : Representation (ZMod p) G (ι → ZMod p), IsIrreducible σ ∧
      Nonempty ((mapCoefficients (algebraMap (ZMod p) K) σ).Equiv ρ) := by
  obtain ⟨σ, ⟨e⟩⟩ := exists_primeField_model_of_frobenius_equiv p ρ b hfrob
  let er : mapCoefficients (algebraMap (ZMod p) K) σ ≃ₗ ρ :=
    { toLinearEquiv := e.toLinearEquiv
      isIntertwining' := e.isIntertwining' }
  let : IsIrreducible (extendScalars K σ) :=
    (extendScalarsMapCoefficientsEquiv (E := K) σ).irreducible_of_euqiv
      (er.irreducible_of_euqiv hρ)
  exact ⟨σ, irreducible_of_extendScalars K σ, ⟨e⟩⟩

end Representation
