module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Algebra.ZMod

/-!
# Solvability of finite-field automorphisms

Every automorphism fixes the prime field. Embedding the ring automorphism
group in the cyclic Galois group over that prime field proves cyclicity,
and hence solvability. This is the field factor used in the PSL₂ case of
GLS3, Theorem 2.5.12(d), `refs/KGroup/GLS3/chapter2.tex`.

The prime-field argument is extracted from
`Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Field`,
so the PSL₂ calculation has no unitary or campaign dependency.
-/

namespace Theory.PSL2.OuterSolvable

/-- Ring automorphisms of a finite field form a cyclic group. -/
public theorem finiteFieldAut_isCyclic {K : Type*} [Field K] [Finite K] :
    IsCyclic (K ≃+* K) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  let := hp
  let : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let := ZMod.algebra K p
  let f : (K ≃+* K) →* (K ≃ₐ[ZMod p] K) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (fun z => by
        exact congrArg (fun f : ZMod p →+* K => f z)
          (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod p) K))
            (algebraMap (ZMod p) K)))
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }
  exact isCyclic_of_injective f (fun σ τ h => RingEquiv.ext fun x =>
    congrArg (fun f : K ≃ₐ[ZMod p] K => f x) h)

/-- The field factor in the outer automorphism calculation is solvable. -/
public theorem finiteFieldAut_isSolvable {K : Type*} [Field K] [Finite K] :
    Group.IsSolvable (K ≃+* K) := by
  let : IsCyclic (K ≃+* K) := finiteFieldAut_isCyclic
  let := IsCyclic.commGroup (α := K ≃+* K)
  infer_instance

end Theory.PSL2.OuterSolvable
