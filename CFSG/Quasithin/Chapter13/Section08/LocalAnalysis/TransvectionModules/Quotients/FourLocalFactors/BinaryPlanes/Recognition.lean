module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.BinaryPlanes.Generating
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.BinaryPlanes.Natural
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.PGroupCore

/-!
# Generating binary planes with a specified S₃ quotient

Full action-difference generation makes a binary plane irreducible. The
normal two-core therefore acts trivially. Descend through the actual quotient
and the supplied isomorphism e, identify this S₃ action with the three-point
core, and inflate through the same e. Faithfulness of the core gives equality
of the original action kernel and the two-core.

This is the independent representation contract used for the local planes
in Aschbacher–Smith, combined manuscript (1 March 2004), proof of 13.8.6(4),
printed p.948. The source assembly supplies the dimensions, commutator
identities and actual local quotient isomorphisms.
-/

public section

open Representation Module Subgroup
namespace Representation.BinaryPlaneRecognition

private theorem three_core_faithful : Function.Injective (BinaryPermutation.coreRepresentation (Fin 3)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro g hg
  change g = 1
  have hfinite : ∀ g : Equiv.Perm (Fin 3),
      (∀ v : Fin 3 → ZMod 2, (∑ i, v i) = 0 → ∀ i, v (g.symm i) = v i) → g = 1 := by
    decide +kernel
  apply hfinite g
  intro v hv i
  have he := LinearMap.congr_fun (MonoidHom.mem_ker.mp hg)
    (⟨v, hv⟩ : BinaryPermutation.core (Fin 3))
  exact congrArg (fun w : BinaryPermutation.core (Fin 3) => w.val i) he

variable {P X : Type*} [Group P] [Finite P] [AddCommGroup X] [Module (ZMod 2) X]

/-- Recognition retains the given quotient isomorphism e in the natural
representation, and derives both irreducibility and the exact kernel. -/
theorem recognize (ρ : Representation (ZMod 2) P X)
    (hd : Module.finrank (ZMod 2) X = 2) (hgen : Coinvariants.ker ρ = ⊤)
    (e : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) :
    ρ.IsIrreducible ∧ ρ.ker = pCore 2 P ∧
      Nonempty (ρ.Equiv ((BinaryPermutation.coreRepresentation (Fin 3)).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))))) := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := X) (by omega)
  have hirr := irreducible_of_generating_plane ρ hd hgen
  let : ρ.IsIrreducible := hirr
  have hcore : pCore 2 P ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  let σ : Representation (ZMod 2) (Equiv.Perm (Fin 3)) X := (quotientOfLEKer ρ (pCore 2 P) hcore).comp e.symm.toMonoidHom
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have happ (p : P) : σ (π p) = ρ p := by
    change quotientOfLEKer ρ (pCore 2 P) hcore (e.symm (e (QuotientGroup.mk' _ p))) = _
    rw [e.symm_apply_apply]
    rfl
  have hcomp : σ.comp π = ρ := MonoidHom.ext happ
  have hσ : σ.IsIrreducible := by
    apply (irreducible_comp_surjective_iff π hπ σ).mp
    rw [hcomp]
    exact hirr
  let := hσ
  obtain ⟨E⟩ := equiv_three_core_of_irreducible σ hd
  let F : ρ.Equiv ((BinaryPermutation.coreRepresentation (Fin 3)).comp π) :=
    Representation.Equiv.mk E.toLinearEquiv (fun p => by
      have he := E.isIntertwining' (π p)
      simpa only [happ, MonoidHom.comp_apply] using he)
  refine ⟨hirr, le_antisymm ?_ hcore, ⟨F⟩⟩
  intro g hg
  apply (QuotientGroup.eq_one_iff _).mp
  apply e.injective
  rw [map_one]
  apply three_core_faithful
  rw [map_one]
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := F.toLinearEquiv.surjective v
  have he := IntertwiningMap.isIntertwining _ _ F.toIntertwiningMap g w
  rw [MonoidHom.mem_ker.mp hg] at he
  exact he.symm

/-- An equivariant linear equivalence for the same marked quotient map. -/
noncomputable def naturalEquiv (ρ : Representation (ZMod 2) P X)
    (hd : Module.finrank (ZMod 2) X = 2) (hgen : Coinvariants.ker ρ = ⊤)
    (e : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) :
    ρ.Equiv ((BinaryPermutation.coreRepresentation (Fin 3)).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P)))) :=
  Classical.choice (recognize ρ hd hgen e).2.2

end Representation.BinaryPlaneRecognition
