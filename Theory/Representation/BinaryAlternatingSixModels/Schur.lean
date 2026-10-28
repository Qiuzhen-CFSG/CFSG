module

public import Theory.Representation.BinaryAlternatingSixModels.TensorSchurDegree
public import Theory.Representation.BinaryPermutation.FiveTensorNormalizer
public import Theory.Representation.BinaryPermutation.SixFiveRestriction

/-!
# Schur-degree inputs for binary A₆ recognition

Conjugation and actor relabelling give linear equivalences between the actual
intertwining endomorphism spaces. The natural six-letter module restricts,
through zero extension and the natural quotient, to the five-letter augmentation
core. Its scalar commutant therefore gives Schur degree one. The imported tensor
bound is on the actual group-algebra endomorphism field; the same transport
identifies it with the intertwining space used in the source application.

Source: Aschbacher--Smith G.5.1 and the homogeneous multiplicity argument in
G.11.7--8, printed pp.342,366,368--369.
-/

public noncomputable section

open Representation
namespace BinaryAlternatingSix.Schur
variable {k D E V W : Type*} [Field k] [Group D] [Group E]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Conjugating by an actual representation equivalence identifies the
intertwining endomorphism spaces over the original coefficient field. -/
def endEquiv {ρ : Representation k D V} {σ : Representation k D W}
    (e : ρ.Equiv σ) : IntertwiningMap ρ ρ ≃ₗ[k] IntertwiningMap σ σ where
  toFun f := e.toIntertwiningMap.comp (f.comp e.symm.toIntertwiningMap)
  invFun f := e.symm.toIntertwiningMap.comp (f.comp e.toIntertwiningMap)
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

/-- Relabelling every actor by a group isomorphism leaves the actual
intertwining endomorphism space unchanged. -/
def endCompEquiv (ρ : Representation k D V) (e : E ≃* D) :
    IntertwiningMap (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) ≃ₗ[k]
      IntertwiningMap ρ ρ where
  toFun f := ⟨f.toLinearMap, fun g => by simpa using f.isIntertwining' (e.symm g)⟩
  invFun f := ⟨f.toLinearMap, fun g => f.isIntertwining' (e g)⟩
  left_inv f := by ext v; rfl
  right_inv f := by ext v; rfl
  map_add' f g := by ext v; rfl
  map_smul' c f := by ext v; rfl

end BinaryAlternatingSix.Schur

open Representation
namespace BinaryAlternatingSix.Schur
open BinaryPermutation
open BinaryPermutation.SixFiveRestriction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-- Restriction to the literal five-letter subgroup makes every endomorphism
commuting with the six-letter natural action a binary scalar. -/
theorem natural_commuting_scalar
    (f : natural (Fin 6) →ₗ[ZMod 2] natural (Fin 6))
    (hf : ∀ (g : alternatingGroup (Fin 6)) v,
      f (alternatingNaturalRepresentation (Fin 6) g v) =
        alternatingNaturalRepresentation (Fin 6) g (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  let e := naturalSixEquivCoreFive
  have he (g : FivePair.five) (v : natural (Fin 6)) :=
    naturalSixEquivCoreFive_equivariant g v
  let F := e.toLinearMap.comp (f.comp e.symm.toLinearMap)
  obtain ⟨c,hc⟩ := FiveTensorNormalizer.core_commuting_scalar F (by
    intro g v
    let q := FivePair.fiveEquiv.symm g
    have hq : FivePair.fiveEquiv q = g := FivePair.fiveEquiv.apply_symm_apply g
    have hv := he q (e.symm v)
    change e (naturalRepresentation (Fin 6) q.val (e.symm v)) =
      alternatingCoreRepresentation (Fin 5) (FivePair.fiveEquiv q) (e (e.symm v)) at hv
    rw [hq,e.apply_symm_apply] at hv
    change e (f (e.symm _)) = _
    rw [← hv,e.symm_apply_apply]
    change e (f (alternatingNaturalRepresentation (Fin 6) ⟨q.val,q.property.2⟩ (e.symm v))) = _
    rw [hf]
    change e (naturalRepresentation (Fin 6) q.val (f (e.symm v))) =
      alternatingCoreRepresentation (Fin 5) g (e (f (e.symm v)))
    have h := he q (f (e.symm v))
    change e (naturalRepresentation (Fin 6) q.val (f (e.symm v))) =
      alternatingCoreRepresentation (Fin 5) (FivePair.fiveEquiv q) (e (f (e.symm v))) at h
    rw [hq] at h
    exact h)
  refine ⟨c,fun v => e.injective ?_⟩
  simpa only [F,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    e.symm_apply_apply,map_smul] using hc (e v)

/-- The natural binary A₆ module has Schur degree one. -/
theorem natural_end_finrank_one : Module.finrank (ZMod 2)
    (IntertwiningMap (alternatingNaturalRepresentation (Fin 6))
      (alternatingNaturalRepresentation (Fin 6))) = 1 := by
  let ρ := alternatingNaturalRepresentation (Fin 6)
  let : Nontrivial (natural (Fin 6)) := Module.nontrivial_of_finrank_pos (by
    rw [finrank_natural_even (Fin 6) (by decide)]
    decide)
  have hn : IntertwiningMap.id ρ ≠ 0 := by
    obtain ⟨v,hv⟩ := exists_ne (0 : natural (Fin 6))
    intro hz
    exact hv (congrArg (fun f : IntertwiningMap ρ ρ => f v) hz)
  apply (finrank_eq_one_iff_of_nonzero' (IntertwiningMap.id ρ) hn).mpr
  intro f
  obtain ⟨c,hc⟩ := natural_commuting_scalar f.toLinearMap f.isIntertwining
  refine ⟨c, IntertwiningMap.ext (LinearMap.ext fun v => ?_)⟩
  exact (hc v).symm

end BinaryAlternatingSix.Schur
