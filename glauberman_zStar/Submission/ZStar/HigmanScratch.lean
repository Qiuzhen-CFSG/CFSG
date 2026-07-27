import Submission.ZStar.NagaoRelativeTrace
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Rep.Iso

noncomputable section

open scoped BigOperators
open Module

namespace Submission.ZStar
namespace HigmanScratch

universe u v w

attribute [local instance] Fintype.ofFinite

/-! A Higman-style criterion in a form tailored to the later order-two trace
calculation.  We first prove it for an arbitrary finite group and an
`R[P]`-module which is free over `R`. -/

theorem projective_of_relative_trace_id
    {R P M : Type*} [CommRing R] [Group P] [Fintype P]
    [AddCommGroup M] [Module R M]
    [Module (MonoidAlgebra R P) M]
    [IsScalarTower R (MonoidAlgebra R P) M]
    [Module.Free R M]
    (a : M →ₗ[R] M)
    (htrace : ∑ g : P, (a.conjugate g) = LinearMap.id) :
    Module.Projective (MonoidAlgebra R P) M := by
  let b : Basis (Module.Free.ChooseBasisIndex R M) R M :=
    Module.Free.chooseBasis R M
  let α := Module.Free.ChooseBasisIndex R M
  let W := Representation.free R P α
  let oneCoeff : R →ₗ[R] MonoidAlgebra R P :=
    Finsupp.lsingle (1 : P)
  let equivW := Representation.finsuppLEquivFreeAsModule R P α
  let qF : (α →₀ MonoidAlgebra R P) →ₗ[MonoidAlgebra R P] M :=
    Finsupp.linearCombination (MonoidAlgebra R P) (fun i : α => b i)
  let q : W.asModule →ₗ[MonoidAlgebra R P] M :=
    qF.comp equivW.symm.toLinearMap
  let s0F : M →ₗ[R] α →₀ MonoidAlgebra R P :=
    (Finsupp.mapRange.linearMap oneCoeff).comp b.repr.toLinearMap
  let s0 : M →ₗ[R] W.asModule :=
    (equivW.toLinearMap.restrictScalars R).comp s0F
  let π : M →ₗ[R] W.asModule := s0.comp a
  let s : M →ₗ[MonoidAlgebra R P] W.asModule :=
    LinearMap.sumOfConjugatesEquivariant P π
  have hqs0 : (q.restrictScalars R).comp s0 = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change qF (s0F x) = x
    simp only [qF, s0F, LinearMap.comp_apply, Finsupp.linearCombination_apply]
    rw [Finsupp.mapRange.linearMap_apply]
    rw [Finsupp.sum_mapRange_index (fun _ => by simp)]
    calc
      (b.repr x).sum (fun i r => oneCoeff r • b i) =
          (b.repr x).sum (fun i r => r • b i) := by
            apply Finsupp.sum_congr
            intro i hi
            have honeCoeff (r : R) :
                oneCoeff r = algebraMap R (MonoidAlgebra R P) r := by
              ext g
              simp [oneCoeff, MonoidAlgebra.coe_algebraMap]
            rw [honeCoeff, IsScalarTower.algebraMap_smul]
      _ = (Finsupp.linearCombination R (fun i : α => b i)) (b.repr x) := rfl
      _ = x := by
        rw [← b.repr_symm_apply, b.repr.symm_apply_apply]
  have hqs : q.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.sumOfConjugatesEquivariant_apply]
    -- Push the retraction through the conjugate sum.  The resulting sum is
    -- exactly the assumed relative trace of `a`.
    simp only [LinearMap.conjugate_apply]
    calc
      q (∑ g : P,
          MonoidAlgebra.single g⁻¹ (1 : R) •
            π (MonoidAlgebra.single g (1 : R) • x)) =
          ∑ g : P, MonoidAlgebra.single g⁻¹ (1 : R) •
            a (MonoidAlgebra.single g (1 : R) • x) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro g hg
              rw [map_smul]
              change MonoidAlgebra.single g⁻¹ (1 : R) •
                  q (s0 (a (MonoidAlgebra.single g (1 : R) • x))) = _
              have h := LinearMap.congr_fun hqs0
                (a (MonoidAlgebra.single g (1 : R) • x))
              simpa [LinearMap.comp_apply] using
                congrArg (fun y : M =>
                  MonoidAlgebra.single g⁻¹ (1 : R) • y) h
      _ = (∑ g : P, a.conjugate g) x := by
            simp only [LinearMap.sum_apply, LinearMap.conjugate_apply]
      _ = x := by rw [htrace]; rfl
  letI : Module.Free (MonoidAlgebra R P) W.asModule :=
    Representation.free_asModule_free R P α
  letI : Module.Projective (MonoidAlgebra R P) W.asModule :=
    Module.Projective.of_free
  exact Module.Projective.of_split s q hqs

end HigmanScratch
end Submission.ZStar
