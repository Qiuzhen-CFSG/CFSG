module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Theory.AlgebraicGroup.Jordan.Basic

universe u

/-! Simultaneous eigenspace decompositions for commuting semisimple right
translations. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- If every point of an algebraic group is semisimple and its point group is
commutative, every regular function is a finite sum of simultaneous
right-translation eigenvectors. -/
public theorem exists_rightTranslateOrbitSpan_commonEigen_decomposition
    (T : Variety k) [AlgebraicGroup T]
    (hcomm : IsMulCommutative (Variety.Point T))
    (hsemi : ∀ t : Variety.Point T, IsSemisimpleElement T t)
    (f : Variety.PolynomialFunction T) :
    ∃ v : (Variety.Point T → k) →₀ rightTranslateOrbitSpan T f,
      (∀ μ g, rightTranslationPullback T g
          ((v μ : rightTranslateOrbitSpan T f) :
            Variety.PolynomialFunction T) =
        μ g • ((v μ : rightTranslateOrbitSpan T f) :
          Variety.PolynomialFunction T)) ∧
      v.sum (fun _ w ↦ (w : Variety.PolynomialFunction T)) = f := by
  rw [isMulCommutative_iff] at hcomm
  let W := rightTranslateOrbitSpan T f
  have hW (g : Variety.Point T) :
      W ∈ Module.End.invtSubmodule (rightTranslationPullback T g) :=
    rightTranslateOrbitSpan_stable T f g
  let R (g : Variety.Point T) : Module.End k W :=
    (rightTranslationPullback T g).restrict (hW g)
  let : Module.Finite k W := inferInstance
  have hRcomm : Pairwise fun g h ↦ Commute (R g) (R h) := by
    intro g h _
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change rightTranslationPullback T g
        (rightTranslationPullback T h x.1) =
      rightTranslationPullback T h
        (rightTranslationPullback T g x.1)
    calc
      rightTranslationPullback T g
          (rightTranslationPullback T h x.1) =
          rightTranslationPullback T (g * h) x.1 :=
        LinearMap.congr_fun (rightTranslationPullback_mul T g h).symm x.1
      _ = rightTranslationPullback T (h * g) x.1 := by rw [hcomm g h]
      _ = rightTranslationPullback T h
          (rightTranslationPullback T g x.1) :=
        LinearMap.congr_fun (rightTranslationPullback_mul T h g) x.1
  have hRsemi (g : Variety.Point T) : (R g).IsFinitelySemisimple :=
    (hsemi g).restrict (hW g)
  have htop :
      ⨆ μ : Variety.Point T → k, ⨅ g, (R g).eigenspace (μ g) = ⊤ := by
    have hmax :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        R hRcomm (fun g ↦ Module.End.iSup_maxGenEigenspace_eq_top (R g))
    simpa only [(hRsemi _).maxGenEigenspace_eq_eigenspace] using hmax
  have hfmem : f ∈ W := by
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    exact rightMul_pullback_one T f
  let fw : W := ⟨f, hfmem⟩
  have hf : fw ∈ ⨆ μ : Variety.Point T → k,
      ⨅ g, (R g).eigenspace (μ g) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨v, hv, hsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun μ : Variety.Point T → k ↦
        ⨅ g, (R g).eigenspace (μ g)) fw).mp hf
  refine ⟨v, ?_, ?_⟩
  · intro μ g
    have hμg : v μ ∈ (R g).eigenspace (μ g) :=
      (Submodule.mem_iInf (fun g ↦ (R g).eigenspace (μ g))).mp (hv μ) g
    have hr := Module.End.mem_eigenspace_iff.mp hμg
    exact congrArg (fun w : W ↦ (w : Variety.PolynomialFunction T)) hr
  · calc
      v.sum (fun _ w ↦ (w : Variety.PolynomialFunction T)) =
          ((v.sum fun _ w ↦ w : W) : Variety.PolynomialFunction T) := by
            classical
            change (∑ μ ∈ v.support,
                ((v μ : W) : Variety.PolynomialFunction T)) =
              ((∑ μ ∈ v.support, v μ : W) : Variety.PolynomialFunction T)
            simp
      _ = f := congrArg (fun w : W ↦
        (w : Variety.PolynomialFunction T)) hsum

end Theory.AlgebraicGroup
