module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.Reduction
public import Theory.Representation.SU3.CubicDegree.SchurOuter.Models
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable.WordSelection
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable.Labels
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable.Displacement

/-!
# Assembly of the outer unitary word selection

The literal scalar-extension formula and the perfect-image rank bound turn
the displacement estimate into e*dim ≤ 12(s+1) ≤ 18s. Label symmetry removes
the natural factors; the twisted period counts then select one adjoint
factor and the exact Schur degree. An actual tensor-unit intertwiner gives
the published adjoint model.

The final theorem discharges label symmetry and displacement using the
literal outer involution, including its passage through the perfect action
image and genuine central quotient. Only the earlier-source catalogue,
actual word witness, and twisted period counts remain explicit. It supplies
the graph-stable selection contract used by the Schur-linear outer branch;
the parent retains the adjoint fixed-space calculation and outer exclusion.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32, and §3.5.
-/

public section
open BenderSuzuki.MatrixGroups Representation Representation.FrobeniusTensor
open Representation.SL3.BinaryDefiningFactors Representation.BinaryOffender
open Representation.SU3.CubicDegree.SchurOuter
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]
  (hk : σ.ker ≤ Subgroup.center J.specialSubgroup)

include hs hcard hconj hk

/-- Assemble the two outer-word steps with the genuine word witness and
period counts. `graphStableReduction_of_catalogue` below discharges both
outer-word premises. -/
theorem graphStableReduction_of_word_steps
    (hmodel : ∃ (ι : F →+* Closure σ) (w : List Factor), w.length = s ∧
      Nonempty ((absoluteRep σ).Equiv (MinimalDegree.word J ι w)))
    (hperiod : ∀ (ι : F →+* Closure σ) (w : List Factor), w.length = s →
      Nonempty ((absoluteRep σ).Equiv (MinimalDegree.word J ι w)) →
      MinimalDegree.PeriodCounts s (schurDegree 2 σ) w)
    (hlabels : OuterLabelSymmetry J σ s)
    (hdisplacement : OuterWordDisplacement J σ s) :
    GraphStableReduction J σ s := by
  intro A hA _ hc hl t ht ho
  obtain ⟨ι, w, hw, he⟩ := hmodel
  have ht2 : t ^ 2 = 1 := by
    let : IsElementaryAbelian 2 A := hA.2
    exact elemPow_eq_one_of_isElementaryAbelian t ht
  have hn := hlabels ι w hw he t ht2 (hl t ht) ho
  have hd := hdisplacement ι w hw he hn A hA hl t ht ho
  have hscaled : schurDegree 2 σ * wordDegree w ≤
      6 * fixedCodim (normalizerRepresentation σ) A := by
    calc
      schurDegree 2 σ * wordDegree w ≤
          schurDegree 2 σ * (6 * Module.finrank (Closure σ)
            (AbsoluteSpace σ ⧸ (absoluteActorRepresentation σ A hl).invariants)) :=
        Nat.mul_le_mul_left _ hd
      _ = 6 * fixedCodim (normalizerRepresentation σ) A := by
        rw [fixedCodim_eq_schur_mul σ A hl]
        change _ = 6 * (schurDegree 2 σ * _)
        ring
  have hr := Representation.SU3.CubicDegree.elementary_rank_le
    J hs hcard hconj σ inferInstance hk A hA
  apply adjointSchurModel_of_word_bound J σ ι w he (hperiod ι w hw he) hn
  omega

/-- Graph-stable selection from the earlier-source word catalogue and twisted
period counts. A literal outer Schur-linear elementary actor satisfying the
cubic codimension bound forces Schur degree `s` and an actual equivalence
with the published adjoint representation, including at `s = 2`.

The catalogue supplies irreducibility, uniqueness, and an actual word model;
the period premise concerns every such model. Neither graph stability nor
an adjoint model or displacement bound is assumed. -/
theorem graphStableReduction_of_catalogue
    (hirr : ∀ (ι : F →+* Closure σ) (w : List Factor), w.length = s →
      IsIrreducible (MinimalDegree.word J ι w))
    (hunique : ∀ (ι : F →+* Closure σ) (u v : List Factor),
      u.length = s → v.length = s →
      Nonempty ((MinimalDegree.word J ι u).Equiv (MinimalDegree.word J ι v)) → u = v)
    (hmodel : ∃ (ι : F →+* Closure σ) (w : List Factor), w.length = s ∧
      Nonempty ((absoluteRep σ).Equiv (MinimalDegree.word J ι w)))
    (hperiod : ∀ (ι : F →+* Closure σ) (w : List Factor), w.length = s →
      Nonempty ((absoluteRep σ).Equiv (MinimalDegree.word J ι w)) →
      MinimalDegree.PeriodCounts s (schurDegree 2 σ) w) :
    GraphStableReduction J σ s :=
  graphStableReduction_of_word_steps J hs hcard hconj σ hk hmodel hperiod
    (outerLabelSymmetry_of_catalogue J hs hcard hconj σ hk hirr hunique)
    (outerWordDisplacement J σ hs hcard hconj hk)

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable
