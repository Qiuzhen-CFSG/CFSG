module

public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.BinaryLieModels
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.LinearRank
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.SymplecticRank
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.UnitaryRank
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrthogonalRank
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.ExceptionalRank

/-!
# The complete known Lie-type branch of Theorem D

For a finite simple QTKE group with nonempty actual faithful local family,
every characteristic-two Lie model over `2^n`, `n > 1`, gives the precise
rank-two output at the same exponent. The input includes all fifteen Lie
families and places no upper rank bound or unitary-five restriction.

The direct root-normalizer theorems exclude higher ranks. The rank-one
Borel theorem excludes the linear, unitary, symplectic and minus-orthogonal
rank-one models and the Suzuki family. Actual orthogonal equivalences
identify the surviving odd and minus models with symplectic and unitary
models. The unitary-five theorem forces `n = 2`. The remaining G₂,
genuine triality and general Ree F₄ witnesses already give allowed outputs.

The final corollary supplies the full Lie-family exclusion in Hypothesis
13.3.1(2) when no conclusion of Theorem D holds. The K-class remains
arbitrary, so in particular this applies to the full known-simple class.
All rank, parameter and model premises of the family proofs are discharged
from the original input; no smaller-section induction premise is required.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Hypothesis 13.3.1(2), printed p.884, and
Theorem D/14.8.2(1), printed pp.1078–1079. The direct rank obstructions
implement the relevant Lie-family restrictions of A.2.18, printed p.40.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- The full characteristic-two Lie input gives the allowed rank-two model
at the original exponent, including the required U₅ restriction. -/
theorem rankTwoModel_of_binaryLieModel
    (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {n : ℕ} (hn : 1 < n) (hmodel : IsBinaryLieModelAt G n) :
    ClassificationModels.IsRankTwoModel G n := by
  cases hmodel with
  | linear d hd iso => exact rankTwoModel_of_psl h T hne hd hn iso
  | unitary d hd iso => exact rankTwoModel_of_psu h T hne hd hn iso
  | symplectic r hr iso => exact rankTwoModel_of_psp h T hne hr hn iso
  | orthogonalPlus r hr iso =>
      exact (not_pOmegaPlus_of_quasithin h.quasithin hr hn iso).elim
  | orthogonalOdd r hr iso =>
      exact rankTwoModel_of_psp h T hne hr hn (psp_of_pOmegaOdd hr (by omega) iso)
  | orthogonalMinus r hr iso => exact rankTwoModel_of_pOmegaMinus h T hne hr hn iso
  | g2 iso => exact .g2 (by omega) iso
  | suzuki m hm hnm iso =>
      exact (hne.ne_empty (localFamilies_eq_empty_of_suzuki h T iso).2).elim
  | triality iso => exact .triality (by omega) iso
  | reeF4 m hm hnm iso => exact .ree_f4 m hm hnm iso
  | f4 iso => exact (not_isF4_of_quasithin h.quasithin hn iso).elim
  | e6 iso => exact (not_isE6_of_quasithin h.quasithin hn iso).elim
  | e7 iso => exact (not_isE7_of_quasithin h.quasithin hn iso).elim
  | e8 iso => exact (not_isE8_of_quasithin h.quasithin hn iso).elim
  | twistedE6 iso => exact (not_isTwistedE6_of_quasithin h.quasithin hn iso).elim

/-- The known Lie-type branch of Theorem D, with the strict source exponent. -/
theorem theoremDModel_of_binaryLieModel
    (h : IsSimpleQTKE K G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    {n : ℕ} (hn : 1 < n) (hmodel : IsBinaryLieModelAt G n) :
    ClassificationModels.IsTheoremDModel G :=
  .rank_two n hn (rankTwoModel_of_binaryLieModel h T hne hn hmodel)

/-- If no conclusion of Theorem D holds, the source's full Lie-type exclusion
in Hypothesis 13.3.1(2) follows for the chosen faithful local subgroup. -/
theorem not_exists_binaryLieModel_of_not_theoremDModel
    (h : IsSimpleQTKE K G) (T : Sylow 2 G) {L : Subgroup G}
    (hL : L ∈ MainForward.faithfulLocalComponents T)
    (hnot : ¬ ClassificationModels.IsTheoremDModel G) :
    ¬ ∃ n : ℕ, 1 < n ∧ IsBinaryLieModelAt G n := by
  rintro ⟨n, hn, hmodel⟩
  exact hnot (theoremDModel_of_binaryLieModel h T ⟨L, hL⟩ hn hmodel)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
