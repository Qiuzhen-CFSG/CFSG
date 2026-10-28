module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Binary
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Exceptional
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.ExceptionalEndpoints
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Linear
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Unitary
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Twisted
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Janko
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.MathieuOddCoverCases
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.HSOddCoverCase
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.J2OddCoverCase
/-!
# The full ordinary-component case split for A.3.6

Every classical, alternating, small-derived, triality and seven sporadic
source branches are discharged by their actual covering calculations. The
remaining calculations are the odd-primary center bounds for the
Ree and Held quotient models. The legacy input record also retains the
now-proved J₄ bound. These are not classification conclusions.
The A.3.6 assembly must discharge these inputs before it is unconditional.

Source: Aschbacher–Smith A.3.6 and I.1.3, printed pp.43–45, 407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u

/-- The three remaining odd-primary source calculations. These are
central-kernel statements on the actual listed quotient models. -/
structure RemainingOddCoverInputs : Prop where
  ree : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L]
    (m : ℕ), 1 ≤ m → IsReeF4At (L ⧸ center L) m → IsPGroup 2 (center L)
  held : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L],
    Nonempty (L ⧸ center L ≃* Held.He) → IsPGroup 2 (center L)
  janko_four : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L],
    Nonempty (L ⧸ center L ≃* Janko4.Model) → IsPGroup 2 (center L)

private theorem conclusion_of_center_two {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (hc : IsPGroup 2 (center L))
    (hmodel : ∀ _j : L ≃* L ⧸ center L, TheoremCModel L) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have hz : center L = ⊥ := by
    apply bot_unique
    rw [← hcore]
    exact le_sSup ⟨inferInstance, hc⟩
  let j : L ≃* L ⧸ center L := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  let : IsSimpleGroup L := j.isSimpleGroup
  exact simple_conclusion L hL (hmodel j)

/-- The entire ordinary-component catalogue of A.3.6. All classical,
small-derived, triality and remaining sporadic cases are proved above;
only the three displayed odd-primary covering calculations remain. -/
theorem ordinary_conclusion (hrem : RemainingOddCoverInputs.{u})
    {X : Type u} [Group X] [Finite X] (hcore : pCore 2 X = ⊥)
    (L : Subgroup X) (hL : IsComponent X L)
    (hmodel : TheoremCModel (L ⧸ center L)) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  have hc : pCore 2 L = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hL.1, hcore, MonoidHom.comap_bot]
    exact L.subtype.ker_eq_bot_iff.mpr L.subtype_injective
  cases hmodel with
  | alternating n hn he =>
    obtain ⟨e⟩ := he
    exact a36_alternating hcore L hL n hn e
  | linear_odd p r hp ho hr hs he =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
    by_cases h9 : p ^ r = 9
    · exact a36_psl2_nine hcore L hL F (hF.trans h9) e
    · exact RankOneCoverCases.a36_psl2_odd L hL hc p r hp ho hr hs h9 F hF e
  | three_odd p hp ho unitary he =>
    cases unitary
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
      exact a36_linear_odd_prime L hL p hp ho F hF e
    · obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := he
      exact a36_unitary_odd_prime L hL hc p hp ho F J hF hconj e
  | rank_one he =>
    cases he with
    | linear n hn he =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
      exact RankOneCoverCases.a36_psl2_even L hL hc n hn F hF e
    | unitary n hn he =>
      obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := he
      exact a36_unitary_even L hL hc n hn F J hF hconj e
    | suzuki m hm he => exact RankOneCoverCases.a36_suzuki L hL hc m hm he.some
  | rank_two he =>
    cases he with
    | linear n hn he =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
      exact a36_linear_even hcore L hL n hn F hF e
    | symplectic n hn he =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
      exact a36_symplectic_even L hL n hn F hF e
    | g2 n hn he =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
      exact a36_g2_even L hL hc n hn F hF e
    | triality n hn he => exact a36_triality L hL hc n hn he
    | ree m hm he =>
      apply conclusion_of_center_two L hL hc (hrem.ree L m hm he)
      intro j
      obtain ⟨d, ⟨e⟩⟩ := he
      exact .rank_two (.ree m hm ⟨d, ⟨j.trans e⟩⟩)
    | symplectic_derived he => exact a36_symplectic_derived hcore L hL he.some
    | g2_derived he => exact RankOneCoverCases.a36_binary_g2_derived L hL hc he.some
    | tits he => exact a36_tits L hL hc he.some
  | binary_linear n hn he =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
    rcases hn with rfl | rfl
    · exact a36_psl4_two hcore L hL F hF e
    · exact a36_psl5_two L hL hc F hF e
  | sporadic name hne he =>
    cases name with
    | m11 => exact MathieuOddCoverCases.a36_m11 L hL hc he.some
    | m12 => exact MathieuOddCoverCases.a36_m12 L hL hc he.some
    | m22 => exact ReadyCoverCases.a36_m22 L hL hc he.some
    | m23 => exact MathieuOddCoverCases.a36_m23 L hL hc he.some
    | m24 => exact a36_m24 L hL hc he.some
    | j2 => exact J2OddCoverCase.a36_j2 L hL hc he.some
    | hs => exact HSOddCoverCase.a36_hs L hL hc he.some
    | ru => exact a36_ru L hL hc he.some
    | j3 => exact (hne rfl).elim
    | he =>
      apply conclusion_of_center_two L hL hc (hrem.held L he)
      intro j
      exact .sporadic .he (by intro h; cases h) ⟨j.trans he.some⟩
    | j4 => exact a36_janko_four L hL hc he.some
  | janko_one he => exact ReadyCoverCases.a36_janko L hL hc he.some
end CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
