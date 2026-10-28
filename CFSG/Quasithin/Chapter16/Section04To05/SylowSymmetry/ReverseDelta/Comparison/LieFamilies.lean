module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.InnerOnly
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Linear
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Unitary
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.LinearThree
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Symplectic
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional

/-!
# Lie-family residual comparison

The action transports retain the actual central quotient maps of both
components. PSL₂ is excluded by its trivial inner residual and a cubic
element in the outer residual, including the smallest half-field endpoint.
The Suzuki exclusion uses its proved automorphism theorem, including
exceptional covers of Sz(8). The unitary exclusion uses precisely stated
earlier involution rows, then proves the solvability contradiction. Together
these exclude every Bender alternative under those explicit unitary inputs.

The eight rank-two constructors are excluded by the linear, symplectic, and
exceptional comparisons. In the symplectic root case relative normality forces
the outer simple residual to have the order of the inner rank-one Levi factor;
the actual model orders contradict this. For G₂(2)′ it would give a quotient
of order two of a two-perfect residual. These arguments retain both central
maps, the small derived endpoints, and the full-group root actors.

`RankTwoInvolutionInputs` lists the remaining earlier inputs on actual models,
including the triality divisor and the binary Ree action and involution coverage
used for Tits. The G₂(2)′ centerless-cover clause of 16.1.2 is a separate,
model-dependent premise. No family exclusion or residual comparison is assumed
as an input. The source-theorem owner must discharge these inputs and the unitary
table before using this conditional helper to complete 16.4.11(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2–4, printed pp.1170–1171, and 16.4.11(2), p.1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The precise earlier model facts consumed by the rank-two comparison.
Each field refers to the concrete actions, residual equivalences, and field
parameters in its defining module. The binary G₂ covering clause is supplied
separately, only when that quotient model occurs. -/
structure RankTwoInvolutionInputs : Prop where
  linear : LinearThreeInvolutionTable
  symplectic : SymplecticInvolutionTable
  symplectic_derived : BinarySymplecticInvolutionRows
  g2 : Exceptional.G2InvolutionTable
  g2_derived : Exceptional.BinaryG2InvolutionRows
  triality : Exceptional.TrialityInvolutionTable
  ree_f4 : Exceptional.ReeInvolutionTable
  tits : Exceptional.TitsInvolutionInputs

/-- The Suzuki case, through the canonical center/two-core quotient map. -/
theorem not_suzuki_bender_quotient
    (d : Contrary T z L g R r) {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Nonempty ((L ⧸ pCore 2 L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  obtain ⟨e⟩ := hmodel
  exact Comparison.not_suzuki_quotient d hm
    ((LiePreliminaries.centerQuotientEquivTwoCore (component_oddCore d)).trans e)

/-- The complete Bender exclusion. Only the displayed unitary involution
rows remain explicit earlier inputs; the PSL₂ and Suzuki inputs are proved. -/
theorem not_bender_quotient (d : Contrary T z L g R r)
    (rows : UnitaryInvolutionTable)
    (hmodel : ClassificationModels.IsBenderModel (L ⧸ pCore 2 L)) : False := by
  cases hmodel with
  | linear n hn h => exact not_psl_two_quotient d hn h
  | unitary n hn h => exact not_psu_three_quotient d rows hn h
  | suzuki m hm h => exact not_suzuki_bender_quotient d hm h

/-- All eight characteristic-two rank-two constructors, with their original
field ranges, derived endpoints and actual model identifications. The only
covering premise used here is the G₂(2)′ specialization of 16.1.2(1). -/
theorem not_rank_two_model (d : Contrary T z L g R r)
    (rows : RankTwoInvolutionInputs)
    (binary_g2_cover : Nonempty ((L ⧸ pCore 2 L) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) → center L = ⊥)
    {f : ℕ} (hmodel : ChapterA.Section02.IsTheoremCRankTwoModel
      (L ⧸ pCore 2 L) f) : False := by
  cases hmodel with
  | linear hf h => exact not_psl_three_quotient d rows.linear hf h
  | symplectic hf h => exact not_psp_four_quotient d rows.symplectic hf h
  | g2 hf h => exact not_g2_quotient d rows.g2 hf h
  | triality hf h => exact not_triality_quotient d rows.triality hf h
  | ree_f4 m hm _ h =>
    obtain ⟨e⟩ := h
    exact not_ree_f4_quotient d rows.ree_f4 hm e
  | symplectic_derived _ h =>
    obtain ⟨e⟩ := h
    exact not_binary_derived_psp_quotient d e rows.symplectic_derived
  | g2_derived _ h =>
    obtain ⟨e⟩ := h
    exact not_g2_derived_quotient d rows.g2_derived (binary_g2_cover ⟨e⟩) e
  | tits _ h =>
    obtain ⟨e⟩ := h
    exact not_tits_quotient d rows.tits e

/-- Exclude the existential rank-two alternative used by the component
catalogue, conditional on the displayed earlier model and covering inputs. -/
theorem not_rank_two_quotient (d : Contrary T z L g R r)
    (rows : RankTwoInvolutionInputs)
    (binary_g2_cover : Nonempty ((L ⧸ pCore 2 L) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) → center L = ⊥)
    (hmodel : ∃ f, ChapterA.Section02.IsTheoremCRankTwoModel
      (L ⧸ pCore 2 L) f) : False := by
  obtain ⟨f, hf⟩ := hmodel
  exact not_rank_two_model d rows binary_g2_cover hf

/-- The complete rank-one/rank-two part of the reverse-Δ₀ comparison.
This is a conditional family helper; the parent source assembly retains the
obligation to establish the unitary, rank-two, and binary G₂ covering inputs. -/
theorem not_lie_quotient (d : Contrary T z L g R r)
    (unitary : UnitaryInvolutionTable) (rows : RankTwoInvolutionInputs)
    (binary_g2_cover : Nonempty ((L ⧸ pCore 2 L) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) → center L = ⊥)
    (hmodel : ClassificationModels.IsBenderModel (L ⧸ pCore 2 L) ∨
      ∃ f, ChapterA.Section02.IsTheoremCRankTwoModel (L ⧸ pCore 2 L) f) : False := by
  rcases hmodel with h | h
  · exact not_bender_quotient d unitary h
  · exact not_rank_two_quotient d rows binary_g2_cover h

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
