module
public import Stellmacher.SectionEight.EightSixCommonStructure
public import Stellmacher.SectionEight.LemmaEightFive

/-!
# Common structure for the canonical hypotheses of Stellmacher (8.6)

Under the central first-step center hypothesis, the actual prescribed
predecessor and subgroups D, L and Q satisfy the source's equation-one data,
[D,L] = Z_a, and elementary-abelian conclusions for D and Q/D.

Lemma (8.5) supplies the initial ordinary SL₂(2) quotient and critical length
two. Its proved fixed-center argument, using (8.4), also gives |Z_a| = 4.
The local common-structure theorem then applies through the graph-preserving
adapter. This is the unconditional common part of the numbered (8.6) theorem;
none of its classification alternatives is assumed.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed pp.41–42,
initial reduction and equations (1)–(3); refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven
universe u

public theorem eight_six_common_structure
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup H)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L) :
    EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q ∧
      ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D := by
  obtain ⟨hquot, hlength⟩ := lemma_eight_five ctx hcenter
  obtain ⟨w, _⟩ := (lemma_eight_one ctx).barred_decomposition
  have hcard := eight_five_center_card_four_of_fixed_normal ctx hcenter w
    (lemma_eight_four ctx hcenter w)
  exact eight_six_common_structure_local ctx.toLocalContext hcenter hquot hlength hcard
    previous hprev D L Q hD hL hQ

end Stellmacher.SectionEight
