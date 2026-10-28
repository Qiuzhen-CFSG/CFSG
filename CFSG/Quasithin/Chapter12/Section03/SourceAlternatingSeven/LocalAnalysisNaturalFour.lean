module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionTransitive
public import Theory.Representation.BinaryAlternatingSevenControl.FixedLine

/-!
# Transitivity and point-centralizer escape in the exceptional A₇ row

The faithful action of L/C_L(V) on the entire chosen four-space is
transitive on its fifteen nonzero vectors. The original inclusion into V
transports these operators to actual L-conjugators. Conjugating the escape
supplied by 12.2.13 then proves escape at every nonidentity point of V.

These are the opening steps of the exceptional branch of 12.3.3. The
central-line residual, its ambient component enlargements, and the final
block contradiction are still required to exclude that branch.
Source: Aschbacher--Smith, Lemma 12.3.3, printed p.808.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

/-- The literal L-action is transitive on all of V minus the identity. -/
theorem four_transitive
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {x y : G} (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ l ∈ L, l * x * l⁻¹ = y := by
  let := S.chosen.actionCentralizer_normal
  apply RecognitionSource.chosen_vector_transitive S.chosen ?_ hx hy hx1 hy1
  intro v w hv hw
  let σ := S.chosen.faithfulAction.comp e.symm.toMonoidHom
  obtain ⟨g,hg⟩ := BinaryAlternatingSevenControl.transitive σ
    (S.chosen.faithfulAction_injective.comp e.symm.injective) hd hv hw
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective
    ((centralizer (V : Set G)).subgroupOf L) (e.symm g)
  refine ⟨l,?_⟩
  change S.chosen.faithfulAction (QuotientGroup.mk' _ l) v = w
  rw [hl]
  exact hg

/-- The earlier escape conclusion holds at every nonidentity point in the
exceptional four-dimensional row. -/
theorem four_all_pointCentralizers_escape
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨x,hx,hx1,hout⟩ := escape L V S.hypothesis S.chosen
  obtain ⟨l,hl,he⟩ := S.four_transitive e hd hx hv hx1 hv1
  intro hc
  apply hout
  intro a ha
  have hlN := L.le_normalizer hl
  have hla : l * a * l⁻¹ ∈ centralizer ({v} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hax := mem_centralizer_singleton_iff.mp ha
    rw [← he]
    calc
      (l*a*l⁻¹)*(l*x*l⁻¹) = l*(a*x)*l⁻¹ := by group
      _ = l*(x*a)*l⁻¹ := by rw [hax]
      _ = (l*x*l⁻¹)*(l*a*l⁻¹) := by group
  have hh := mul_mem (mul_mem (inv_mem hlN) (hc hla)) hlN
  convert hh using 1; group

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
