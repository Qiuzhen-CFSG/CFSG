module

public import Theory.Representation.BinaryOffender.LineDisplacementObstruction
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.QuadraticEquality
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Geometry

/-!
# The critical-denominator obstruction in the terminal A6 branch

For the original F.9 critical actor, rank two and fixed codimension four
force its actual denominator to have codimension two. The displacement of
every actor element on that denominator lies in the original A1 image, a
space of dimension at most one. Consequently no actor element can move four
dimensions on the full section.

The terminal consumer retains the full rank-two setup and H=Mc. The model
calculation producing rank two, fixed codimension four and such an element
is deliberately separate: this module does not claim that an arbitrary
quadratic actor already satisfies those conclusions.

Source: Aschbacher--Smith, 14.6.24(2), printed p.1041, using the equality
case of 14.5.18(2), equivalently F.9.16(2).
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer

variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The genuine F.9 equality case contradicts a four-dimensional displacement
on the same section. The denominator is constructed, not an added premise. -/
theorem critical_equality_obstruction
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (c : CriticalPair D.L (D.T : Subgroup G) D.H D.V) (hb : 3 ≤ c.path.length)
    [IsElementaryAbelian 2 D.UH]
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (s : ConjugationSection D.H D.UH D.V₁ ρ)
    (hcomparison : Reorientation.denominatorRank D.Vplus D.V₁ c ≤
      rank (Source.starImage D.H (c.Ugamma D.Vplus)))
    (hrank : rank (Source.starImage D.H (c.Ugamma D.Vplus)) = 2)
    (hfixed : fixedCodim ρ (Source.starImage D.H (c.Ugamma D.Vplus)) = 4)
    (a : Source.starImage D.H (c.Ugamma D.Vplus))
    (ha : 4 ≤ fixedCodim ρ (zpowers (a : Source.Hstar D.H))) : False := by
  have he : fixedCodim ρ (Source.starImage D.H (c.Ugamma D.Vplus)) =
      2 * rank (Source.starImage D.H (c.Ugamma D.Vplus)) := by omega
  obtain ⟨W,hW,hr,_,_⟩ :=
    SourceCompletion.f9_denominator_equality D h c hb s hcomparison he
  obtain ⟨W',hW',hZ,hd,_⟩ := SourceCompletion.f9_denominator_action D h c hb s
  have hdenom : Module.finrank (ZMod 2) (E ⧸ W'.toSubmodule) = 2 := by
    rw [hW']
    have hUgH : c.Ugamma D.Vplus ≤ D.H :=
      (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans
        (SourceCompletion.f9_endpoint_spans D h c hb).2
    exact (s.quotient_finrank _ (s.line_le_DH _ _ hUgH)).trans (hr.trans hrank)
  have ha' : 4 ≤ fixedCodim
      (ρ.comp (Source.starImage D.H (c.Ugamma D.Vplus)).subtype) (zpowers a) := by
    change 4 ≤ Module.finrank (ZMod 2)
      (E ⧸ fixedSpace (ρ.comp (Source.starImage D.H (c.Ugamma D.Vplus)).subtype) (zpowers a))
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
    exact ha
  exact no_line_displacement_of_four_le _ W' a (s.image (c.Aone D.V₁)) hZ
    hdenom.le ha' (fun v => hd a v v.property)

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Original-source application: the same obstruction for the terminal Mc,
with its F.9 hypotheses and elementary section proved from the rank-two setup. -/
theorem terminal_equality_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (c : CriticalPair (sourceResidual M Mc) (T : Subgroup G) Mc (localModule T M))
    (hb : 3 ≤ c.path.length)
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (s : ConjugationSection Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T) ρ)
    (hcomparison : Reorientation.denominatorRank (localModule T M) (centralInvolutions T) c ≤
      rank (Source.starImage Mc (c.Ugamma (localModule T M))))
    (hrank : rank (Source.starImage Mc (c.Ugamma (localModule T M))) = 2)
    (hfixed : fixedCodim ρ (Source.starImage Mc (c.Ugamma (localModule T M))) = 4)
    (a : Source.starImage Mc (c.Ugamma (localModule T M)))
    (ha : 4 ≤ fixedCodim ρ (zpowers (a : Source.Hstar Mc))) : False := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  have h : D.Hypothesis :=
    ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  exact critical_equality_obstruction D h c hb s hcomparison hrank hfixed a ha

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
