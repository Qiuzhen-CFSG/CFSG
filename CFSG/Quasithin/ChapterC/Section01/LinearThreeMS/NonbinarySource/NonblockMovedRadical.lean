module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockMovedCenter
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSRadicalInequality

/-!
# Original Sylow inequalities from the natural moved center

In the original nonblock configuration, a natural [Z(Q),K] already
promotes to the whole natural center and places L in the line residual,
with one change of basis. Apply the original ambient radical-normalizer
argument at that marking to every eligible Sylow subgroup of KR. The
resulting inequality is independent of the quotient marking, so it feeds
the moved-sections MSData constructor directly. That constructor transports
the doubled-dual section by the same change of basis as the natural one.

Thus only the whole natural moved-center and whole doubled-dual quotient
models remain as section inputs. No radical callback, parabolic-placement
premise, ambient centrality of C_Q(K), or restriction excluding field four
is needed. The literal secondary-component application retains its own
original ambient hypothesis. Recognition of those whole sections and the
remaining intrinsic C.1.34 alternatives are still required.

Source: Aschbacher--Smith C.1.34(3), pp.136--137, and original 4.3.8--14,
pp.616--618.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.MovedCenter
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

/-- A natural whole moved center gives the original radical inequality for
every eligible Sylow subgroup, including over the field of four elements. -/
theorem radical_inequality {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) ⁅U c,K c⁆ ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  obtain ⟨a,ha,hline,_⟩ := exists_whole_natural_center D hf hn hF e hm
  exact natural_center_radical_inequality D hf n hn hF
    (e.trans (Matrix.HigherLinear.SubspaceTransport.slConj a)) ha hline P hP hRP

/-- Construct the original MSData with simultaneous line and Sylow markings
from the two whole sections. The original radical inequalities are discharged. -/
theorem exists_msData_of_sections
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (hm : HasSectionModel (K c) ⁅U c,K c⁆ ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F.Carrier) 3))
    (hdual : HasSectionModel (K c) (Q c) (U c) (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F.Carrier) 3).dual.prod
        (Representation.specialLinearNatural (k := F.Carrier) 3).dual)) :
    ∃ d : MSData c n, d.field = F ∧
      (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier := by
  have hF : Nat.card F.Carrier = 2^n := F.card_eq.trans (congrArg (2^·) hdegree)
  apply exists_msData_of_moved_sections D hf n hn F hdegree e hm hdual
  intro P hRP
  exact radical_inequality D hf n hn hF e hm
    ((P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G)).map
      (K c ⊔ c.I.pCoreIn 2 : Subgroup G).subtype) ⟨P,rfl⟩ hRP

/-- Feed the constructed witness to the original secondary-component
application, retaining its separate original ambient hypothesis. -/
theorem exists_sourceComponent_of_sections
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (hm : HasSectionModel (K c) ⁅U c,K c⁆ ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F.Carrier) 3))
    (hdual : HasSectionModel (K c) (Q c) (U c) (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F.Carrier) 3).dual.prod
        (Representation.specialLinearNatural (k := F.Carrier) 3).dual)) :
    ∃ B : Subgroup (rootNormalizer c),
      B.IsCComponent ∧ B.Normal ∧ IsQuasisimple (B ⧸ pCore 2 B) ∧
      secondary c < B.map (rootNormalizer c).subtype ∧
      B.map (rootNormalizer c).subtype ≤ Subgroup.centralizer (root c : Set G) ∧
      U c < rootCoreLayer c ∧
      rootCoreLayer c ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 ∧
      (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c ∧
      (frattini (rootCoreLayer c)).map (rootCoreLayer c).subtype ≤ root c ∧
      ⁅rootCoreLayer c,rootCoreLayer c⁆ ≤ root c := by
  obtain ⟨d,_,hL,_⟩ := exists_msData_of_sections D hf n hn F hdegree e hm hdual
  exact d.exists_sourceComponent_of_line_marking hn D h hL

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.MovedCenter
