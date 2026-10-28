module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockSymplectic.NonbinaryExclusion
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesSeven
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesFinite
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesBinaryLinear
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingSource
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Direct exclusion of the source symplectic action row

Apply the complete B.5 theorem to the literal offender-generated star action.
Its symplectic action marking supplies the natural block model, and the
nonbinary crossed-module contradiction excludes it over every field in that
row. Thus no separate q = 4 restriction is needed for original 4.3.7.
The previously proved linear and finite source exclusions remove all the
other rows except large G₂. The latter remains the sole explicit premise
owned by qt-d-1222-rankone-uniqueness-block; no C.4.1 classification is assumed.

All actions are transported from the actual moved/fixed section. The original
K and L are unchanged, and the full W is not identified with the chosen V.
Source: Aschbacher--Smith B.5.1, C.4.1 and 4.3.7, pp.99--103,151--153,615--616.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter12.Section02 ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual B.5 natural symplectic action is excluded, with its field,
module and local marking constructed in the same original configuration. -/
theorem SourceConfiguration.false_of_symplectic_source_moved_action
    (c : SourceConfiguration T L) (D : ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (J : Subgroup (StarQuotient (c.K.map c.H.subtype) (c.I.pCoreIn 2)))
    (hCJ : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.K.map c.H.subtype) ≤ J)
    (s : MovedSection ((starRepresentation (c.K.map c.H.subtype)
      (c.I.pCoreIn 2)).comp J.subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf J))
    (F : BinaryField) (hF : 1 < F.degree)
    (E : ActionEquiv (s.action.comp
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf J).subtype) (binarySymplectic F)) : False :=
  NonbinarySymplectic.false_of_natural c D hf hb F hF
    (c.block_model_of_restricted_star_moving hb J hCJ s (binarySymplectic F) E)

private noncomputable def binarySymplecticDerivedEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃*
      alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private noncomputable def binaryFourAlternatingEquiv :
    SL(4,ZMod 2) ≃* alternatingGroup (Fin 8) :=
  Atlas.Order20160A8.sl4TwoEquivPSL.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm

/-- Original 4.3.7 now has just the large-G₂ row left to discharge. The
symplectic row is excluded using its actual B.5 action, not a group tag. -/
theorem source_block_false_of_largeG2_natural_row
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hg2 : ∀ F : BinaryField, 1 < F.degree →
      IsLinearBlockModel c.K (binaryG2 F) → False) : False := by
  obtain ⟨hCJ,s,_,hs⟩ := c.block_star_irreducible_source hf hb
  let e := (subgroupOfEquivOfLe hCJ).symm
  have hseven (a : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.K.map c.H.subtype) ≃* alternatingGroup (Fin 7)) : False := by
    obtain ⟨hn2,ha⟩ := c.alternatingSeven_block_of_star_group hn hpsl hf hb a
    exact c.false_of_alternating_block_four D h.toHypothesis1221
      (by simpa [hn2] using hpsl) hf ha
  have hbinary {d : ℕ} (hd : d = 4 ∨ d = 5)
      (a : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype) ≃* SL(d,ZMod 2)) : False := by
    rcases hd with rfl | rfl
    · exact c.block_star_not_alternatingEight hn hpsl hf hb
        (a.trans binaryFourAlternatingEquiv)
    · exact c.block_star_not_linearFiveTwo hn hpsl hf hb a
  cases hs with
  | linearTwo F _ a _ _ =>
    exact c.block_star_not_linearTwo hf F (e.trans a.groupEquiv)
  | linearThree F _ a _ =>
    exact c.false_of_linearThree_source_moved_action D hn hpsl hf hb _ hCJ s F a
  | symplectic F hF _ a _ =>
    exact c.false_of_symplectic_source_moved_action D hf hb _ hCJ s F hF a
  | symplecticTwo a _ =>
    exact c.block_star_not_alternatingSix hf
      ((e.trans a.subgroupEquiv).trans binarySymplecticDerivedEquiv)
  | g2 F hF _ a _ _ =>
    exact hg2 F hF (c.block_model_of_restricted_star_moving hb _ hCJ s (binaryG2 F) a)
  | g2Two a _ _ => exact c.block_star_not_g2DerivedTwo hf (e.trans a.subgroupEquiv)
  | symmetric d hd a _ _ =>
    rcases hd with rfl | rfl
    · exact c.block_star_not_alternatingFive hf (e.trans a.subgroupEquiv)
    · exact hseven (e.trans a.subgroupEquiv)
  | alternatingSix _ a _ _ =>
    exact c.block_star_not_alternatingSix hf (e.trans a.groupEquiv)
  | alternatingSeven _ _ a _ _ _ => exact hseven (e.trans a)
  | orthogonalSix _ _ a _ _ =>
    exact c.block_star_not_alternatingEight hn hpsl hf hb (e.trans a.groupEquiv)
  | symmetricEight _ a _ =>
    exact c.block_star_not_alternatingEight hn hpsl hf hb (e.trans a.subgroupEquiv)
  | binaryLinear d hd _ a _ => exact hbinary hd (e.trans a.groupEquiv)
  | exteriorFive _ _ a _ _ _ => exact hbinary (Or.inr rfl) (e.trans a)
  | tripleSix _ a _ =>
    exact c.block_star_central_not_alternatingSix hf
      ((QuotientGroup.congr _ _ e (by
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩
          exact (centerCongr e ⟨y,hy⟩).property
        · intro hx
          exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)).trans
        a.quotientEquiv)

/-- The group-row interface follows from the stronger action-level reduction.
The only remaining model exclusion is the large-G₂ source branch. -/
theorem source_block_false_of_largeG2_star_row
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hg2 : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Atlas.G2.Model F.Carrier) → False) : False := by
  apply source_block_false_of_largeG2_natural_row D h hn hpsl c hf hb
  intro F hF hm
  obtain ⟨a⟩ := hm.quotient_iso
  exact hg2 F hF ((c.block_star_quotientEquiv hb).symm.trans a)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
