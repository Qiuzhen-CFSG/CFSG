module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.JankoFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstFieldFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondLargeSporadic

/-!
# J₄ refinement in the original flag normalizers

The relative J₄ embedding forces field four. The original Cartan
factor centralizing the smaller quotient therefore has order three and
acts faithfully on V₁. The checked cubic exclusion rules out the
containing J₄ component. Its second-normalizer counterpart, reexported
here, already uses the full original plane, including C_V(L).

The preceding flag and Cartan premises belong to
qt-d-1222-natural-flag-cartan and are discharged by
qt-d-1222-natural-local-geometry. The relative-components owner retains
the remaining carrier branches and the field-four triangle; this module
does not assume the exhaustive embedding list or an additional field bound.
Source: Aschbacher--Smith 11.1.1--11.1.2, printed pp.761--765,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

private theorem jankoFour_cubic_data {A : Type*} [Group A] [Finite A]
    (e : A ≃* Janko4.Model) :
    center A = ⊥ ∧ 2 ≤ primeRank 3 A ∧ IsPGroup 2 (MulAut.Outer A) := by
  refine ⟨?_, ?_, Janko4.AdequateLocal.outer_isPGroup_two.of_equiv
    (MulAut.outerCongr e).symm⟩
  · apply eq_bot_iff.mpr
    intro a ha
    exact e.map_eq_one_iff.mp
      (Janko4.model_center_eq_bot.le ((centerCongr e) ⟨a,ha⟩).property)
  · rw [primeRank_congr 3 e]
    exact ChapterA.Section03.OddPrime.SourceModels.FourSporadic.j4_three_rank_ge_two

/-- The source J₄ row is impossible at the first flag normalizer.
The field degree is derived from the literal relative embedding. -/
theorem first_not_jankoFour
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) := by
  intro hmodel
  have hn := Embedding.flag_jankoFour_parameters D S f 0 hm hK.1 hLK hmodel
  obtain ⟨hz, hr, ho⟩ := jankoFour_cubic_data hmodel.some
  exact first_component_not_centerless_cubic D S f hm hfix hK hLK
    (inf_le_left.trans (f.cartan_normalizes hu hX 0))
    (hXcard.trans (by rw [hn]; decide)) hfaith hz hr ho

/-- The first-index refinement consumer, with no field-matching or
exhaustive embedding-list premise. -/
theorem first_refinement_of_jankoFour
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree :=
  (first_not_jankoFour D S f hu hm hfix hX hK hLK hXcard hfaith hmodel).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
