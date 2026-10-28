module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow

/-!
# The two-central marking of the actual HS involution classes

The marked involution `e0` centralizes the concrete Sylow two-subgroup.
The other representative has centralizer index 15400, which excludes
two-centrality. Exhaustive intrinsic class coverage therefore identifies
exactly the two classes used by the covering argument.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423;
the intrinsic centralizers are those of 16.1.5(10), printed p.1172.
No assertion about lifts to a central cover is made here.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.BlockNormalizer
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner

/-- The first representative is central in the actual marked Sylow subgroup. -/
theorem e0_twoCentral : TwoCentral e0 := by
  have hmem : e0 ∈ subgroup := elementary_le_subgroup 0
    (subset_closure ⟨0, by simp, rfl⟩)
  refine ⟨baseSylow, hmem, ?_⟩
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  have hc : subgroup ≤ centralizer ({e0} : Set Carrier) := by
    apply (closure_le _).mpr
    rintro y ⟨i, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    have h := baseSylow_conjugation i 0
    fin_cases i <;> exact h
  exact mem_centralizer_singleton_iff.mp (hc x.property)

/-- The second representative has even centralizer index. -/
theorem t_centralizer_index :
    (centralizer ({ClassCoverage.t} : Set Carrier)).index = 15400 := by
  obtain ⟨e⟩ := ClassCoverage.product_centralizer_equiv
  have hc : Nat.card (centralizer ({ClassCoverage.t} : Set Carrier)) = 2880 :=
    (Nat.card_congr e.toEquiv).trans ClassCoverage.product_card
  have h := (centralizer ({ClassCoverage.t} : Set Carrier)).card_mul_index
  rw [hc, NormalizerIndex.card_carrier] at h
  omega

/-- The product-centralizer class is not two-central. -/
theorem t_not_twoCentral : ¬ TwoCentral ClassCoverage.t := by
  intro h
  apply h.not_dvd_centralizer_index
  rw [t_centralizer_index]
  decide

private theorem twoCentral_of_isConj {a b : Carrier} (h : IsConj a b)
    (ha : TwoCentral a) : TwoCentral b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  exact hg ▸ ha.map (MulAut.conj g)

/-- This is precisely the two-central class in the fixed degree-100 carrier. -/
theorem twoCentral_iff_isConj_e0 (x : Carrier) (hx : orderOf x = 2) :
    TwoCentral x ↔ IsConj e0 x := by
  constructor
  · intro h
    rcases ClassCoverage.involution_classes x hx with he | ht
    · exact he
    · exact (t_not_twoCentral (twoCentral_of_isConj ht.symm h)).elim
  · intro h
    exact twoCentral_of_isConj h e0_twoCentral

/-- The other class is exactly the non-two-central class of I.2.2(5b). -/
theorem not_twoCentral_iff_isConj_t (x : Carrier) (hx : orderOf x = 2) :
    ¬ TwoCentral x ↔ IsConj ClassCoverage.t x := by
  constructor
  · intro h
    rcases ClassCoverage.involution_classes x hx with he | ht
    · exact (h (twoCentral_of_isConj he e0_twoCentral)).elim
    · exact ht
  · intro ht h
    exact t_not_twoCentral (twoCentral_of_isConj ht.symm h)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
