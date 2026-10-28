module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceCompletion
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Terminal
public import CFSG.Quasithin.Chapter1.Section01Overgroups

/-!
# Source inputs for the nonempty-δ branch of Theorem 2.1.1

For the disjoint Sylow factors in the proof of 2.5.21, ambient strong
closure supplies the three closure hypotheses of Aschbacher's Lemma 3.4.
Disjointness excludes its nested and order-two-intersection alternatives,
so its conclusion contradicts containment of the generated transporter
group in the source's proper normalizer M₊. The factors may be dihedral.
The proved Lemma 3.4 now supplies this implication from exact Theorem ZD.
The ZD theorem and the source pair construction remain independent inputs.

In the terminal A₆ case, even characteristic of the actual ambient Sylow
supplies the central-intersection clause used by the existing E₁₆ normalizer
argument. Its later setup and earlier centralizer equality remain inputs.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 2.5.21, printed pp.566--567, and the terminal argument, p.570.
-/

public section

open Subgroup Theory.GroupTheory
open BenderSuzuki.PFchapter1section1
open CFSG.Quasithin
open CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure

namespace CFSG.Quasithin.Chapter2.SourceCompletionInputs

universe u
variable {G : Type u} [Group G] [Finite G]

/-- For the disjoint source pair, only the first Asc75 alternative survives. -/
theorem top_of_disjoint_source_conclusion (A B : Subgroup G)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hd : Disjoint A B)
    (h : Asc75.Conclusion A B) : intersectionGenerated A B = ⊤ := by
  rcases h with htop | hnested | hexceptional
  · exact htop
  · rcases hnested.1 with hab | hba
    · exact (hA (bot_unique ((le_inf le_rfl hab).trans
        (disjoint_iff.mp hd).le))).elim
    · exact (hB (bot_unique ((le_inf hba le_rfl).trans
        (disjoint_iff.mp hd).le))).elim
  · have hc := hexceptional.2.2
    rw [disjoint_iff.mp hd] at hc
    simp at hc

/-- Literal application to M_+ in the PSL2(p) pair case on p.567.
The source conclusion supplies h; this does not assume M_+ = G. -/
theorem false_of_disjoint_source_pair (A B Mplus : Subgroup G)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hd : Disjoint A B)
    (hproper : Mplus ≠ ⊤) (hbound : intersectionGenerated A B ≤ Mplus)
    (h : Asc75.Conclusion A B) : False := by
  apply hproper
  exact top_unique ((top_of_disjoint_source_conclusion A B hA hB hd h) ▸ hbound)

omit [Finite G] in
/-- Ambient strong closure supplies all three closure clauses of Asc75 (*).
Commutation makes each factor lie in both factor normalizers. -/
theorem source_hypotheses_of_closed_union (T : Sylow 2 G) (A B : Subgroup G)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (ha : A ≤ T) (hb : B ≤ T) (hc : ⁅A, B⁆ = ⊥)
    (hra : TwoRankAtLeastTwo A) (hrb : TwoRankAtLeastTwo B)
    (hclosed : IsStronglyClosedSet ((A : Set G) ∪ B) (T : Subgroup G) ⊤) :
    Asc75.Hypotheses T A B := by
  have hab : A ≤ centralizer (B : Set G) := commutator_eq_bot_iff_le_centralizer.mp hc
  have hba : B ≤ centralizer (A : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  refine ⟨ha, hb, hc, hra, hrb, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact ⟨hx.elim (fun hxA => left_le_intersectionGenerated hA hxA)
        (fun hxB => right_le_intersectionGenerated hB hxB), hclosed.1 hx⟩
    · intro x hx g _ hg
      exact hclosed.2 x hx g (mem_top g) hg.2
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact ⟨hclosed.1 hx, hx.elim (fun hxA => A.le_normalizer hxA)
        (fun hxB => centralizer_le_normalizer (A : Set G) (hba hxB))⟩
    · intro x hx g hg hgt
      exact hclosed.2 x hx g hg hgt.1
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact ⟨hclosed.1 hx, hx.elim
        (fun hxA => centralizer_le_normalizer (B : Set G) (hab hxA))
        (fun hxB => B.le_normalizer hxB)⟩
    · intro x hx g hg hgt
      exact hclosed.2 x hx g hg hgt.1

/-- Source 2.5.21's disjoint-pair contradiction, with the full Asc75 lemma
proved from exact ZD. The literal set closure constructs hypothesis (*),
and the actual intersection-generated subgroup is bounded by M₊. No
non-dihedral restriction or assumed Asc75 conclusion is needed. -/
theorem false_of_disjoint_source_pair_of_theoremZD
    (zd : Asc75.TheoremZD.{u}) (T : Sylow 2 G) (A B Mplus : Subgroup G)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hd : Disjoint A B)
    (ha : A ≤ T) (hb : B ≤ T) (hc : ⁅A, B⁆ = ⊥)
    (hra : TwoRankAtLeastTwo A) (hrb : TwoRankAtLeastTwo B)
    (hclosed : IsStronglyClosedSet ((A : Set G) ∪ B) (T : Subgroup G) ⊤)
    (hproper : Mplus ≠ ⊤) (hbound : intersectionGenerated A B ≤ Mplus) : False :=
  false_of_disjoint_source_pair A B Mplus hA hB hd hproper hbound
    (Asc75.lemma_3_4 zd T A B
      (source_hypotheses_of_closed_union T A B hA hB ha hb hc hra hrb hclosed))

/-- The p.570 central-intersection premise follows from the actual ambient
Sylow and even characteristic; no extra all-subgroups premise is needed. -/
theorem terminal_false_of_even_characteristic
    (d : Chapter2.A6ShadowConstruction.Setup G)
    (T : Sylow 2 G) (hT : (T : Subgroup G) = d.T)
    (hE : IsEvenCharacteristicAt T)
    (hH : d.H ∈ Chapter2.gammaStar (Chapter1.He G) d.M)
    (hempty : Chapter2.gammaEvenZero (Chapter1.He G) d.M = ∅)
    (hC : centralizer ({d.t} : Set G) ≤ d.H)
    (hzT : d.z ∈ (center d.T).map d.T.subtype) (hz1 : d.z ≠ 1) : False := by
  apply Chapter2.A6Shadow.false_of_terminal_source d hH hempty hC hzT hz1
  intro A hA hp hcenter
  apply Chapter1.lemma_1_1_4_3 T hE hA hp
  intro hbot
  exact hcenter ((congrArg (fun U : Subgroup G => (center U).map U.subtype ⊓ A) hT).symm.trans hbot)

end CFSG.Quasithin.Chapter2.SourceCompletionInputs
