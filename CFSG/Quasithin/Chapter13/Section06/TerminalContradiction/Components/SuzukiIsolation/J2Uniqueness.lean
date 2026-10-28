module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.CComponent.OddRankIsolation
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.FiveRank

/-!
# Direct uniqueness of a Hall–Janko C-component

A J₂ two-core quotient has both three-rank and five-rank at least two.
In an SQTK group, the full three-rank forces every distinct C-component
to have order prime to three. The proved known-simple A.3.6 catalogue
therefore makes its quotient a Suzuki group. Every nonbinary Suzuki
quotient has order divisible by five, contradicting full-five-rank
isolation around the original J₂ component.

This proves the J₂ branch of the uniqueness argument in13.6.27 without
5.2.3, an amalgam classification, or a prior normality assumption. The
M₂₃ and PSL₃(4) branches are separate.

Source: Aschbacher–Smith13.6.27, printed p.934; component calculus and
odd-rank bounds from A.3.18 and the actual checked J₂ odd-local subgroup.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
universe u
variable {H : Type u} [Group H] [Finite H]

private theorem suzuki_five_dvd (m : ℕ) (hm : 0 < m) :
    5 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m hm]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  rw [Nat.dvd_iff_mod_eq_zero]
  have he : (2 ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m := by
    rw [← pow_mul]
    have h : (2 * m + 1) * 2 = 2 + 4 * m := by omega
    rw [h, pow_add, pow_mul]
    norm_num
  rw [he, Nat.add_mod, Nat.mul_mod]
  have h16 : 16 ^ m % 5 = 1 := by
    change Nat.ModEq 5 (16 ^ m) 1
    simpa using (show Nat.ModEq 5 16 1 by decide).pow m
  rw [h16]

/-- An actual J₂ C-component is the only C-component of a known-simple
SQTK group. Its normality is a consequence, not a hypothesis. -/
theorem component_unique_of_j2
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) :
    ∀ D : Subgroup H, D.IsCComponent → D = K := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc : Candidate (⊥ : Subgroup H) K := Or.inl ⟨e⟩
  have hz := ThreeStructure.candidate_center_eq_bot hK hc
  have hthree := ThreeStructure.candidate_three_rank_ge_two hc
  have hfive : 2 ≤ primeRank 5 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 5 e]
    exact Sporadic.LeechRelated.J2.five_rank_ge_two
  intro D hD
  by_contra hne
  have h3 := hK.other_coprime_three_of_rank hz hthree
    (hH.stronglyQuasithin 3 (by decide) (by decide)) hD hne
  have h5 := hK.other_coprime_of_full_odd_rank (p := 5) (by decide) hz
    ((hH.stronglyQuasithin 5 (by decide) (by decide)).trans hfive) hD hne
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_, hH.isKGroup.quotient (pCore 2 H)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  obtain ⟨m,hm,⟨f⟩⟩ := Catalogue.component_suzuki_quotient
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    hQ hD h3
  have hd : 5 ∣ Nat.card D := by
    apply dvd_trans _ (pCore 2 D).card_quotient_dvd_card
    rw [Nat.card_congr f.toEquiv]
    exact suzuki_five_dvd m (by omega)
  exact ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mp h5) hd

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
