module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.RankTwoExclusions
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.TrialityLocal
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.PerfectThreeRank
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# The remaining infinite ordinary rows for the unitary residual

The actual source span has three-rank at least two. Its perfect image in an
ordinary component's central quotient normalizes the nontrivial image of
the radical. Binary PSL₃, triality and Ree two-local geometry bound that
image's three-rank by one. The PSL₃ field-two case follows from order 168.
Together with the previous symplectic and G₂ exclusions, this removes all
infinite rank-two rows of the source catalogue.

Source: Aschbacher–Smith C.3.5, p.150, and 4.2.12–13, pp.610–612.
-/

open scoped MatrixGroups
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

theorem no_unitary_ordinary_psl3
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* PSL(3,F)) : False := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hl := unitary_span_threeRank (M := M) a
  have hu : primeRank 3 (conjugateSpanBy L M) ≤ 1 := by
    apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK e (by decide)
    intro A P hA hP hne hN
    let := hA
    let : Fintype F := Fintype.ofFinite F
    obtain ⟨n,_,hcard⟩ := FiniteField.card F 2
    have hF : Nat.card F = 2 ^ (n : ℕ) := by
      simpa only [Nat.card_eq_fintype_card] using hcard
    by_cases hn1 : (n : ℕ) = 1
    · have hcardF : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
      exact (primeRank_subgroup_le 3 A).trans (primeRank_le_one_of_square_not_dvd (by
        rw [Matrix.PSL3.LinearThree.card_projective F,hcardF]
        norm_num))
    · obtain ⟨g,point,hg⟩ :=
        MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F n.pos hF
          (normalizer (P : Set PSL(3,F))) ⟨P,hne,hP,rfl⟩
      let j := (MulAut.conj g).toMonoidHom.comp A.subtype
      have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic F point := by
        refine le_trans ?_ hg
        rintro _ ⟨x,rfl⟩
        exact mem_map_of_mem _ (hN x.property)
      have hfour : 4 ≤ Nat.card F := by
        rw [hF]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
          (show 2 ≤ (n : ℕ) by have := n.pos; omega)
      by_contra! hb
      apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic F
        (p := 3) (by decide) (by omega) hfour j
        ((MulAut.conj g).injective.comp A.subtype_injective)
      cases point
      · exact Or.inr hj
      · exact Or.inl hj
  omega

theorem no_unitary_ordinary_triality
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    {n : ℕ} (hn : 1 ≤ n)
    (e : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ center K)) : False := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hl := unitary_span_threeRank (M := M) a
  have hu := h.ordinary_span_primeRank_le_one_of_isTrialityGroupAt K hK hn e (by decide : Odd 3)
  omega

theorem no_unitary_ordinary_ree
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    {m : ℕ} (hm : 1 ≤ m) (e : K ⧸ center K ≃* ReeF4.Model m) : False := by
  have hl := unitary_span_threeRank (M := M) a
  have hu : primeRank 3 (conjugateSpanBy L M) ≤ 1 := by
    apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK e (by decide)
    intro A P hA hp hne hN
    let := hA
    exact ReeF4.ConverseParabolics.perfect_two_normalizer_threeRank_le_one hm A P hp hne hN
  omega
end CFSG.Quasithin.ChapterC.HypothesisC28
