module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.ComponentRecognition
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.Rank
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.Mathieu.M11.Properties.RankLower
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M23.Properties.TwoRank
public import GorensteinWalter.PGL2DihedralSylow
public import Theory.GroupTheory.PrimeRankAutomorphismOrder
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankResidualCentralizer
/-!
# Finite rows in the double-linear component sieve

A natural L₂(2ⁿ) module survives every central quotient and has two-rank
at least 2n. Small alternating and odd linear rows are therefore impossible.
The surviving finite Mathieu, PSL₃(4), and PSL₄(2) rows force n=2 and
have cubic rank two, including the original binary M₂₂ quotient.
This is the rank consequence required by Aschbacher–Smith 2.4.7,
printed p.541, from the refined list in 2.3.9(7).
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.LinearShadows.Double
variable {G : Type*} [Group G] [Finite G]

/-- Restricting a central-kernel map preserves the natural-block two-rank. -/
theorem natural_block_two_rank_of_central_map {Y : Type*} [Group Y] [Finite Y]
    (L : Subgroup G) {n : ℕ} (hn : ChapterC.IsL2EvenBlock L n)
    (f : G →* Y) (hk : f.ker ≤ center G) : n*2 ≤ primeRank 2 Y := by
  apply natural_block_image_two_rank hn (f.comp L.subtype)
  intro l hl
  apply mem_center_iff.mpr
  intro u
  apply Subtype.ext
  exact mem_center_iff.mp (hk hl) u

private theorem natural_two_rank (L : Subgroup G) {n : ℕ}
    (hn : ChapterC.IsL2EvenBlock L n) : n*2 ≤ primeRank 2 G :=
  natural_block_image_two_rank hn L.subtype
    (by rw [L.subtype.ker_eq_bot L.subtype_injective]; exact bot_le)

/-- The finite rows of two-rank at most five force the natural field to have
four elements, and hence their cubic rank is the required torus rank. -/
theorem odd_rank_of_two_three_bounds (L : Subgroup G) {n : ℕ}
    (hn : ChapterC.IsL2EvenBlock L n) (h2 : primeRank 2 G ≤ 5)
    (h3 : 2 ≤ primeRank 3 G) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2^n-1 ∧ 2≤primeRank p G := by
  have hr := natural_two_rank L hn
  have hn2 : n=2 := by have := hn.1; omega
  exact ⟨3,by decide,by decide,by rw [hn2]; decide,h3⟩

/-- The same finite-row argument survives the actual central two-core. -/
theorem odd_rank_of_quotient_two_three_bounds [IsQuasisimple G]
    (L : Subgroup G) {n : ℕ} (hn : ChapterC.IsL2EvenBlock L n)
    (h2 : primeRank 2 (G ⧸ pCore 2 G) ≤ 5)
    (h3 : 2 ≤ primeRank 3 (G ⧸ pCore 2 G)) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2^n-1 ∧ 2≤primeRank p G := by
  have hr := natural_block_two_rank_of_central_map L hn (QuotientGroup.mk' (pCore 2 G))
    (by rw [QuotientGroup.ker_mk']; exact IsQuasisimple.pCore_le_center 2)
  have hn2 : n=2 := by have := hn.1; omega
  refine ⟨3,by decide,by decide,by rw [hn2]; decide,?_⟩
  rwa [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 G) pCore_isPGroup] at h3

private theorem small_alternating_two_rank {k : ℕ} (hk : k=6 ∨ k=7) :
    primeRank 2 (alternatingGroup (Fin k)) ≤ 3 := by
  let P : Sylow 2 (alternatingGroup (Fin k)) := Classical.choice inferInstance
  rw [P.primeRank_eq]
  apply primeRank_le_of_card_le_prime_pow
  rw [P.card_eq_multiplicity]
  rcases hk with rfl | rfl <;> rw [nat_card_alternatingGroup,Nat.card_fin] <;> decide +kernel

/-- A central alternating quotient of degree six or seven has too little
 two-rank to contain the actual natural block. -/
theorem not_small_alternating_quotient (L : Subgroup G) {n k : ℕ}
    (hn : ChapterC.IsL2EvenBlock L n) (hk : k=6 ∨ k=7)
    (e : (G ⧸ center G) ≃* alternatingGroup (Fin k)) : False := by
  have hr := natural_block_two_rank_of_central_map L hn (QuotientGroup.mk' (center G))
    (by rw [QuotientGroup.ker_mk'])
  rw [primeRank_equiv 2 e] at hr
  have hu := small_alternating_two_rank hk
  have := hn.1
  omega

/-- The odd degree-three linear row has two-rank only two. -/
theorem not_psl_three_three (L : Subgroup G) {n : ℕ}
    (hn : ChapterC.IsL2EvenBlock L n) (e : G ≃* PSL(3,ZMod 3)) : False := by
  have hr := natural_two_rank L hn
  rw [primeRank_equiv 2 e] at hr
  have hu := Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le
    (F := ZMod 3) (by decide : Nat.Prime 3) (by decide : Odd 3) (by simp)
  have := hn.1
  omega

private theorem fermatMersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨a,ha⟩ | ⟨a,ha⟩
  · have hlow : 2 ≤ 2^(2^a) := Nat.le_pow (by norm_num)
    omega
  · have hd : 2 ∣ 2^a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
    omega

/-- The odd prime-field rank-one row has dihedral Sylow two-subgroups. -/
theorem not_psl_two_fermatMersenne (L : Subgroup G) {n p : ℕ}
    (hn : ChapterC.IsL2EvenBlock L n) (hp : IsFermatOrMersennePrime p)
    (hm : ClassicalGroup.IsPSL G 2 p) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 (PSL(2,F)) := Classical.choice inferInstance
  have ho : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p,1,hp.1,fermatMersenne_odd hp,by decide,by simpa only [pow_one] using hF⟩
  obtain ⟨m,_,⟨a⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F ho P
  have hu := (P.primeRank_eq.trans (primeRank_equiv 2 a)).le.trans (dihedral_rank_le_two m)
  have hr := natural_two_rank L hn
  rw [primeRank_equiv 2 e] at hr
  have := hn.1
  omega

/-- The exceptional PSL₃(4) two-core quotient supplies the required cubic rank. -/
theorem odd_rank_of_psl_three_four_quotient [IsQuasisimple G]
    (L : Subgroup G) {n : ℕ} (hn : ChapterC.IsL2EvenBlock L n)
    (hm : ClassicalGroup.IsPSL (G ⧸ pCore 2 G) 3 4) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2^n-1 ∧ 2≤primeRank p G := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  apply odd_rank_of_quotient_two_three_bounds L hn
  · rw [primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (n:=2) (by decide) hF]
    decide
  · rw [primeRank_equiv 3 e]
    exact LinearDouble.psl_three_prime_rank (by decide) (by rw [hF])

private theorem m11_two_rank_le_four : primeRank 2 M11 ≤ 4 := by
  let P : Sylow 2 M11 := Classical.choice inferInstance
  rw [P.primeRank_eq]
  apply primeRank_le_of_card_le_prime_pow
  rw [P.card_eq_multiplicity,m11_order]
  decide +kernel

/-- Each direct Mathieu survivor has the same required cubic witness. -/
theorem odd_rank_of_mathieu (L : Subgroup G) {n : ℕ}
    (hn : ChapterC.IsL2EvenBlock L n)
    (hm : Nonempty (G ≃* M11) ∨ Nonempty (G ≃* M22) ∨ Nonempty (G ≃* M23)) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2^n-1 ∧ 2≤primeRank p G := by
  apply odd_rank_of_two_three_bounds L hn
  · rcases hm with hm | hm | hm
    · obtain ⟨e⟩ := hm
      exact (primeRank_equiv 2 e).le.trans (m11_two_rank_le_four.trans (by decide))
    · obtain ⟨e⟩ := hm
      exact (primeRank_equiv 2 e).le.trans (m22_twoRank_le_four.trans (by decide))
    · obtain ⟨e⟩ := hm
      exact (primeRank_equiv 2 e).le.trans (m23_twoRank_le_four.trans (by decide))
  · rcases hm with hm | hm | hm
    · obtain ⟨e⟩ := hm
      exact (primeRank_equiv 3 e).ge.trans' m11_primeRank_three_ge_two
    · obtain ⟨e⟩ := hm
      exact (primeRank_equiv 3 e).ge.trans' m22_primeRank_three.ge
    · obtain ⟨e⟩ := hm
      rw [primeRank_equiv 3 e]
      exact m22_primeRank_three.ge.trans ((primeRank_equiv 3 m23EquivM22PointStabilizer).le.trans
        (Theory.GroupTheory.primeRank_le_of_injective 3 _ (MulAction.stabilizer M23 (9:Fin 23)).subtype_injective))

/-- The residual binary M₂₂ cover has the same odd rank as its actual quotient. -/
theorem odd_rank_of_mathieu_quotient [IsQuasisimple G]
    (L : Subgroup G) {n : ℕ} (hn : ChapterC.IsL2EvenBlock L n)
    (e : (G ⧸ pCore 2 G) ≃* M22) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2^n-1 ∧ 2≤primeRank p G := by
  apply odd_rank_of_quotient_two_three_bounds L hn
  · rw [primeRank_equiv 2 e]
    exact m22_twoRank_le_four.trans (by decide)
  · rw [primeRank_equiv 3 e,m22_primeRank_three]

/-- The binary degree-four row is the alternating group of degree eight. -/
theorem odd_rank_of_psl_four_two (L : Subgroup G) {n : ℕ}
    (hn : ChapterC.IsL2EvenBlock L n) (e : G ≃* PSL(4,ZMod 2)) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2^n-1 ∧ 2≤primeRank p G := by
  let a := Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  have hz : center PSL(4,ZMod 2) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have h : a x ∈ center (alternatingGroup (Fin 8)) := (centerCongr a ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at h
    exact a.injective (h.trans (map_one a).symm)
  apply odd_rank_of_two_three_bounds L hn
  · rw [primeRank_equiv 2 e]
    exact (Theory.GroupTheory.primeRank_le_of_injective 2 MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot hz)).trans
      (BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le.trans (by decide))
  · rw [primeRank_equiv 3 (e.trans a)]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
end CFSG.Quasithin.Chapter2.LinearShadows.Double
