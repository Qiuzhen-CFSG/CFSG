module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveContracts
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveSectionTernarySieve
public import Theory.GroupTheory.PerfectFiveSectionSmallCore
public import Theory.GroupTheory.PrimeCentralizerExclusion
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import GorensteinWalter.PSL2Center

/-!
# Excluding the PSL₃(5) row of the literal nonblock sieve

The secondary projection has quotient A₅ when n = 2. Its order divides
372000, so its two-core has order dividing eight. Generation by five-elements
then makes that core central. Consequently the actual torus centralizes the
whole secondary action image. The outer automorphism group of PSL₃(5) is a
two-group, so an automorphism of order three is inner. Since nine does not
divide 372000, the prime-order centralizer argument excludes it and Cauchy's
theorem kills the original torus image.

Source: Aschbacher–Smith, original 4.3.16(3) and the following elimination,
printed p.618. The projection, inner image and full quotient remain literal.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The actual secondary quotient at n = 2 is the alternating group A₅. -/
theorem SecondaryData.secondaryProjection_alternating_five (s : SecondaryData c n) (hn : n = 2) :
    Nonempty (((SecondaryData.secondaryProjection s).range ⧸
      pCore 2 (SecondaryData.secondaryProjection s).range) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨em⟩⟩ := SecondaryData.secondaryProjection_model s
  obtain ⟨ea⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := F) (by simpa [hn] using hF)
  exact ⟨em.trans ea⟩

omit [Finite G] in
/-- Centrality of the projected two-core lifts to the entire secondary action image. -/
theorem SecondaryData.coreImageCentral_of_projection_core_le_center (s : SecondaryData c n)
    (hc : pCore 2 (SecondaryData.secondaryProjection s).range ≤
      center (SecondaryData.secondaryProjection s).range) : SecondaryData.CoreImageCentral s := by
  let f := SecondaryData.secondaryProjection s
  have hcore : (pCore 2 (secondary c)).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 (secondary c)).Normal).map _ f.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  intro a ha
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨u,hu,heu⟩ := hx
  have hxa : x = ⟨u,(s.secondary_le.trans (map_subtype_le _)) u.property⟩ := Subtype.ext heu.symm
  rw [hxa,SecondaryData.action_secondary]
  rintro b ⟨y,hy,rfl⟩
  have hya : y = ⟨(⟨y,hy⟩ : secondary c),(s.secondary_le.trans (map_subtype_le _)) hy⟩ := rfl
  rw [hya,SecondaryData.action_secondary]
  have huC := hc (hcore (mem_map_of_mem f.rangeRestrict hu))
  have heq := congrArg (fun z : f.range => (z : s.component ⧸ pCore 2 s.component))
    (mem_center_iff.mp huC (f.rangeRestrict ⟨y,hy⟩))
  change f ⟨y,hy⟩ * f u = f u * f ⟨y,hy⟩ at heq
  simpa only [← map_mul] using congrArg
    (MulAut.conj : (s.component ⧸ pCore 2 s.component) →* MulAut _) heq

private theorem ternary_five_card {J : Type*} [Group J] (hm : ClassicalGroup.IsPSL J 3 5) :
    Nat.card J = 372000 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective, hF]
  norm_num

/-- The actual secondary two-core image is central in the PSL₃(5) row. -/
theorem SecondaryData.coreImageCentral_of_ternary_five (s : SecondaryData c n) (hn : n = 2)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 5) :
    SecondaryData.CoreImageCentral s := by
  apply SecondaryData.coreImageCentral_of_projection_core_le_center s
  let H := (SecondaryData.secondaryProjection s).range
  let := SecondaryData.secondaryProjection_perfect s
  obtain ⟨e⟩ := SecondaryData.secondaryProjection_alternating_five s hn
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (H ⧸ pCore 2 H) := e.isSimpleGroup
  have hquot : Nat.card (H ⧸ pCore 2 H) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  apply pCore_two_le_center_of_perfect_simple_five_section (by rw [hquot]; decide)
  have hH : Nat.card H = 60 * Nat.card (pCore 2 H) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 H),hquot]
  have hd : Nat.card (pCore 2 H) ∣ 6200 := by
    have h := H.card_subgroup_dvd_card
    rw [hH,ternary_five_card hm] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 60) h
  have hcop : Nat.Coprime (Nat.card (pCore 2 H)) 775 := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 2 775).pow_left k
  exact hcop.dvd_mul_right.mp hd

/-- No order-three automorphism centralizes the entire secondary image in PSL₃(5). -/
theorem SecondaryData.ternary_five_prime_exclusion (s : SecondaryData c n) (hn : n = 2)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 5)
    {a : MulAut (s.component ⧸ pCore 2 s.component)}
    (ha : a ∈ centralizer (SecondaryData.secondaryImage s : Set _)) : orderOf a ≠ 3 := by
  let J := s.component ⧸ pCore 2 s.component
  let : IsQuasisimple J := s.quasisimple
  have hs : IsSimpleGroup J := by
    obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
    let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
    exact e.isSimpleGroup
  let := hs
  have hJ : center J = ⊥ := by
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp h)).elim
  let H := (SecondaryData.secondaryProjection s).range
  let := SecondaryData.secondaryProjection_perfect s
  obtain ⟨e⟩ := SecondaryData.secondaryProjection_alternating_five s hn
  have hquot : Nat.card (H ⧸ pCore 2 H) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd3 : 3 ∣ Nat.card H := by
    have hd := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _)
    rw [hquot] at hd
    exact (by decide : 3 ∣ 60).trans hd
  have hcenter : center (H ⧸ pCore 2 H) = ⊥ := by
    obtain ⟨F,_,_,_,⟨em⟩⟩ := SecondaryData.secondaryProjection_model s
    apply (eq_bot_iff_forall _).mpr
    intro z hz
    have hz' : em z ∈ center PSL(2,F) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := em.surjective y
      simpa only [map_mul] using congrArg em (mem_center_iff.mp hz y)
    rw [GorensteinWalter.psl2_center_eq_bot,mem_bot] at hz'
    exact em.injective (hz'.trans (map_one em).symm)
  intro horder
  have hout := ChapterA.Section03.SourceEmbeddings.linear_three_five_outer_two hm
  let q := QuotientGroup.mk' (MulAut.innerSubgroup J)
  have hqdiv : orderOf (q a) ∣ 3 := by simpa only [horder] using orderOf_map_dvd q a
  have hcop := hout.orderOf_coprime (by decide : Nat.Coprime 2 3) (q a)
  have hqone : q a = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hqdiv)
  apply inner_automorphism_orderOf_ne_prime_of_square_not_dvd H hd3
    (by rw [ternary_five_card hm]; norm_num)
    (center_le_pCore_of_quotient_center_eq_bot hcenter) (by decide : Nat.Coprime 2 3) hJ a
    (by rwa [← SecondaryData.secondary_action_image s])
    ((QuotientGroup.eq_one_iff a).mp hqone) horder

/-- The prescribed nontrivial torus action excludes PSL₃(5) at n = 2. -/
theorem SecondaryData.not_ternary_five_model (s : SecondaryData c n) (hn : n = 2) :
    ¬ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 5 := by
  intro hm
  apply s.torus_action_ne_bot
  apply SecondaryData.torusImage_eq_bot_of_prime_centralizer s (by omega)
    (SecondaryData.coreImageCentral_of_ternary_five s hn hm)
  intro p hp _ hd a _ hc horder
  have hp3 : p = 3 := by
    rw [hn] at hd
    norm_num at hd
    exact (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left hp.ne_one
  exact SecondaryData.ternary_five_prime_exclusion s hn hm hc (horder.trans hp3)
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
