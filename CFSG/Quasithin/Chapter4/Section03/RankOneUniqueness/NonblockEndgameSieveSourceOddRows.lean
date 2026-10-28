module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceGeometry
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveExclusionsJanko
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveExclusionsTernaryFive

/-!
# The odd-model rows with only core movement

In the J₁ and PSL₃(5) rows, the original secondary two-core has central
image. The literal secondary projection has A₅ quotient. Its order is divisible
by three, but the ambient order is not divisible by nine. The existing
prime-centralizer theorem therefore kills every cubic centralizing automorphism;
Cauchy kills the torus image. Core movement now kills Q-star. Mutual normalization
puts the radical-secondary commutator in the central secondary-core image,
and perfectness kills that commutator. Explicit whole-radical generation then
kills R₂-star, contradicting its prescribed nontrivial action.

The final conditional assembly excludes all three nonexceptional source rows
without whole-radical torus movement. It retains the four-row model inspection
and whole-radical generation as premises. The sieve owner must still establish
the model inspection, and the nonblock constructor owner must supply generation
and the source geometry. No legacy SecondaryData witness is used.
Source: Aschbacher–Smith, original 4.3.16 and its elimination, printed p.618;
see the source movement correction in docs/quasithin-proof-basis.md.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve.SourceImages
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable (c : SourceConfiguration T L) (C : Subgroup (rootNormalizer c)) [C.Normal]
variable (hK : secondary c ≤ C.map (rootNormalizer c).subtype)

omit [C.Normal] in
/-- At degree two the actual projected secondary quotient is A₅. -/
theorem secondaryProjection_alternating_five
    (hm : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ 2)) :
    Nonempty (((secondaryProjection c C hK).range ⧸
      pCore 2 (secondaryProjection c C hK).range) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨em⟩⟩ := secondaryProjection_model c C hK hm
  obtain ⟨ea⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := F) (by simpa using hF)
  exact ⟨em.trans ea⟩

omit [C.Normal] in
private theorem secondaryProjection_quotient_card
    (hm : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ 2)) :
    Nat.card ((secondaryProjection c C hK).range ⧸ pCore 2 (secondaryProjection c C hK).range) = 60 := by
  obtain ⟨e⟩ := secondaryProjection_alternating_five c C hK hm
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

omit [C.Normal] in
private theorem three_dvd_secondaryProjection_card
    (hm : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ 2)) :
    3 ∣ Nat.card (secondaryProjection c C hK).range := by
  have hd := card_dvd_of_surjective
    (QuotientGroup.mk' (pCore 2 (secondaryProjection c C hK).range))
    (QuotientGroup.mk'_surjective _)
  rw [secondaryProjection_quotient_card c C hK hm] at hd
  exact (by decide : 3 ∣ 60).trans hd

private theorem janko_center : center Janko1.Model = ⊥ := by
  rcases (inferInstance : (center Janko1.Model).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative Janko1.Model (center_eq_top_iff.mp h)).elim

include hK in
/-- In the J₁ model the actual secondary-core action image is central. -/
theorem coreImageCentral_of_janko (e : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    image c C ((secondary c).pCoreIn 2) ≤ centralizer (image c C (secondary c) : Set _) := by
  let f := e.toMonoidHom.comp (secondaryProjection c C hK)
  let := EndgameSieve.secondary_perfect c
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hcore : (pCore 2 (secondary c)).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 (secondary c)).Normal).map _ f.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  have hc := hcore.trans (Janko1.perfect_subgroup_pCore_two_le_center f.range)
  intro a ha
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨u,hu,heu⟩ := hx
  have hxa : x = ⟨u,(hK.trans (map_subtype_le _)) u.property⟩ := Subtype.ext heu.symm
  rw [hxa,action_secondary]
  rintro b ⟨y,hy,rfl⟩
  have hya : y = ⟨(⟨y,hy⟩ : secondary c),(hK.trans (map_subtype_le _)) hy⟩ := rfl
  rw [hya,action_secondary]
  have huC := hc (mem_map_of_mem f.rangeRestrict hu)
  have heq := congrArg (fun z : f.range => (z : Janko1.Model))
    (mem_center_iff.mp huC (f.rangeRestrict ⟨y,hy⟩))
  have heq' : secondaryProjection c C hK ⟨y,hy⟩ * secondaryProjection c C hK u =
      secondaryProjection c C hK u * secondaryProjection c C hK ⟨y,hy⟩ := by
    apply e.injective
    change f ⟨y,hy⟩ * f u = f u * f ⟨y,hy⟩ at heq
    simpa only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul] using heq
  simpa only [← map_mul] using congrArg (MulAut.conj : (C ⧸ pCore 2 C) →* MulAut _) heq'

include hK in
/-- Cubics cannot centralize the literal secondary image in the J₁ row. -/
theorem janko_prime_exclusion
    (hm : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ 2))
    (e : (C ⧸ pCore 2 C) ≃* Janko1.Model)
    {a : MulAut (C ⧸ pCore 2 C)}
    (ha : a ∈ centralizer (image c C (secondary c) : Set _)) : orderOf a ≠ 3 := by
  let H := (secondaryProjection c C hK).range
  let := secondaryProjection_perfect c C hK
  have hJ : center (C ⧸ pCore 2 C) = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hx' : e x ∈ center Janko1.Model := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
    rw [janko_center,mem_bot] at hx'
    exact e.injective (hx'.trans (map_one e).symm)
  apply inner_automorphism_orderOf_ne_prime_of_square_not_dvd H
    (three_dvd_secondaryProjection_card c C hK hm)
    (by rw [Nat.card_congr e.toEquiv,Janko1.card_model]; norm_num)
    (center_le_pCore_of_quotient_center_eq_bot (secondaryProjection_center_eq_bot c C hK hm))
    (by decide : Nat.Coprime 2 3) hJ a
  · rwa [← secondary_action_image c C hK]
  · obtain ⟨g,hg⟩ := Janko1.OuterCertificate.aut_inner (MulAut.congr e a)
    obtain ⟨x,hx⟩ := (MulAut.congr_inner_iff e a).mp ⟨g,hg.symm⟩
    exact ⟨x,hx.symm⟩

private theorem ternary_five_card {J : Type*} [Group J] (hm : ClassicalGroup.IsPSL J 3 5) :
    Nat.card J = 372000 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF]
  norm_num

include hK in
/-- In PSL₃(5), the A₅ quotient and ambient order force the projected two-core
to have order dividing eight. Perfectness then makes its action image central. -/
theorem coreImageCentral_of_ternary_five
    (hmodel : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ 2))
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 5) :
    image c C ((secondary c).pCoreIn 2) ≤ centralizer (image c C (secondary c) : Set _) := by
  apply coreImageCentral_of_projection_core_le_center c C hK
  let H := (secondaryProjection c C hK).range
  let := secondaryProjection_perfect c C hK
  obtain ⟨e⟩ := secondaryProjection_alternating_five c C hK hmodel
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (H ⧸ pCore 2 H) := e.isSimpleGroup
  have hquot : Nat.card (H ⧸ pCore 2 H) = 60 := secondaryProjection_quotient_card c C hK hmodel
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

include hK in
/-- Cubics cannot centralize the literal secondary image in the PSL₃(5) row. -/
theorem ternary_five_prime_exclusion [Group.IsPerfect (C ⧸ pCore 2 C)]
    (hmodel : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ 2))
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 5)
    {a : MulAut (C ⧸ pCore 2 C)}
    (ha : a ∈ centralizer (image c C (secondary c) : Set _)) : orderOf a ≠ 3 := by
  let J := C ⧸ pCore 2 C
  have hs : IsSimpleGroup J := by
    obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
    let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
    exact e.isSimpleGroup
  let := hs
  have hJ : center J = ⊥ := by
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp h)).elim
  let H := (secondaryProjection c C hK).range
  let := secondaryProjection_perfect c C hK
  intro horder
  have hout := ChapterA.Section03.SourceEmbeddings.linear_three_five_outer_two hm
  let q := QuotientGroup.mk' (MulAut.innerSubgroup J)
  have hqdiv : orderOf (q a) ∣ 3 := by simpa only [horder] using orderOf_map_dvd q a
  have hcop := hout.orderOf_coprime (by decide : Nat.Coprime 2 3) (q a)
  have hqone : q a = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hqdiv)
  exact inner_automorphism_orderOf_ne_prime_of_square_not_dvd H
    (three_dvd_secondaryProjection_card c C hK hmodel)
    (by rw [ternary_five_card hm]; norm_num)
    (center_le_pCore_of_quotient_center_eq_bot (secondaryProjection_center_eq_bot c C hK hmodel))
    (by decide : Nat.Coprime 2 3) hJ a
    (by rwa [← secondary_action_image c C hK])
    ((QuotientGroup.eq_one_iff a).mp hqone) horder

include hK in
/-- The two odd-model rows kill the original torus action without any movement
assumption on the whole radical or any assumed nontriviality of the torus image. -/
theorem odd_rows_torus_eq_bot [Group.IsPerfect (C ⧸ pCore 2 C)]
    (hmodel : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ 2))
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 5 ∨ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model))
    (Y : Subgroup G) (hY : Y ≤ rootNormalizer c) (hcard : Nat.card Y = 2 ^ 2 - 1)
    (hcomm : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2) : image c C Y = ⊥ := by
  have hc : image c C ((secondary c).pCoreIn 2) ≤ centralizer (image c C (secondary c) : Set _) := by
    rcases hm with hm | hj
    · exact coreImageCentral_of_ternary_five c C hK hmodel hm
    · exact coreImageCentral_of_janko c C hK (Classical.choice hj)
  apply torus_eq_bot_of_prime_centralizers c C (by decide : 0 < 2) Y
    (hK.trans (map_subtype_le _)) hY hcard hcomm hc
  intro p hp _ hd a _ ha horder
  have hp3 : p = 3 := by
    norm_num at hd
    exact (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left hp.ne_one
  rcases hm with hm | hj
  · exact ternary_five_prime_exclusion c C hK hmodel hm ha (horder.trans hp3)
  · exact janko_prime_exclusion c C hK hmodel (Classical.choice hj) ha (horder.trans hp3)

include hK in
/-- With the separately proved generation identity, the odd-model rows kill
the whole radical action, including its possible contribution outside K. -/
theorem odd_rows_radical_eq_bot [Group.IsPerfect (C ⧸ pCore 2 C)]
    (hmodel : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ 2))
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 5 ∨ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model))
    (Y : Subgroup G) (hR : R₂ c ≤ rootNormalizer c) (hY : Y ≤ rootNormalizer c)
    (hN : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (hcard : Nat.card Y = 2 ^ 2 - 1) (hcomm : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2)
    (hmoved : ⁅Q c,Y⁆ = Q c)
    (hgen : image c C (Q c) ⊔ ⁅image c C (R₂ c),image c C (secondary c)⁆ = image c C (R₂ c)) :
    image c C (R₂ c) = ⊥ := by
  have hc : image c C ((secondary c).pCoreIn 2) ≤ centralizer (image c C (secondary c) : Set _) := by
    rcases hm with hm | hj
    · exact coreImageCentral_of_ternary_five c C hK hmodel hm
    · exact coreImageCentral_of_janko c C hK (Classical.choice hj)
  exact radical_eq_bot_of_torus_eq_bot c C Y (hK.trans (map_subtype_le _)) hR hY hN hc hmoved hgen
    (odd_rows_torus_eq_bot c C hK hmodel hm Y hY hcard hcomm)

include hK in
/-- The source-correct exclusion of all three nonexceptional rows, conditional
only on their actual model, original geometry, and whole-radical generation. -/
theorem nonexceptional_radical_eq_bot [Group.IsPerfect (C ⧸ pCore 2 C)] {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n))
    (hm : NonexceptionalModel (C ⧸ pCore 2 C) n)
    (Y : Subgroup G) (hR : R₂ c ≤ rootNormalizer c) (hY : Y ≤ rootNormalizer c)
    (hN : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (hcard : Nat.card Y = 2 ^ n - 1) (hcomm : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2)
    (hmoved : ⁅Q c,Y⁆ = Q c)
    (hgen : image c C (Q c) ⊔ ⁅image c C (R₂ c),image c C (secondary c)⁆ = image c C (R₂ c)) :
    image c C (R₂ c) = ⊥ := by
  have hne := secondaryImage_ne_bot c C hK hmodel
  rcases hm with ⟨i,_,hi⟩ | hu | ⟨rfl,ho⟩
  · exact binary_radical_eq_bot c C hi Y hK hR hY hN hne hcomm hmoved hgen
  · exact unitary_radical_eq_bot c C hn hu Y hK hR hY hN hne hmoved hgen
  · exact odd_rows_radical_eq_bot c C hK hmodel ho Y hR hY hN hcard hcomm hmoved hgen

include hK in
/-- Conditional exceptional-model assembly with all model-centralizer and
core-centrality premises discharged. The four-row inspection and whole-radical
generation remain explicit mathematical obligations of the source assembly. -/
theorem exceptional_of_models_and_generation [Group.IsPerfect (C ⧸ pCore 2 C)] {n : ℕ}
    (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n))
    (Y : Subgroup G) (hR : R₂ c ≤ rootNormalizer c) (hY : Y ≤ rootNormalizer c)
    (hN : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (hcard : Nat.card Y = 2 ^ n - 1) (hcomm : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2)
    (hmoved : ⁅Q c,Y⁆ = Q c)
    (hgen : image c C (Q c) ⊔ ⁅image c C (R₂ c),image c C (secondary c)⁆ = image c C (R₂ c))
    (hrad : image c C (R₂ c) ≠ ⊥)
    (hm : NonexceptionalModel (C ⧸ pCore 2 C) n ∨
      (ExceptionalModel (C ⧸ pCore 2 C) n ∧
        image c C Y ⊓ MulAut.innerSubgroup (C ⧸ pCore 2 C) = ⊥)) :
    ExceptionalModel (C ⧸ pCore 2 C) n ∧
      image c C Y ⊓ MulAut.innerSubgroup (C ⧸ pCore 2 C) = ⊥ := by
  rcases hm with hm | hm
  · exact (hrad (nonexceptional_radical_eq_bot c C hK hn hmodel hm Y hR hY hN hcard hcomm hmoved hgen)).elim
  · exact hm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve.SourceImages
