module

public import Stellmacher.SectionEight.ThreePlaneOrbitNoncommutation

namespace Stellmacher.SectionEight

open Later
open scoped commutatorElement

universe u

private theorem common_generator
    {G : Type u} [Group G] (common : Subgroup G)
    (hcard : Nat.card common = 2) :
    ∃ involution : G, involution ∈ common ∧ involution ≠ 1 ∧
      ∀ element ∈ common, element = 1 ∨ element = involution := by
  obtain ⟨involution, hne, hunique⟩ := (Nat.card_eq_two_iff' (1 : common)).mp hcard
  refine ⟨involution, involution.property, ?_, ?_⟩
  · intro heq
    exact hne (Subtype.ext heq)
  · intro element helement
    by_cases hone : element = 1
    · exact Or.inl hone
    · exact Or.inr (congrArg Subtype.val (hunique ⟨element, helement⟩
        (fun heq => hone (congrArg Subtype.val heq))))

private theorem plane_generator
    {G : Type u} [Group G] [Finite G] (plane common : Subgroup G)
    (hplane : Nat.card plane = 4) (hcommon : Nat.card common = 2)
    (hle : common ≤ plane) (involution : G) (hinvolution : involution ∈ common)
    (hunique : ∀ element ∈ common, element = 1 ∨ element = involution) :
    ∃ generator : G, generator ∈ plane ∧ generator ∉ common ∧
      plane = Subgroup.closure ({generator, involution} : Set G) := by
  have hnotle : ¬ plane ≤ common := by
    intro hreverse
    have hcard := Subgroup.card_le_of_le hreverse
    omega
  obtain ⟨generator, hgenerator, houtside⟩ := SetLike.not_le_iff_exists.mp hnotle
  let generated := Subgroup.closure ({generator, involution} : Set G)
  have hgeneratorMem : generator ∈ generated := Subgroup.subset_closure (by simp)
  have hinvolutionMem : involution ∈ generated := Subgroup.subset_closure (by simp)
  have hcommonLe : common ≤ generated := by
    intro element helement
    rcases hunique element helement with rfl | rfl
    · exact generated.one_mem
    · exact hinvolutionMem
  have hgeneratedLe : generated ≤ plane := by
    apply (Subgroup.closure_le _).mpr
    intro element helement
    rcases Set.mem_insert_iff.mp helement with rfl | helement
    · exact hgenerator
    · exact Set.mem_singleton_iff.mp helement ▸ hle hinvolution
  have hgreater : 2 < Nat.card generated := by
    by_contra hnot
    have hequal : common = generated :=
      Subgroup.eq_of_le_of_card_ge hcommonLe (by omega)
    exact houtside (hequal ▸ hgeneratorMem)
  have hbound : Nat.card generated ≤ 4 := by
    simpa [hplane] using Subgroup.card_le_of_le hgeneratedLe
  have hdiv : Nat.card generated ∣ 4 := by
    simpa [hplane] using Subgroup.card_dvd_of_le hgeneratedLe
  have hfour : Nat.card generated = 4 := by
    have hcases : Nat.card generated = 3 ∨ Nat.card generated = 4 := by omega
    rcases hcases with hthree | hfour
    · norm_num [hthree] at hdiv
    · exact hfour
  exact ⟨generator, hgenerator, houtside,
    (Subgroup.eq_of_le_of_card_ge hgeneratedLe (by omega)).symm⟩

private theorem generators_not_commute
    {G : Type u} [Group G] (firstPlane secondPlane : Subgroup G)
    (first second involution : G)
    (hfirst : firstPlane = Subgroup.closure ({first, involution} : Set G))
    (hsecond : secondPlane = Subgroup.closure ({second, involution} : Set G))
    (hcentralFirst : Commute involution first)
    (hcentralSecond : Commute involution second)
    (hnoncommute : ⁅firstPlane, secondPlane⁆ ≠ ⊥) : ¬ Commute first second := by
  intro hcommute
  apply hnoncommute
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, hfirst, hsecond,
    Subgroup.centralizer_closure]
  apply (Subgroup.closure_le _).mpr
  intro element helement
  rcases Set.mem_insert_iff.mp helement with rfl | helement
  · intro other hother
    rcases Set.mem_insert_iff.mp hother with rfl | hother
    · exact hcommute.symm.eq
    · exact Set.mem_singleton_iff.mp hother ▸ hcentralFirst.eq
  · have heq := Set.mem_singleton_iff.mp helement
    subst element
    intro other hother
    rcases Set.mem_insert_iff.mp hother with rfl | hother
    · exact hcentralSecond.symm.eq
    · exact Set.mem_singleton_iff.mp hother ▸ rfl

private theorem pair_square_eq_common
    {G : Type u} [Group G] (whole common : Subgroup G)
    (hderived : ⁅whole, whole⁆ = common) (first second involution : G)
    (hfirst : first ^ 2 = 1) (hsecond : second ^ 2 = 1)
    (hfirstMem : first ∈ whole) (hsecondMem : second ∈ whole)
    (hunique : ∀ element ∈ common, element = 1 ∨ element = involution)
    (hnoncommute : ¬ Commute first second) : (first * second) ^ 2 = involution := by
  have hfirstInv : first⁻¹ = first :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hfirst)
  have hsecondInv : second⁻¹ = second :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsecond)
  have hidentity : ⁅first, second⁆ = (first * second) ^ 2 := by
    simp only [commutatorElement_def, hfirstInv, hsecondInv, pow_two, mul_assoc]
  have hmem : (first * second) ^ 2 ∈ common := by
    rw [← hderived, ← hidentity]
    exact Subgroup.commutator_mem_commutator hfirstMem hsecondMem
  rcases hunique _ hmem with hone | hequal
  · apply False.elim
    apply hnoncommute
    have hproductInv : (first * second)⁻¹ = first * second :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hone)
    exact (show first * second = second * first by
      simpa only [mul_inv_rev, hfirstInv, hsecondInv] using hproductInv.symm)
  · exact hequal

public theorem three_plane_generators_of_pairwise_noncommuting
    {G : Type u} [Group G] [Finite G]
    (seed secondPlane thirdPlane common whole : Subgroup G)
    (hseedElementary : IsElementaryAbelian 2 seed)
    (hsecondElementary : IsElementaryAbelian 2 secondPlane)
    (hthirdElementary : IsElementaryAbelian 2 thirdPlane)
    (hseedCard : Nat.card seed = 4) (hsecondCard : Nat.card secondPlane = 4)
    (hthirdCard : Nat.card thirdPlane = 4) (hcommonCard : Nat.card common = 2)
    (hcommonSeed : common ≤ seed) (hcommonSecond : common ≤ secondPlane)
    (hcommonThird : common ≤ thirdPlane)
    (hcentral : whole ≤ Subgroup.centralizer (common : Set G))
    (hgeneration : whole = seed ⊔ secondPlane ⊔ thirdPlane)
    (hderived : ⁅whole, whole⁆ = common)
    (hseedSecond : ⁅seed, secondPlane⁆ ≠ ⊥)
    (hsecondThird : ⁅secondPlane, thirdPlane⁆ ≠ ⊥)
    (hseedThird : ⁅seed, thirdPlane⁆ ≠ ⊥) :
    ∃ first second third involution : G,
      first ^ 2 = 1 ∧ second ^ 2 = 1 ∧ third ^ 2 = 1 ∧ involution ^ 2 = 1 ∧
      involution ≠ 1 ∧ Commute involution first ∧ Commute involution second ∧
      Commute involution third ∧ (first * second) ^ 2 = involution ∧
      (second * third) ^ 2 = involution ∧ (first * third) ^ 2 = involution ∧
      whole = Subgroup.closure ({first, second, third} : Set G) ∧
      seed = Subgroup.closure ({first, involution} : Set G) := by
  let _ := hseedElementary
  let _ := hsecondElementary
  let _ := hthirdElementary
  obtain ⟨involution, hinvolution, hne, hunique⟩ := common_generator common hcommonCard
  obtain ⟨first, hfirstMem, _, hfirstGeneration⟩ :=
    plane_generator seed common hseedCard hcommonCard hcommonSeed involution
      hinvolution hunique
  obtain ⟨second, hsecondMem, _, hsecondGeneration⟩ :=
    plane_generator secondPlane common hsecondCard hcommonCard hcommonSecond involution
      hinvolution hunique
  obtain ⟨third, hthirdMem, _, hthirdGeneration⟩ :=
    plane_generator thirdPlane common hthirdCard hcommonCard hcommonThird involution
      hinvolution hunique
  have hfirst : first ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian first hfirstMem
  have hsecond : second ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian second hsecondMem
  have hthird : third ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian third hthirdMem
  have hinvolutionSquare : involution ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian involution (hcommonSeed hinvolution)
  have hseedLe : seed ≤ whole := hgeneration ▸ le_sup_of_le_left le_sup_left
  have hsecondLe : secondPlane ≤ whole := hgeneration ▸ le_sup_of_le_left le_sup_right
  have hthirdLe : thirdPlane ≤ whole := hgeneration ▸ le_sup_right
  have hfirstWhole := hseedLe hfirstMem
  have hsecondWhole := hsecondLe hsecondMem
  have hthirdWhole := hthirdLe hthirdMem
  have hcentralFirst : Commute involution first := hcentral hfirstWhole involution hinvolution
  have hcentralSecond : Commute involution second := hcentral hsecondWhole involution hinvolution
  have hcentralThird : Commute involution third := hcentral hthirdWhole involution hinvolution
  have hfirstSecond := pair_square_eq_common whole common hderived first second involution
    hfirst hsecond hfirstWhole hsecondWhole hunique
    (generators_not_commute seed secondPlane first second involution hfirstGeneration
      hsecondGeneration hcentralFirst hcentralSecond hseedSecond)
  have hsecondThirdSquare := pair_square_eq_common whole common hderived second third involution
    hsecond hthird hsecondWhole hthirdWhole hunique
    (generators_not_commute secondPlane thirdPlane second third involution hsecondGeneration
      hthirdGeneration hcentralSecond hcentralThird hsecondThird)
  have hfirstThird := pair_square_eq_common whole common hderived first third involution
    hfirst hthird hfirstWhole hthirdWhole hunique
    (generators_not_commute seed thirdPlane first third involution hfirstGeneration
      hthirdGeneration hcentralFirst hcentralThird hseedThird)
  refine ⟨first, second, third, involution, hfirst, hsecond, hthird, hinvolutionSquare,
    hne, hcentralFirst, hcentralSecond, hcentralThird, hfirstSecond,
    hsecondThirdSquare, hfirstThird, ?_, hfirstGeneration⟩
  let generated := Subgroup.closure ({first, second, third} : Set G)
  have hfirstGenerated : first ∈ generated := Subgroup.subset_closure (by simp)
  have hsecondGenerated : second ∈ generated := Subgroup.subset_closure (by simp)
  have hthirdGenerated : third ∈ generated := Subgroup.subset_closure (by simp)
  have hinvolutionGenerated : involution ∈ generated := by
    rw [← hfirstSecond]
    exact generated.pow_mem (generated.mul_mem hfirstGenerated hsecondGenerated) 2
  apply le_antisymm
  · rw [hgeneration]
    apply sup_le
    · apply sup_le
      · rw [hfirstGeneration]
        exact (Subgroup.closure_le _).mpr (by
          intro element helement
          rcases Set.mem_insert_iff.mp helement with rfl | helement
          · exact hfirstGenerated
          · exact Set.mem_singleton_iff.mp helement ▸ hinvolutionGenerated)
      · rw [hsecondGeneration]
        exact (Subgroup.closure_le _).mpr (by
          intro element helement
          rcases Set.mem_insert_iff.mp helement with rfl | helement
          · exact hsecondGenerated
          · exact Set.mem_singleton_iff.mp helement ▸ hinvolutionGenerated)
    · rw [hthirdGeneration]
      exact (Subgroup.closure_le _).mpr (by
        intro element helement
        rcases Set.mem_insert_iff.mp helement with rfl | helement
        · exact hthirdGenerated
        · exact Set.mem_singleton_iff.mp helement ▸ hinvolutionGenerated)
  · apply (Subgroup.closure_le _).mpr
    intro element helement
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at helement
    rcases helement with rfl | rfl | rfl
    · exact hfirstWhole
    · exact hsecondWhole
    · exact hthirdWhole

public theorem three_plane_involution_generators
    {G : Type u} [Group G] [Finite G]
    (seed actors common whole : Subgroup G)
    (hseedActors : seed ≤ actors)
    (helementary : IsElementaryAbelian 2 seed)
    (hseedCard : Nat.card seed = 4)
    (hcommonCard : Nat.card common = 2)
    (hcommonSeed : common ≤ seed)
    (hcentral : actors ≤ Subgroup.centralizer (common : Set G))
    (hgeneration : whole = conjugateClosure seed actors)
    (hderived : ⁅whole, whole⁆ = common)
    (horbit : ((Subgroup.normalizer (seed : Set G)).subgroupOf actors).index = 3)
    (hsmall : Nat.card whole ≤ 16) :
    ∃ first second third involution : G,
      first ^ 2 = 1 ∧ second ^ 2 = 1 ∧ third ^ 2 = 1 ∧ involution ^ 2 = 1 ∧
      involution ≠ 1 ∧ Commute involution first ∧ Commute involution second ∧
      Commute involution third ∧ (first * second) ^ 2 = involution ∧
      (second * third) ^ 2 = involution ∧ (first * third) ^ 2 = involution ∧
      whole = Subgroup.closure ({first, second, third} : Set G) ∧
      seed = Subgroup.closure ({first, involution} : Set G) := by
  obtain ⟨secondPlane, thirdPlane, hsecondElementary, hthirdElementary, hsecondCard,
    hthirdCard, hcommonSecond, hcommonThird, hjoin, hseedSecond, hsecondThird,
    hseedThird⟩ := three_plane_pairwise_noncommuting_geometry seed actors common whole
      hseedActors helementary hseedCard hcommonCard hcommonSeed hcentral hgeneration
      hderived horbit hsmall
  have hwholeActors : whole ≤ actors := by
    rw [hgeneration, conjugateClosure]
    apply (Subgroup.closure_le _).mpr
    rintro element ⟨actor, representative, rfl⟩
    exact actors.mul_mem (actors.mul_mem actor.property
      (hseedActors representative.property)) (actors.inv_mem actor.property)
  exact three_plane_generators_of_pairwise_noncommuting seed secondPlane thirdPlane
    common whole helementary hsecondElementary hthirdElementary hseedCard hsecondCard
    hthirdCard hcommonCard hcommonSeed hcommonSecond hcommonThird
    (hwholeActors.trans hcentral) hjoin hderived hseedSecond hsecondThird hseedThird

end Stellmacher.SectionEight
