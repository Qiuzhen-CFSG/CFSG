module

public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexSetup
public import Theory.GroupTheory.NormalizedSupCard

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u v

public structure EightSixSmallIndexNextData
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph) : Prop where
  next_quotient : QuotientIsModel (GAt graph path.firstStep)
    (QAt graph path.firstStep) SL2Two
  next_v : IsCentralProductModel (VAt graph path.firstStep) C4 Q8
  intersection : IsModel (VAt graph path.firstStep ⊓ QAt graph path.a) (C2 × C4)
  next_core : (IsCentralProductModel (QAt graph path.firstStep) C4 Q8 ∨
    IsCentralProductQ8Q8 (QAt graph path.firstStep)) ∧
    IsModel (QAt graph path.firstStep ⊓ EAt graph path.firstStep) Q8

public theorem eight_six_three_four_subgroups_card_le
    {G : Type u} [Group G] [Finite G]
    (left middle right common whole : Subgroup G)
    (hwhole : whole = left ⊔ middle ⊔ right)
    (hleft : Nat.card left = 4) (hmiddle : Nat.card middle = 4)
    (hright : Nat.card right = 4) (hcommon : Nat.card common = 2)
    (hcommon_left : common ≤ left) (hcommon_middle : common ≤ middle)
    (hcommon_right : common ≤ right)
    (hcommutator : ⁅whole, whole⁆ ≤ common) : Nat.card whole ≤ 16 := by
  have hleft_whole : left ≤ whole := hwhole ▸ le_sup_of_le_left le_sup_left
  have hmiddle_whole : middle ≤ whole := hwhole ▸ le_sup_of_le_left le_sup_right
  have hright_whole : right ≤ whole := hwhole ▸ le_sup_right
  have hpair_whole : left ⊔ middle ≤ whole := sup_le hleft_whole hmiddle_whole
  have hnormalize_pair : middle ≤ Subgroup.normalizer (left : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hleft_whole hmiddle_whole).trans
        (hcommutator.trans hcommon_left))
  have hnormalize_whole : right ≤ Subgroup.normalizer (↑(left ⊔ middle) : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hpair_whole hright_whole).trans
        (hcommutator.trans (hcommon_left.trans le_sup_left)))
  have hfirst_intersection : 2 ≤ Nat.card (left ⊓ middle : Subgroup G) := by
    rw [← hcommon]
    exact Subgroup.card_le_of_le (le_inf hcommon_left hcommon_middle)
  have hsecond_intersection : 2 ≤ Nat.card ((left ⊔ middle) ⊓ right : Subgroup G) := by
    rw [← hcommon]
    exact Subgroup.card_le_of_le (le_inf (hcommon_left.trans le_sup_left) hcommon_right)
  have hpair_card := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    left middle hnormalize_pair
  have hwhole_card := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (left ⊔ middle) right hnormalize_whole
  rw [hleft, hmiddle] at hpair_card
  rw [hright, ← hwhole] at hwhole_card
  have hpair_bound : Nat.card (left ⊔ middle : Subgroup G) ≤ 8 := by nlinarith
  nlinarith

public theorem eight_six_three_conjugates_card_le
    {G : Type u} [Group G] [Finite G]
    (seed actors common : Subgroup G) (first second third : actors)
    (hseed : Nat.card seed = 4) (hcommon : Nat.card common = 2)
    (hfirst : common ≤ conjugateBy seed first)
    (hsecond : common ≤ conjugateBy seed second)
    (hthird : common ≤ conjugateBy seed third)
    (hconjugates : ∀ actor : actors,
      conjugateBy seed actor = conjugateBy seed first ∨
      conjugateBy seed actor = conjugateBy seed second ∨
      conjugateBy seed actor = conjugateBy seed third)
    (hcommutator : ⁅conjugateClosure seed actors, conjugateClosure seed actors⁆ ≤ common) :
    Nat.card (conjugateClosure seed actors) ≤ 16 := by
  have hconjugate_le (actor : actors) :
      conjugateBy seed actor ≤ conjugateClosure seed actors := by
    rintro element ⟨representative, hrepresentative, rfl⟩
    exact Subgroup.subset_closure ⟨actor, ⟨representative, hrepresentative⟩, rfl⟩
  have hwhole : conjugateClosure seed actors =
      conjugateBy seed first ⊔ conjugateBy seed second ⊔ conjugateBy seed third := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      rintro element ⟨actor, representative, rfl⟩
      have hmem : (actor : G) * (representative : G) * (actor : G)⁻¹ ∈
          conjugateBy seed actor :=
        Subgroup.mem_map.mpr ⟨representative, representative.property, rfl⟩
      rcases hconjugates actor with hequal | hequal | hequal
      · rw [hequal] at hmem
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hmem)
      · rw [hequal] at hmem
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hmem)
      · rw [hequal] at hmem
        exact Subgroup.mem_sup_right hmem
    · exact sup_le (sup_le (hconjugate_le first) (hconjugate_le second))
        (hconjugate_le third)
  have hcard (actor : actors) : Nat.card (conjugateBy seed actor) = 4 := by
    unfold conjugateBy
    rw [Subgroup.card_map_of_injective (MulAut.conj (actor : G)).injective, hseed]
  exact eight_six_three_four_subgroups_card_le _ _ _ _ _ hwhole
    (hcard first) (hcard second) (hcard third) hcommon hfirst hsecond hthird hcommutator

public theorem eight_six_central_product_card
    {G : Type u} [Group G] [Finite G]
    {N K : Type v} [Group N] [Group K]
    {whole : Subgroup G} (hmodel : IsCentralProductModel whole N K) :
    Nat.card N * Nat.card K = 2 * Nat.card whole := by
  obtain ⟨left, right, ⟨leftModel⟩, ⟨rightModel⟩, rfl, hintersection, hcommute, _⟩ := hmodel
  have hnormalize : right ≤ Subgroup.normalizer (left : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro actor hactor element helement
    exact hcommute element helement actor hactor
  have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    left right hnormalize
  rwa [Nat.card_congr leftModel.toEquiv, Nat.card_congr rightModel.toEquiv,
    hintersection] at hcard

public theorem eight_six_c4_quaternion_card
    {G : Type u} [Group G] [Finite G]
    {whole : Subgroup G} (hmodel : IsCentralProductModel whole C4 Q8) :
    Nat.card whole = 16 := by
  have hcard := eight_six_central_product_card hmodel
  have hcyclic : Nat.card C4 = 4 := by
    change Nat.card (Multiplicative (ZMod 4)) = 4
    simp
  have hquaternion : Nat.card Q8 = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [hcyclic, hquaternion] at hcard
  omega

public theorem eight_six_quaternion_quaternion_card
    {G : Type u} [Group G] [Finite G]
    {whole : Subgroup G} (hmodel : IsCentralProductQ8Q8 whole) :
    Nat.card whole = 32 := by
  have hcard := eight_six_central_product_card
    (show IsCentralProductModel whole Q8 Q8 from hmodel)
  have hquaternion : Nat.card Q8 = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [hquaternion] at hcard
  omega

public theorem eight_six_generated_trivially_of_card_sixteen
    {G : Type u} [Group G] [Finite G]
    {core whole : Subgroup G} (hle : core ≤ whole)
    (hmodel : IsModel core (C4 × C4)) (hcard : Nat.card whole = 16) :
    ∃ actor : G, (actor = 1 ∨ IsInvertingOn actor core) ∧
      whole = GeneratedWith core actor := by
  obtain ⟨model⟩ := hmodel
  have hcore : Nat.card core = 16 := by
    rw [Nat.card_congr model.toEquiv, Nat.card_prod]
    simp [C4]
  have hequal : core = whole := Subgroup.eq_of_le_of_card_ge hle (by omega)
  refine ⟨1, Or.inl rfl, ?_⟩
  simp [GeneratedWith, hequal]

public theorem eight_six_models_of_next_and_initial
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (Q : Subgroup G) (next : EightSixSmallIndexNextData graph path)
    (hcore : IsModel (twoCoreIn (EAt graph path.a)) (C4 × C4))
    (hgenerated : ∃ actor : G,
      (actor = 1 ∨ IsInvertingOn actor (twoCoreIn (EAt graph path.a))) ∧
      Q = GeneratedWith (twoCoreIn (EAt graph path.a)) actor) :
    EightSixSmallIndexModelData graph path Q :=
  ⟨next.next_quotient, hcore, hgenerated, next.next_core⟩

end Stellmacher.SectionEight
