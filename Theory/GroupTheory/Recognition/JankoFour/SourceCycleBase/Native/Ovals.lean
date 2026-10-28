module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Polar
/-!
# The six dual ovals and the disc alternative

The fifteen singular lines of the binary symplectic residue identify with
pairs of the six ovals. Collinearity becomes disjointness of these pairs.
A pairwise intersecting family of at least four pairs is a star, proving
that the six displayed ovals are complete. The incidence degree sum then
proves the disc-or-nine alternative: three neighbors at each touched oval
force four or six touched ovals; four gives the disc of the complementary
pair. Only the small labelled incidence table is checked by reduction.

Source: Aschbacher–Segev (1991), (2.1)–(2.2) and duality (2.3), p.592.
The point-plane flag consumer is in `SourceCycleBase.ResidueOvals`.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Polar
open Theory.SpecificGroups.SymmetricSix
open Finset

def ovalTable : Fin 6 → Finset Syntheme :=
  ![{0,4,8,10,12}, {0,5,7,9,13}, {1,3,7,11,12},
    {1,5,6,10,14}, {2,3,8,9,14}, {2,4,6,11,13}]

theorem ovalTable_oval (i : Fin 6) : Oval (ovalTable i) := by
  unfold Oval
  decide +revert

def ovalPair (s : Syntheme) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => s ∈ ovalTable i)

theorem ovalPair_card (s : Syntheme) : (ovalPair s).card = 2 := by decide +revert

theorem ovalPair_injective : Function.Injective ovalPair := by decide

theorem ovalPair_surjective (s : Finset (Fin 6)) (hs : s.card = 2) :
    ∃ a, ovalPair a = s := by
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hs
  have h : ∀ i j : Fin 6, i ≠ j → ∃ a, ovalPair a = {i,j} := by decide
  exact h i j hij

theorem collinear_iff_ovalPair_disjoint (s t : Syntheme) :
    synthemeCollinear s t ↔ Disjoint (ovalPair s) (ovalPair t) := by decide +revert

def touched (S : Finset Syntheme) : Finset (Fin 6) := S.biUnion ovalPair

theorem mem_touched (S : Finset Syntheme) (i : Fin 6) :
    i ∈ touched S ↔ (ovalTable i ∩ S).Nonempty := by
  simp only [touched, Finset.mem_biUnion, ovalPair, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.nonempty_def, Finset.mem_inter]
  exact exists_congr fun _ => and_comm

theorem oval_degree_sum (S : Finset Syntheme) :
    (∑ i : Fin 6, (ovalTable i ∩ S).card) = 2 * S.card := by
  calc
    _ = ∑ i : Fin 6, ∑ s ∈ S, if s ∈ ovalTable i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.card_filter]
      congr 1
      ext s
      simp [and_comm]
    _ = ∑ s ∈ S, ∑ i : Fin 6, if s ∈ ovalTable i then 1 else 0 := Finset.sum_comm
    _ = ∑ s ∈ S, (ovalPair s).card := by simp only [ovalPair, Finset.card_filter]
    _ = _ := by simp [ovalPair_card, Nat.mul_comm]

theorem degree_sum_of_three (S : Finset Syntheme)
    (hit : ∀ i, (ovalTable i ∩ S).Nonempty → (ovalTable i ∩ S).card = 3) :
    2 * S.card = 3 * (touched S).card := by
  rw [← oval_degree_sum]
  calc
    _ = ∑ i : Fin 6, if i ∈ touched S then 3 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ touched S
      · rw [if_pos hi, hit i ((mem_touched S i).mp hi)]
      · rw [if_neg hi]
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp
          (fun h => hi ((mem_touched S i).mpr h)))
    _ = _ := by simp [Nat.mul_comm]

theorem oval_neighbor_bound (S : Finset Syntheme) (i : Fin 6) :
    (ovalTable i ∩ S).card ≤ ((touched S).erase i).card := by
  classical
  have mate (s : Syntheme) (hs : s ∈ ovalTable i ∩ S) : ∃! j, j ∈ ovalPair s ∧ j ≠ i := by
    have hi : i ∈ ovalPair s := by simpa [ovalPair] using (Finset.mem_inter.mp hs).1
    have hc : ((ovalPair s).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, ovalPair_card]
    obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hc
    refine ⟨j, ?_, ?_⟩
    · have hm : j ∈ (ovalPair s).erase i := hj.symm ▸ Finset.mem_singleton_self j
      exact ⟨(Finset.mem_erase.mp hm).2, (Finset.mem_erase.mp hm).1⟩
    · rintro k ⟨hk,hki⟩
      have hm : k ∈ (ovalPair s).erase i := Finset.mem_erase.mpr ⟨hki,hk⟩
      simpa [hj] using hm
  let f : {s // s ∈ ovalTable i ∩ S} → {j // j ∈ (touched S).erase i} := fun s =>
    ⟨(mate s.val s.property).choose, Finset.mem_erase.mpr
      ⟨(mate s.val s.property).choose_spec.1.2,
        Finset.mem_biUnion.mpr ⟨s.val,(Finset.mem_inter.mp s.property).2,
          (mate s.val s.property).choose_spec.1.1⟩⟩⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro s t he
  apply Subtype.ext
  apply ovalPair_injective
  have pair (s : {s // s ∈ ovalTable i ∩ S}) : ovalPair s.val = {i, (f s).val} := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      by_cases hji : j = i
      · simp [hji]
      · have hm := (mate s.val s.property).choose_spec.2 j ⟨hj,hji⟩
        exact Finset.mem_insert_of_mem (by simpa only [Finset.mem_singleton] using hm)
    · rw [ovalPair_card]
      exact Finset.card_le_two (a := i) (b := (f s).val)
  rw [pair s, pair t, he]


theorem oval_hitting_classification (S : Finset Syntheme) (hne : S.Nonempty)
    (hit : ∀ i, (ovalTable i ∩ S).Nonempty → (ovalTable i ∩ S).card = 3) :
    (∃ s, S = disc s) ∨ S.card = 9 := by
  classical
  let A := touched S
  have hsum := degree_sum_of_three S hit
  have hlow (i : Fin 6) (hi : i ∈ A) : 4 ≤ A.card := by
    have hdeg := hit i ((mem_touched S i).mp hi)
    have hbound := oval_neighbor_bound S i
    rw [hdeg] at hbound
    have hcard : (A.erase i).card + 1 = A.card := Finset.card_erase_add_one hi
    change 3 ≤ (A.erase i).card at hbound
    omega
  have hAlo : 4 ≤ A.card := by
    obtain ⟨s,hs⟩ := hne
    have hnepair : (ovalPair s).Nonempty := Finset.card_pos.mp (by rw [ovalPair_card]; decide)
    obtain ⟨i,hi⟩ := hnepair
    exact hlow i (Finset.mem_biUnion.mpr ⟨s,hs,hi⟩)
  have hAhi : A.card ≤ 6 := by
    calc A.card ≤ (Finset.univ : Finset (Fin 6)).card := Finset.card_le_univ _
         _ = 6 := by decide
  have hcase : A.card = 4 ∨ A.card = 6 := by change 2 * S.card = 3 * A.card at hsum; omega
  rcases hcase with hA4 | hA6
  · left
    let C := Aᶜ
    have hCcard : C.card = 2 := by simp [C,Finset.card_compl,hA4]
    obtain ⟨e,he⟩ := ovalPair_surjective C hCcard
    refine ⟨e, Finset.eq_of_subset_of_card_le ?_ ?_⟩
    · intro s hs
      simp only [disc,Finset.mem_filter,Finset.mem_univ,true_and]
      rw [collinear_iff_ovalPair_disjoint,he]
      apply Finset.disjoint_left.mpr
      intro i hC hi
      have hiA : i ∈ A := Finset.mem_biUnion.mpr ⟨s,hs,hi⟩
      exact (Finset.mem_compl.mp hC) hiA
    · rw [disc_card]
      change 2 * S.card = 3 * A.card at hsum
      omega
  · right
    change 2 * S.card = 3 * A.card at hsum
    omega


private theorem pair_partner (s : Syntheme) (i : Fin 6) (hi : i ∈ ovalPair s) :
    ∃ j, j ≠ i ∧ ovalPair s = {i,j} := by
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp (ovalPair_card s)
  have hi' : i = a ∨ i = b := by simpa [he] using hi
  rcases hi' with rfl | rfl
  · exact ⟨b,hab.symm,he⟩
  · exact ⟨a,hab,by rw [he,Finset.pair_comm]⟩

private theorem intersects_pair {a : Finset (Fin 6)} {i j : Fin 6}
    (h : ¬Disjoint a {i,j}) : i ∈ a ∨ j ∈ a := by
  by_contra! hn
  apply h
  exact Finset.disjoint_left.mpr fun k hk hk' =>
    (by simpa using hk' : k = i ∨ k = j).elim
      (fun he => hn.1 (he ▸ hk)) (fun he => hn.2 (he ▸ hk))

private theorem pair_eq_of_two_mem {s : Syntheme} {i j : Fin 6}
    (hij : i ≠ j) (hi : i ∈ ovalPair s) (hj : j ∈ ovalPair s) : ovalPair s = {i,j} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · simpa using (show {i,j} ⊆ ovalPair s from fun k hk =>
      (by simpa using hk : k = i ∨ k = j).elim (fun he => he ▸ hi) (fun he => he ▸ hj))
  · rw [ovalPair_card,Finset.card_pair hij]

theorem ovalTable_complete {S : Finset Syntheme} (hS : Oval S) : ∃ i, S = ovalTable i := by
  classical
  have hinter : ∀ s ∈ S, ∀ t ∈ S, ¬Disjoint (ovalPair s) (ovalPair t) := by
    intro s hs t ht hd
    have hst := (collinear_iff_ovalPair_disjoint s t).mpr hd
    obtain ⟨hne,a,has,hat⟩ := (syntheme_collinear_iff_common_duad s t).mp hst
    exact Finset.disjoint_left.mp (hS.2 s hs t ht hne) has hat
  obtain ⟨s,hs,t,ht,hst⟩ := Finset.one_lt_card.mp (by rw [hS.1]; decide)
  have hshare : (ovalPair s ∩ ovalPair t).Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp (hinter s hs t ht)
  obtain ⟨i,hi⟩ := hshare
  obtain ⟨j,hji,heS⟩ := pair_partner s i (Finset.mem_inter.mp hi).1
  obtain ⟨k,hki,heT⟩ := pair_partner t i (Finset.mem_inter.mp hi).2
  have hjk : j ≠ k := by
    intro he
    exact hst (ovalPair_injective (by rw [heS,heT,he]))
  have hstar : ∀ v ∈ S, i ∈ ovalPair v := by
    by_contra! hn
    obtain ⟨u,hu,hiu⟩ := hn
    have hju : j ∈ ovalPair u :=
      (intersects_pair (by rw [← heS]; exact hinter u hu s hs)).resolve_left hiu
    have hku : k ∈ ovalPair u :=
      (intersects_pair (by rw [← heT]; exact hinter u hu t ht)).resolve_left hiu
    have heU := pair_eq_of_two_mem hjk hju hku
    have hsub : S ⊆ {s,t,u} := by
      intro v hv
      have hvU := intersects_pair (by rw [← heU]; exact hinter v hv u hu)
      have hvS := intersects_pair (by rw [← heS]; exact hinter v hv s hs)
      have hvT := intersects_pair (by rw [← heT]; exact hinter v hv t ht)
      have hcase : v = s ∨ v = t ∨ v = u := by
        by_cases hvj : j ∈ ovalPair v
        · by_cases hvk : k ∈ ovalPair v
          · exact Or.inr (Or.inr (ovalPair_injective ((pair_eq_of_two_mem hjk hvj hvk).trans heU.symm)))
          · have hvi := hvT.resolve_right hvk
            exact Or.inl (ovalPair_injective ((pair_eq_of_two_mem hji.symm hvi hvj).trans heS.symm))
        · have hvk := hvU.resolve_left hvj
          have hvi := hvS.resolve_right hvj
          exact Or.inr (Or.inl (ovalPair_injective ((pair_eq_of_two_mem hki.symm hvi hvk).trans heT.symm)))
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hcase
    have hc := Finset.card_le_card hsub
    have hc' : ({s,t,u} : Finset Syntheme).card ≤ 3 := Finset.card_le_three
    rw [hS.1] at hc
    omega
  refine ⟨i, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro v hv
    simpa only [ovalPair,Finset.mem_filter,Finset.mem_univ,true_and] using hstar v hv
  · rw [hS.1,(ovalTable_oval i).1]

/-- AS91 (2.2), in the dual singular-line convention. -/
theorem disc_or_nine_of_oval_intersections (S : Finset Syntheme) (hne : S.Nonempty)
    (hit : ∀ O, Oval O → (O ∩ S).Nonempty → (O ∩ S).card = 3) :
    (∃ s, S = disc s) ∨ S.card = 9 :=
  oval_hitting_classification S hne (fun i => hit _ (ovalTable_oval i))

theorem ovalTable_injective : Function.Injective ovalTable := by decide

/-- All six ovals in the dual residue. -/
def allOvals : Finset (Finset Syntheme) := Finset.univ.image ovalTable

theorem mem_allOvals (S : Finset Syntheme) : S ∈ allOvals ↔ Oval S := by
  constructor
  · intro hS
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
    exact ovalTable_oval i
  · intro hS
    obtain ⟨i,rfl⟩ := ovalTable_complete hS
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem allOvals_card : allOvals.card = 6 := by
  rw [allOvals, Finset.card_image_of_injective _ ovalTable_injective]
  decide

/-- AS91 (2.1.1): each singular line lies on exactly two dual ovals. -/
theorem ovals_through_card (s : Syntheme) :
    (allOvals.filter (fun O => s ∈ O)).card = 2 := by
  have he : allOvals.filter (fun O => s ∈ O) = (ovalPair s).image ovalTable := by
    ext O
    simp only [allOvals,ovalPair,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨i,rfl⟩,hs⟩
      exact ⟨i,hs,rfl⟩
    · rintro ⟨i,hs,rfl⟩
      exact ⟨⟨i,rfl⟩,hs⟩
  rw [he,Finset.card_image_of_injective _ ovalTable_injective,ovalPair_card]

/-- AS91 (2.1.1): two distinct ovals have exactly one common singular line. -/
theorem oval_intersection_card_one {S T : Finset Syntheme}
    (hS : Oval S) (hT : Oval T) (hne : S ≠ T) : (S ∩ T).card = 1 := by
  obtain ⟨i,rfl⟩ := ovalTable_complete hS
  obtain ⟨j,rfl⟩ := ovalTable_complete hT
  have hij : i ≠ j := fun he => hne (congrArg ovalTable he)
  have hc : ∀ i j : Fin 6, i ≠ j → (ovalTable i ∩ ovalTable j).card = 1 := by decide
  exact hc i j hij

/-- A disc meets an oval in zero or three singular lines. -/
theorem disc_oval_card (s : Syntheme) {O : Finset Syntheme} (hO : Oval O) :
    (O ∩ disc s).card = if s ∈ O then 0 else 3 := by
  obtain ⟨i,rfl⟩ := ovalTable_complete hO
  have hc : ∀ (s : Syntheme) (i : Fin 6),
      (ovalTable i ∩ disc s).card = if s ∈ ovalTable i then 0 else 3 := by decide
  exact hc s i

/-- The marked ovals meeting a set. Completeness of the six ovals ensures
this is the literal family O(S) in AS91. -/
def ovalsMeeting (S : Finset Syntheme) : Finset (Finset Syntheme) :=
  allOvals.filter (fun O => (O ∩ S).Nonempty)

theorem ovalsMeeting_card (S : Finset Syntheme) :
    (ovalsMeeting S).card = (touched S).card := by
  have he : ovalsMeeting S = (touched S).image ovalTable := by
    ext O
    simp only [ovalsMeeting,allOvals,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨i,rfl⟩,hi⟩
      exact ⟨i,(mem_touched S i).mpr hi,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,rfl⟩,(mem_touched S i).mp hi⟩
  rw [he,Finset.card_image_of_injective _ ovalTable_injective]

theorem disc_ovalsMeeting_card (s : Syntheme) : (ovalsMeeting (disc s)).card = 4 := by
  rw [ovalsMeeting_card]
  have hc : ∀ s : Syntheme, (touched (disc s)).card = 4 := by decide
  exact hc s

/-- The full dual version of AS91 (2.2), including both sizes in its disc alternative. -/
theorem disc_or_nine (S : Finset Syntheme) (hne : S.Nonempty)
    (hit : ∀ O, Oval O → (O ∩ S).Nonempty → (O ∩ S).card = 3) :
    (∃ s, S = disc s ∧ S.card = 6 ∧ (ovalsMeeting S).card = 4) ∨ S.card = 9 := by
  rcases disc_or_nine_of_oval_intersections S hne hit with ⟨s,rfl⟩ | hc
  · exact Or.inl ⟨s,rfl,disc_card s,disc_ovalsMeeting_card s⟩
  · exact Or.inr hc

/-- Every clique containing two lines is contained in their singular pencil. -/
theorem clique_subset_pencil (S : Finset Syntheme) (hc : 1 < S.card)
    (hcl : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → synthemeCollinear s t) :
    ∃ a, S ⊆ pencil a := by
  obtain ⟨s,hs,t,ht,hst⟩ := Finset.one_lt_card.mp hc
  obtain ⟨a,has,hat⟩ := ((syntheme_collinear_iff_common_duad s t).mp (hcl s hs t ht hst)).2
  refine ⟨a, ?_⟩
  intro u hu
  have hau : incident a u := by
    by_cases hus : u = s
    · simpa [hus] using has
    by_cases hut : u = t
    · simpa [hut] using hat
    by_contra hn
    obtain ⟨v,_,hv⟩ := quadrangle_unique_collinear_dual a u hn
    have hvs := hv s ⟨has,hcl u hu s hs hus⟩
    have hvt := hv t ⟨hat,hcl u hu t ht hut⟩
    exact hst (hvs.trans hvt.symm)
  simpa [pencil] using hau

theorem clique_card_le_three (S : Finset Syntheme)
    (hcl : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → synthemeCollinear s t) : S.card ≤ 3 := by
  by_cases hc : 1 < S.card
  · obtain ⟨a,ha⟩ := clique_subset_pencil S hc hcl
    exact (Finset.card_le_card ha).trans_eq (pencil_card a)
  · omega

theorem coclique_card_le_five (S : Finset Syntheme)
    (hn : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ synthemeCollinear s t) : S.card ≤ 5 := by
  have hdis : (S : Set Syntheme).PairwiseDisjoint synthemeDuads := by
    intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro a has hat
    exact hn s hs t ht hst ((syntheme_collinear_iff_common_duad s t).mpr ⟨hst,a,has,hat⟩)
  have hcard := Finset.card_le_univ (S.biUnion synthemeDuads)
  rw [Finset.card_biUnion hdis] at hcard
  simp only [(syntheme_is_partition _).1,Finset.sum_const_nat] at hcard
  change S.card * 3 ≤ 15 at hcard
  omega

end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Polar
