module
public import Theory.Combinatorics.DuadGraph.Defs
/-!
# Independent five-sets in the disjoint-duad graph

An intersecting family of pairs with no common point contains the three
edges of a triangle. Every pair meeting all three is one of them, so the
family has at most three members. Hence every independent five-set in
KG(6,2) is a point star. Distinct points have distinct stars, giving a
canonical bijection with the six underlying points. All arguments are
structural; no list of graph automorphisms or independent sets is enumerated.

Source application: the duad action in the U₄(3) recognition argument.
-/

public section
namespace Theory.Combinatorics.DuadGraph
open Finset

private theorem pair_of_mem {α : Type*} [DecidableEq α] (s : Finset α)
    (hs : s.card = 2) {a : α} (ha : a ∈ s) :
    ∃ b, a ≠ b ∧ s = {a,b} := by
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hs
  rcases mem_insert.mp ha with rfl | ha
  · exact ⟨y,hxy,rfl⟩
  · have : a=y := mem_singleton.mp ha
    subst a
    exact ⟨x,hxy.symm,pair_comm _ _⟩

private theorem meets_pair {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (h : ¬ Disjoint s {a,b}) : a ∈ s ∨ b ∈ s := by
  obtain ⟨x,hx,hp⟩ := not_disjoint_iff.mp h
  simp only [mem_insert,mem_singleton] at hp
  rcases hp with rfl | rfl <;> tauto

/-- Three intersecting edges without a common point form a triangle; every
further edge meeting all three must be one of them. -/
theorem intersecting_card_le_three {α : Type*} [DecidableEq α]
    (F : Finset (PairGraph.Vertex α))
    (hi : ∀ s ∈ F, ∀ t ∈ F, ¬ Disjoint s.val t.val)
    (hn : ¬ ∃ a, ∀ s ∈ F, a ∈ s.val) : F.card ≤ 3 := by
  classical
  by_cases hF : F.Nonempty
  swap
  · simpa only [not_nonempty_iff_eq_empty.mp hF,card_empty] using (by decide : 0 ≤ 3)
  obtain ⟨s,hs⟩ := hF
  obtain ⟨a,b,hab,hsval⟩ := card_eq_two.mp s.property
  obtain ⟨t,ht,hat⟩ : ∃ t∈F, a∉t.val := by
    by_contra! hh
    exact hn ⟨a,hh⟩
  have hbt : b∈t.val := (meets_pair (hsval ▸ hi t ht s hs)).resolve_left hat
  obtain ⟨c,hbc,htval⟩ := pair_of_mem t.val t.property hbt
  have hac : a≠c := by intro he; exact hat (htval ▸ (by simp [he]))
  obtain ⟨u,hu,hbu⟩ : ∃ u∈F, b∉u.val := by
    by_contra! hh
    exact hn ⟨b,hh⟩
  have hau : a∈u.val := (meets_pair (hsval ▸ hi u hu s hs)).resolve_right hbu
  have hcu : c∈u.val := (meets_pair (htval ▸ hi u hu t ht)).resolve_left hbu
  have huval : u.val={a,c} := (eq_of_subset_of_card_le
    (show {a,c} ⊆ u.val by simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hau hcu)
    (by rw [u.property,card_pair hac])).symm
  have hsubset : F ⊆ {s,t,u} := by
    intro w hw
    have hwab := meets_pair (hsval ▸ hi w hw s hs)
    have hwbc := meets_pair (htval ▸ hi w hw t ht)
    have hwac := meets_pair (huval ▸ hi w hw u hu)
    have heq (x y : α) (hxy : x≠y) (hx : x∈w.val) (hy : y∈w.val) :
        w.val={x,y} := (eq_of_subset_of_card_le
      (show {x,y} ⊆ w.val by simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hx hy)
      (by rw [w.property,card_pair hxy])).symm
    by_cases haw : a∈w.val
    · rcases hwbc with hbw | hcw
      · have : w=s := Subtype.ext ((heq a b hab haw hbw).trans hsval.symm)
        simp [this]
      · have : w=u := Subtype.ext ((heq a c hac haw hcw).trans huval.symm)
        simp [this]
    · have : w=t := Subtype.ext ((heq b c hbc (hwab.resolve_left haw)
        (hwac.resolve_left haw)).trans htval.symm)
      simp [this]
  exact (card_le_card hsubset).trans card_le_three

/-- The point star has five vertices. -/
theorem card_star (a : Fin 6) : (star a).card=5 := by
  have hc : (Finset.univ.erase a).card=5 := by simp
  rw [←hc]
  apply Finset.card_bij (fun s (hs : s∈star a) =>
    Classical.choose (pair_of_mem s.val s.property ((mem_star a s).mp hs)))
  · intro s hs
    obtain ⟨hneq,he⟩ := Classical.choose_spec (pair_of_mem s.val s.property ((mem_star a s).mp hs))
    exact mem_erase.mpr ⟨hneq.symm,mem_univ _⟩
  · intro s hs t ht he
    apply Subtype.ext
    exact (Classical.choose_spec (pair_of_mem s.val s.property ((mem_star a s).mp hs))).2.trans
      (he ▸ (Classical.choose_spec (pair_of_mem t.val t.property ((mem_star a t).mp ht))).2.symm)
  · intro b hb
    have hab : a≠b := (mem_erase.mp hb).1.symm
    let s : Vertex := PairGraph.pair a b hab
    have hs : s∈star a := (mem_star a s).mpr (by simp [s,PairGraph.pair])
    refine ⟨s,hs,?_⟩
    have he := (Classical.choose_spec (pair_of_mem s.val s.property ((mem_star a s).mp hs))).2
    have hb' : b ∈ s.val := by simp [s,PairGraph.pair]
    rw [he] at hb'
    exact (mem_singleton.mp ((mem_insert.mp hb').resolve_left hab.symm)).symm



theorem star_independent (a : Fin 6) : graph.IsIndepSet (star a : Set Vertex) := by
  intro s hs t ht _ hst
  exact disjoint_left.mp hst ((mem_star a s).mp hs) ((mem_star a t).mp ht)

theorem independent_five_eq_star (F : Finset Vertex) (hF : graph.IsNIndepSet 5 F) :
    ∃ a : Fin 6, F=star a := by
  have hi : ∀ s∈F, ∀ t∈F, ¬Disjoint s.val t.val := by
    intro s hs t ht
    by_cases he : s=t
    · subst t
      intro hd
      exact graph.loopless.irrefl s hd
    · exact hF.isIndepSet hs ht he
  have hcommon : ∃ a, ∀ s∈F,a∈s.val := by
    by_contra hn
    have hb := intersecting_card_le_three F hi hn
    have hc := hF.card_eq
    omega
  obtain ⟨a,ha⟩ := hcommon
  exact ⟨a,eq_of_subset_of_card_le (fun s hs => (mem_star a s).mpr (ha s hs))
    (by rw [card_star,hF.card_eq])⟩

theorem star_injective : Function.Injective star := by
  intro a b he
  by_contra hab
  have hp : ∃ c : Fin 6, c≠a ∧ c≠b := by
    by_contra! h
    have hsub : (univ : Finset (Fin 6)) ⊆ {a,b} := by
      intro c _
      by_cases hc : c=a
      · simp [hc]
      · simp [h c hc]
    have hc := card_le_card hsub
    rw [card_pair hab] at hc
    simp at hc
  obtain ⟨c,hca,hcb⟩ := hp
  let s : Vertex := PairGraph.pair a c hca.symm
  have hs : s∈star a := (mem_star a s).mpr (by simp [s,PairGraph.pair])
  have hb := (mem_star b s).mp (he ▸ hs)
  have : b=a ∨ b=c := by simpa [s,PairGraph.pair] using hb
  exact this.elim (Ne.symm hab) hcb.symm

@[expose] noncomputable def starEquiv : Fin 6 ≃ {F : Finset Vertex // graph.IsNIndepSet 5 F} :=
  Equiv.ofBijective (fun a => ⟨star a,star_independent a,card_star a⟩)
    ⟨fun a b h => star_injective (congrArg Subtype.val h), fun ⟨F,hF⟩ => by
      obtain ⟨a,ha⟩ := independent_five_eq_star F hF
      exact ⟨a,Subtype.ext ha.symm⟩⟩

@[simp] theorem starEquiv_val (a : Fin 6) : (starEquiv a).val=star a := rfl
end Theory.Combinatorics.DuadGraph
