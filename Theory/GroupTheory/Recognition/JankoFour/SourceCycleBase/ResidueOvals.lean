module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.LineViewsPolar
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Ovals
/-!
# Ovals, discs, and cliques in the actual point-plane residue

The literal Todd chart transports the six-oval calculation to each ambient
point-plane flag. A nonempty line set meeting every touched oval in three
lines is a six-line disc or has nine lines. The same chart gives the sharp
clique and coclique bounds. The off-plane common-neighbor clique assertion
is proved from the earlier-source unique-plane geometry, as used in (7.4).

Source: Aschbacher–Segev (1991), (2.1)–(2.2) and (7.4), pp.592,603–604.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h) {x : Point d.P} {π : Plane z}
noncomputable local instance : DecidableEq (Line d.L) := Classical.decEq _

noncomputable def residueSet (hxπ : OnPlane d.P x π)
    (S : Finset {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π}) : Finset Syntheme :=
  S.map (d.residue.flagLines x π hxπ).toEmbedding

theorem residueSet_card (hxπ : OnPlane d.P x π)
    (S : Finset {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π}) :
    (d.residueSet hxπ S).card = S.card := Finset.card_map _

def residueOval
    (S : Finset {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π}) : Prop :=
  S.card = 5 ∧ ∀ l ∈ S, ∀ m ∈ S, l ≠ m → ¬ LineType d.residue 1 x l.val m.val

theorem residueSet_oval_iff (hxπ : OnPlane d.P x π)
    (S : Finset {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π}) :
    Native.Polar.Oval (d.residueSet hxπ S) ↔ d.residueOval S := by
  classical
  constructor
  · intro ho
    refine ⟨(d.residueSet_card hxπ S).symm.trans ho.1, ?_⟩
    intro l hl m hm hlm htype
    have hcol := (d.residue.flagLines_collinear_iff x π hxπ l m).mpr htype
    obtain ⟨_,a,hal,ham⟩ := (syntheme_collinear_iff_common_duad _ _).mp hcol
    exact Finset.disjoint_left.mp (ho.2 _ (Finset.mem_map.mpr ⟨l,hl,rfl⟩)
      _ (Finset.mem_map.mpr ⟨m,hm,rfl⟩) ((d.residue.flagLines x π hxπ).injective.ne hlm)) hal ham
  · rintro ⟨hc,hn⟩
    apply Native.Polar.oval_of_five_coclique _ ((d.residueSet_card hxπ S).trans hc)
    intro s hs t ht hst hcol
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hs
    obtain ⟨m,hm,rfl⟩ := Finset.mem_map.mp ht
    exact hn l hl m hm (fun he => hst (congrArg (d.residue.flagLines x π hxπ) he))
      ((d.residue.flagLines_collinear_iff x π hxπ l m).mp hcol)

noncomputable def residueDisc (hxπ : OnPlane d.P x π)
    (l : {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π}) :
    Finset {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π} :=
  (Native.Polar.disc (d.residue.flagLines x π hxπ l)).map
    (d.residue.flagLines x π hxπ).symm.toEmbedding

theorem mem_residueDisc (hxπ : OnPlane d.P x π)
    (l m : {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π}) :
    m ∈ d.residueDisc hxπ l ↔ LineType d.residue 1 x l.val m.val := by
  simp only [residueDisc,Finset.mem_map_equiv,Equiv.symm_symm,Native.Polar.disc,
    Finset.mem_filter,Finset.mem_univ,true_and]
  exact d.residue.flagLines_collinear_iff x π hxπ l m

theorem residueDisc_card (hxπ : OnPlane d.P x π)
    (l : {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π}) :
    (d.residueDisc hxπ l).card = 6 := by
  rw [residueDisc,Finset.card_map,Native.Polar.disc_card]

/-- The dual disc-or-nine lemma in the actual point-plane flag and its
literal Todd orbital, supplying the finite residue step of AS91 (7.4). -/
theorem residue_disc_or_nine (hxπ : OnPlane d.P x π)
    (S : Finset {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π})
    (hne : S.Nonempty)
    (hit : ∀ O, d.residueOval O → (O ∩ S).Nonempty → (O ∩ S).card = 3) :
    (∃ l, S = d.residueDisc hxπ l ∧ S.card = 6) ∨ S.card = 9 := by
  classical
  let e := d.residue.flagLines x π hxπ
  have hn : (d.residueSet hxπ S).Nonempty := by
    obtain ⟨l,hl⟩ := hne
    exact ⟨e l,Finset.mem_map.mpr ⟨l,hl,rfl⟩⟩
  have hhit : ∀ O, Native.Polar.Oval O → (O ∩ d.residueSet hxπ S).Nonempty →
      (O ∩ d.residueSet hxπ S).card = 3 := by
    intro O hO hmeet
    let T := O.map e.symm.toEmbedding
    have hT : d.residueSet hxπ T = O := by simp [residueSet,T,e,Finset.map_map]
    have hoval : d.residueOval T := (d.residueSet_oval_iff hxπ T).mp (hT.symm ▸ hO)
    have hmap : d.residueSet hxπ (T ∩ S) = O ∩ d.residueSet hxπ S := by
      change (T ∩ S).map e.toEmbedding = _
      rw [Finset.map_inter]
      change d.residueSet hxπ T ∩ _ = _
      rw [hT]
      rfl
    have hTS : (T ∩ S).Nonempty := by
      rw [← hmap] at hmeet
      obtain ⟨s,hs⟩ := hmeet
      obtain ⟨l,hl,_⟩ := Finset.mem_map.mp hs
      exact ⟨l,hl⟩
    rw [← hmap,d.residueSet_card,hit T hoval hTS]
  rcases Native.Polar.disc_or_nine_of_oval_intersections _ hn hhit with ⟨s,hs⟩ | hc
  · left
    refine ⟨e.symm s, ?_, ?_⟩
    · apply Finset.map_injective e.toEmbedding
      change d.residueSet hxπ S = _
      rw [hs]
      simp [residueDisc,e,Finset.map_map]
    · rw [← d.residueSet_card hxπ S,hs,Native.Polar.disc_card]
  · exact Or.inr ((d.residueSet_card hxπ S).symm.trans hc)

/-- A δ₁ clique in the literal point-plane residue has at most three lines. -/
theorem residue_clique_card_le_three (hxπ : OnPlane d.P x π)
    (S : Finset {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π})
    (hcl : ∀ l ∈ S, ∀ m ∈ S, l ≠ m → LineType d.residue 1 x l.val m.val) :
    S.card ≤ 3 := by
  rw [← d.residueSet_card hxπ S]
  apply Native.Polar.clique_card_le_three
  intro s hs t ht hst
  obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hs
  obtain ⟨m,hm,rfl⟩ := Finset.mem_map.mp ht
  exact (d.residue.flagLines_collinear_iff x π hxπ l m).mpr
    (hcl l hl m hm (fun he => hst (congrArg (d.residue.flagLines x π hxπ) he)))

/-- A coclique in that same residue has at most five lines. -/
theorem residue_coclique_card_le_five (hxπ : OnPlane d.P x π)
    (S : Finset {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l π})
    (hn : ∀ l ∈ S, ∀ m ∈ S, l ≠ m → ¬ LineType d.residue 1 x l.val m.val) :
    S.card ≤ 5 := by
  rw [← d.residueSet_card hxπ S]
  apply Native.Polar.coclique_card_le_five
  intro s hs t ht hst hcol
  obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hs
  obtain ⟨m,hm,rfl⟩ := Finset.mem_map.mp ht
  exact hn l hl m hm (fun he => hst (congrArg (d.residue.flagLines x π hxπ) he))
    ((d.residue.flagLines_collinear_iff x π hxπ l m).mp hcol)

/-- The clique assertion used in AS91 (7.4): the common neighbors in a
plane form a clique whenever the other endpoint is outside that plane. -/
theorem common_neighbors_off_plane_clique {y : Point d.P}
    (hyπ : ¬ OnPlane d.P y π) {a b : Point d.P}
    (haπ : OnPlane d.P a π) (hbπ : OnPlane d.P b π)
    (hxa : Adj d.L x a) (hya : Adj d.L y a)
    (hxb : Adj d.L x b) (hyb : Adj d.L y b) (hab : a ≠ b) : Adj d.L a b := by
  by_contra hn
  have hd : DistanceTwo d.L a b := ⟨hab,hn,x,adj_symm hxa,hxb⟩
  exact hyπ (d.common_neighbors_in_plane a b π hd haπ hbπ y (adj_symm hya) (adj_symm hyb))

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
