module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Residue
/-!
# Singular pencils and ovals in the dual binary symplectic residue

The generalized quadrangle axiom forces a three-clique to be the pencil
through a point. Five pairwise noncollinear singular lines partition the
fifteen points, so each singular pencil meets the oval exactly once.
These are structural proofs using the existing binary symplectic model.

Source: Aschbacher–Segev (1991), (2.1.3) and (7.3), pp.592,603.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Polar
open Theory.SpecificGroups.SymmetricSix
open Finset

def pencil (a : Duad) : Finset Syntheme := Finset.univ.filter (incident a)

def Oval (S : Finset Syntheme) : Prop :=
  S.card = 5 ∧ ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint (synthemeDuads s) (synthemeDuads t)

def disc (s : Syntheme) : Finset Syntheme := Finset.univ.filter (synthemeCollinear s)

theorem pencil_card (a : Duad) : (pencil a).card = 3 := duad_incidence_three a

theorem disc_card (s : Syntheme) : (disc s).card = 6 := syntheme_collinear_six s

theorem clique_three_is_pencil (S : Finset Syntheme) (hc : S.card = 3)
    (hcl : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → synthemeCollinear s t) :
    ∃ a, S = pencil a := by
  obtain ⟨s,t,u,hst,hsu,htu,hS⟩ := Finset.card_eq_three.mp hc
  have hs : s ∈ S := by simp [hS]
  have ht : t ∈ S := by simp [hS]
  have hu : u ∈ S := by simp [hS]
  obtain ⟨a,has,hat⟩ := ((syntheme_collinear_iff_common_duad s t).mp (hcl s hs t ht hst)).2
  have hau : incident a u := by
    by_contra hn
    obtain ⟨v,_,hv⟩ := quadrangle_unique_collinear_dual a u hn
    have hvs := hv s ⟨has,hcl u hu s hs hsu.symm⟩
    have hvt := hv t ⟨hat,hcl u hu t ht htu.symm⟩
    exact hst (hvs.trans hvt.symm)
  refine ⟨a, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro v hv
    have hv' : v = s ∨ v = t ∨ v = u := by simpa [hS] using hv
    rcases hv' with rfl | rfl | rfl <;> simp [pencil,has,hat,hau]
  · rw [pencil_card,hc]

theorem oval_of_five_coclique (S : Finset Syntheme) (hc : S.card = 5)
    (hn : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ synthemeCollinear s t) : Oval S := by
  refine ⟨hc, ?_⟩
  intro s hs t ht hst
  apply Finset.disjoint_left.mpr
  intro a ha hb
  exact hn s hs t ht hst ((syntheme_collinear_iff_common_duad s t).mpr ⟨hst,a,ha,hb⟩)

theorem oval_covers (S : Finset Syntheme) (hS : Oval S) :
    S.biUnion synthemeDuads = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_biUnion (show (S : Set Syntheme).PairwiseDisjoint synthemeDuads from hS.2)]
  simp only [(syntheme_is_partition _).1]
  simp [hS.1]

/-- The dual oval meets every singular pencil in exactly one line, AS91 (2.1.3). -/
theorem oval_hits_pencil (S : Finset Syntheme) (hS : Oval S) (a : Duad) :
    ∃! s, s ∈ S ∧ incident a s := by
  have ha : a ∈ S.biUnion synthemeDuads := (oval_covers S hS).symm ▸ Finset.mem_univ a
  obtain ⟨s,hs,has⟩ := Finset.mem_biUnion.mp ha
  refine ⟨s, ⟨hs,has⟩, ?_⟩
  rintro t ⟨ht,hat⟩
  by_contra hts
  exact Finset.disjoint_left.mp (hS.2 t ht s hs hts) hat has

end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Polar
