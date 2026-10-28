module
public import Theory.Representation.BinaryOffender.QuadraticPairPermutation
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Transvections
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Selection

/-!
# Quadratic actors in the exchanged-factor action

Faithfulness on the moved section and quadraticity make an actor exchanging
the two disjoint summands cyclic of order two. Its fixed-codimension bound
then forces p=3 and moved dimension four. In dimension eight every quadratic
member therefore preserves the two factors. The product of the two odd
dihedral factors bounds the rank of a preserving actor by two.

The literal selected-endpoint application is in Selection.StrictOrthogonalSource.
The ambient exclusion of the swapping case and the rank-eight confinement
remain with the same source assembly owner.

Source: Aschbacher--Smith 14.6.13, printed pp.1031--1032.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer OrthogonalSource Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.CriticalGeometry.Reorientation
variable {G : Type*} [Group G] [Finite G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

/-- A quadratic actor either preserves the original two supports or is
cyclic of order two and exchanges them. In the latter case the Q-family
codimension bound forces p=3 and moved dimension four. -/
theorem exchanged_quadratic_preserves_or_swaps
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (hf : ∀ t : H ⧸ pCore 2 H,
      (∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation t v = v) → t = 1)
    (B : Subgroup (H ⧸ pCore 2 H)) (hq : QuadraticMember a.representation B) :
    B ≤ actorImage H H0 ∨
      (p = 3 ∧ Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4 ∧
        ∃ t ∈ B, B = zpowers t ∧ Nat.card B = 2 ∧ rank B = 1 ∧
          (subspaceCommutator a.representation ⊤ (actorImage H H1)).map (a.representation t) =
            subspaceCommutator a.representation ⊤ (actorImage H H2) ∧
          (subspaceCommutator a.representation ⊤ (actorImage H H2)).map (a.representation t) =
            subspaceCommutator a.representation ⊤ (actorImage H H1)) := by
  classical
  let I := subspaceCommutator a.representation ⊤ (actorImage H H1)
  let J := subspaceCommutator a.representation ⊤ (actorImage H H2)
  let : IsElementaryAbelian 2 B := hq.1.2
  have hf' (t : H ⧸ pCore 2 H) (hfix : ∀ v ∈ I ⊔ J, a.representation t v = v) : t = 1 := by
    apply hf t
    simpa only [I,J,d.split] using hfix
  have hI : I ≠ ⊥ := by
    intro he
    have hd := d.first_dimension
    change (p = 3 ∧ (Module.finrank (ZMod 2) I = 2 ∨ Module.finrank (ZMod 2) I = 4)) ∨
      (p = 5 ∧ Module.finrank (ZMod 2) I = 4) at hd
    rw [he,finrank_bot] at hd
    omega
  by_cases hs : B ≤ subspaceStabilizer a.representation I
  · left
    intro t ht
    exact exchanged_actor_mem_of_first_plane_stable a T hTH p H0 H1 H2 d (hs ht)
  · obtain ⟨t,ht,hts⟩ : ∃ t ∈ B, t ∉ subspaceStabilizer a.representation I := by
      by_contra! hh
      exact hs (fun t ht => hh t ht)
    have hswap : I.map (a.representation t) = J ∧ J.map (a.representation t) = I := by
      rcases exchanged_spaces_permuted a T hTH p H0 H1 H2 d t with hkeep | hswap
      · exact False.elim (hts ((subspace_map_eq_iff _ _ _).mp hkeep.1))
      · exact hswap
    have hperm (b : H ⧸ pCore 2 H) (_hb : b ∈ B) :
        I.map (a.representation b) = I ∨ I.map (a.representation b) = J := by
      rcases exchanged_spaces_permuted a T hTH p H0 H1 H2 d b with hkeep | hswap
      · exact Or.inl hkeep.1
      · exact Or.inr hswap.1
    have he := quadratic_swapping_actor_eq_zpowers a.representation I J hf' B hq.2.1
      d.disjoint hperm t ht hswap
    obtain ⟨hcard,hrank⟩ := quadratic_swapping_actor_rank a.representation I J hf' B hq.2.1
      d.disjoint hI hperm t ht hswap
    have hsmall := finrank_le_fixedCodim_of_disjoint_map a.representation I ht
      (by rw [hswap.1]; exact d.disjoint)
    have hbound := hq.2.2
    rw [hrank] at hbound
    have hd := d.first_dimension
    have heq := exchanged_dimensions_eq a T hTH p H0 H1 H2 d
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq I J
    rw [show I ⊔ J = subspaceCommutator a.representation ⊤ ⊤ from d.split,
      d.disjoint.eq_bot,finrank_bot,add_zero] at hsum
    change (p = 3 ∧ (Module.finrank (ZMod 2) I = 2 ∨ Module.finrank (ZMod 2) I = 4)) ∨
      (p = 5 ∧ Module.finrank (ZMod 2) I = 4) at hd
    change Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) J at heq
    exact Or.inr ⟨by omega,by omega,t,ht,he,hcard,hrank,hswap.1,hswap.2⟩

/-- In moved dimension eight every quadratic member preserves the two
original factors. This rules out exchanging actors before any point placement. -/
theorem exchanged_quadratic_preserves_of_eight
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (hf : ∀ t : H ⧸ pCore 2 H,
      (∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation t v = v) → t = 1)
    (B : Subgroup (H ⧸ pCore 2 H)) (hq : QuadraticMember a.representation B)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 8) :
    B ≤ actorImage H H0 := by
  rcases exchanged_quadratic_preserves_or_swaps a T hTH p H0 H1 H2 d hf B hq with h | h
  · exact h
  · have := h.2.1
    omega

/-- The product of the two odd dihedral factors has elementary binary rank
at most two. This is the actor-rank bound in (*) on printed p.1032. -/
theorem exchanged_preserving_actor_rank
    (a : LocalQuotientAction H U Z) (T : Subgroup G)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (B : Subgroup (H ⧸ pCore 2 H)) [IsElementaryAbelian 2 B]
    (hB : B ≤ actorImage H H0) : rank B ≤ 2 := by
  have he : actorImage H H0 = actorImage H H1 ⊔ actorImage H H2 := by
    unfold actorImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup (d.first_le.trans d.zero_le)
      (d.second_le.trans d.zero_le),d.join_eq]
  have hc : actorImage H H1 ≤ centralizer (actorImage H H2 : Set _) := by
    intro x hx y hy
    exact (d.actors_commute x hx y hy).symm
  obtain ⟨f,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (actorImage H H1) (actorImage H H2) d.actors_disjoint hc
  have hsize : Nat.card (actorImage H H0) = (2*p)*(2*p) := by
    rw [he,← Nat.card_congr f.toEquiv,Nat.card_prod,
      Nat.card_congr d.first_model.some.toEquiv,Nat.card_congr d.second_model.some.toEquiv,
      DihedralGroup.nat_card]
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
  have hdiv := card_dvd_of_le hB
  rw [hn,hsize] at hdiv
  have hn2 : n ≤ 2 := by
    by_contra! hh
    have h8 : 8 ∣ (2*p)*(2*p) := (Nat.pow_dvd_pow 2 hh).trans hdiv
    rcases d.prime with rfl | rfl <;> norm_num at h8
  simpa only [rank,hn,Nat.log_pow (by decide : 1 < 2)] using hn2
end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
