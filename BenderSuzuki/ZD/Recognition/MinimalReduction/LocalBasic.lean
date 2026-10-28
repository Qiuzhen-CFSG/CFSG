module

public import BenderSuzuki.ZD.Recognition.Interfaces
public import BenderSuzuki.ZD.RankOne

/-!
# Induction and the rank-one local case in the ZD reduction

Minimality supplies the complete ZD conclusion in each eligible proper
subgroup, and in each nontrivial quotient where product disconnection has
been established. In rank one every involution is conjugate to a member of
the distinguished set. Unique conjugate membership then gives strong
embedding. Consequently a failure of local strong embedding forces the
structural alternative of ZD in that proper subgroup.

Source: GLS, Volume 4, Chapter 2, (3A), (4B)--(4E), and the proof of
Proposition 4.4. Quotient descent is an explicit remaining premise here.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- In rank one, product disconnection already gives strong embedding. -/
public theorem stronglyEmbedded_of_productDisconnected_of_not_twoRank
    (h : IsProductDisconnected Z M) (hr : ¬ TwoRankAtLeastTwo G) :
    IsStronglyEmbedded M := by
  have hall : ∀ x : G, IsInvolution x → x ∈ Z := by
    intro x hx
    obtain ⟨z, hz, _⟩ := h.nonempty
    obtain ⟨g, hg⟩ := involutions_conjugate_of_not_twoRank hr (h.involutions z hz) hx
    simpa only [MulAut.conj_apply, hg] using h.invariant g z hz
  refine ⟨h.proper, ?_, ?_⟩
  · obtain ⟨z, hz, hzM⟩ := h.nonempty
    exact ⟨z, hzM, h.involutions z hz⟩
  · intro g hg x hxM hxg hx
    apply hg
    apply (h.conjugate_mem_iff x (hall x hx) hxM g).mp
    have hh := rightConjugateElem_mem_of_mem_rightConjugate
      (g := g⁻¹) (by simpa only [inv_inv] using hxg)
    simpa only [rightConjugateElem, inv_inv, MulAut.conj_apply] using hh

omit [Finite G] in
/-- The generated group in an eligible subgroup is not contained in `M`.
This is the first assertion of source Lemma 4.6. -/
public theorem local_closure_not_le
    (h : IsProductDisconnected Z M) (H : Subgroup G)
    (hHM : ¬ H ≤ M) (hne : ∃ z ∈ Z, z ∈ H ∧ z ∈ M) :
    ¬ Subgroup.closure (H.subtype ⁻¹' Z) ≤ M.comap H.subtype :=
  (productDisconnected_subgroup h H hHM hne).closure_not_le

/-- The rank-one branch proves Definition SZ(d) for the given subgroup. -/
public theorem local_stronglyEmbedded_of_not_twoRank
    (h : IsProductDisconnected Z M) (H : Subgroup G)
    (hHM : ¬ H ≤ M) (hne : ∃ z ∈ Z, z ∈ H ∧ z ∈ M)
    (hr : ¬ TwoRankAtLeastTwo (Subgroup.closure (H.subtype ⁻¹' Z))) :
    IsStronglyEmbedded
      ((M.comap H.subtype).comap
        (Subgroup.closure (H.subtype ⁻¹' Z)).subtype) := by
  exact stronglyEmbedded_of_productDisconnected_of_not_twoRank
    (productDisconnected_closure (productDisconnected_subgroup h H hHM hne)) hr

/-- Specialize minimality to a proper subgroup, retaining every source clause. -/
public theorem MinimalCounterexample.conclusion_subgroup
    (h : MinimalCounterexample Z M) (H : Subgroup G) (hH : H ≠ ⊤)
    (hHM : ¬ H ≤ M) (hne : ∃ z ∈ Z, z ∈ H ∧ z ∈ M) :
    Conclusion (H.subtype ⁻¹' Z) (M.comap H.subtype) := by
  apply h.smaller _ _ _ (productDisconnected_subgroup h.disconnected H hHM hne)
  exact lt_of_not_ge (fun hle => hH (H.eq_top_of_le_card hle))

/-- Specialize minimality to a quotient by a nontrivial normal subgroup.
Product disconnection in that quotient must be proved separately. -/
public theorem MinimalCounterexample.conclusion_quotient
    (h : MinimalCounterexample Z M) (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥)
    (hquot : IsProductDisconnected ((QuotientGroup.mk' N) '' Z)
      (M.map (QuotientGroup.mk' N))) :
    Conclusion ((QuotientGroup.mk' N) '' Z) (M.map (QuotientGroup.mk' N)) := by
  apply h.smaller _ _ _ hquot
  have hNcard := (Subgroup.one_lt_card_iff_ne_bot (H := N)).mpr hne
  have hpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  have heq := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  nlinarith

/-- A counterexample to the local embedding assertion is necessarily in
the structural branch of the induction hypothesis. This supplies the full
ZD structure used to start the contradiction in Proposition 4.4. -/
public theorem MinimalCounterexample.local_structure_of_not_stronglyEmbedded
    (h : MinimalCounterexample Z M) (H : Subgroup G) (hH : H ≠ ⊤)
    (hHM : ¬ H ≤ M) (hne : ∃ z ∈ Z, z ∈ H ∧ z ∈ M)
    (hnot : ¬ IsStronglyEmbedded
      ((M.comap H.subtype).comap
        (Subgroup.closure (H.subtype ⁻¹' Z)).subtype)) :
    StructureConclusion (H.subtype ⁻¹' Z) (M.comap H.subtype) := by
  rcases h.conclusion_subgroup H hH hHM hne with hr | hs
  · exact False.elim (hnot
      (local_stronglyEmbedded_of_not_twoRank h.disconnected H hHM hne hr))
  · exact hs

end BenderSuzuki.ZD
