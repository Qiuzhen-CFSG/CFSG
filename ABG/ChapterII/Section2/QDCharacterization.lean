module
public import ABG.ChapterII.Section1.FusionFrame
public import ABG.ChapterII.Section1.WreathedFusion
public import ABG.ChapterII.Section2.QuasiQDCharacterization
public import ABG.ChapterII.Section2.WreathedDIndexTwo
public import Theory.GroupTheory.PGroup.TrivialImage

/-!
# QD-groups and the absence of normal index two

For a finite group with a semidihedral or wreathed Sylow two-subgroup,
being a QD-group is equivalent to having no normal subgroup of index two.
The QD predicate retains all the fusion and automizer clauses of ABG's
original definition; this theorem proves its structural characterization.

The quasi-dihedral case is already established. For a wreathed fusion frame,
apply the four-alternative fusion theorem. In the Q case the normal subgroup
of index 2^n gives a nontrivial two-group quotient, impossible by the
no-prime-index image theorem. The D case has its own proved index-two
obstruction, and the normal-complement case gives index two because the
Sylow subgroup has even order. Thus only the full QD pattern remains.
Frame-existence theorems supply the actual subgroup choices for either shape.

Source: Alperin--Brauer--Gorenstein, Chapter II, Section 1, Propositions 1--2,
and Section 2, Definition 1 (article pages 10--14). The result supports the
simple-normal-subgroup reduction under odd-core quotients and odd-index
normal subgroups; these transports are handled by its consumers.
The frame-level wreathed characterization is public for choosing a conjugate
Sylow frame in the involution-centralizer proof of II.2 Proposition 1.
-/

namespace ABG

/-- The full QD definition includes the absence of normal index-two subgroups. -/
public theorem IsQDGroup.no_normal_index_two
    {G : Type*} [Group G] (hG : IsQDGroup G) :
    HasNoNormalIndexTwoSubgroup G := by
  rcases hG with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.1

public theorem wreathed_qdPattern_of_no_normal_index_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hframe : WreathedFusionFrame S n U V)
    (hno : HasNoNormalIndexTwoSubgroup G) : WreathedQDPattern U V := by
  rcases Wreathed.proposition_two S n U V hframe with h | h | h | h
  · exact h
  · obtain ⟨K, hK, hKi, _⟩ := h.1
    let : K.Normal := hK
    have hquot : IsPGroup 2 (G ⧸ K) :=
      IsPGroup.of_card (n := n) (by rw [← K.index_eq_card, hKi])
    have htop : K = ⊤ := by
      apply top_unique
      intro x _
      exact (QuotientGroup.eq_one_iff (N := K) (x := x)).mp
        (MonoidHom.eq_one_of_no_normal_index_prime hno hquot (QuotientGroup.mk' K) x)
    have hd : 2 ∣ K.index := by
      rw [hKi]
      exact dvd_pow_self 2 (by have := hframe.1.1; omega)
    simp [htop] at hd
  · exact (h.not_noNormalIndexTwo hframe hno).elim
  · have hevenS : 2 ∣ Nat.card S := by
      rw [hframe.1.2.1]
      exact dvd_pow_self 2 (by omega)
    have heven : 2 ∣ Nat.card G :=
      hevenS.trans (Subgroup.card_subgroup_dvd_card (S : Subgroup G))
    obtain ⟨K, hK, hKi⟩ := normal_index_two_of_normal_complement heven h.1
    exact (hno K hK hKi).elim

/-- For either full Sylow shape, no normal index two characterizes QD-groups. -/
public theorem isQDGroup_iff_no_normal_index_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) :
    IsQDGroup G ↔ HasNoNormalIndexTwoSubgroup G := by
  refine ⟨IsQDGroup.no_normal_index_two, fun hno => ?_⟩
  rcases hS with hS | ⟨n, hn⟩
  · obtain ⟨T, Q, hframe⟩ := exists_quasiDihedralFusionFrame S hS
    exact Or.inl ⟨S, T, Q, hframe,
      (quasiDihedral_qdPattern_iff_no_normal_index_two S T Q hframe).mpr hno⟩
  · obtain ⟨U, V, hframe⟩ := exists_wreathedFusionFrame S n hn
    exact Or.inr ⟨S, n, U, V, hframe,
      wreathed_qdPattern_of_no_normal_index_two S n U V hframe hno⟩

end ABG
