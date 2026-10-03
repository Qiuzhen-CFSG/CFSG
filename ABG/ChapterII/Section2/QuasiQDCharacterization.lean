module
public import ABG.ChapterII.Section1.Fusion
public import ABG.ChapterII.Section1.SimpleReduction
public import ABG.ChapterII.Section2.Defs
public import Theory.GroupTheory.PGroup.MaximalIndex
/-!
# The quasi-dihedral QD case and normal index two

For a finite group with a chosen quasi-dihedral Sylow fusion frame, the full
QD pattern is equivalent to having no normal subgroup of index two. This
makes the characterization following ABG II.1 Proposition 1 and II.2
Definition 1 available without dropping any of the pattern's fusion clauses.

Apply the proved four-case fusion theorem. The Q and D cases directly supply
normal subgroups of index two. In the normal-complement case, the quotient
by the odd normal complement is a nontrivial finite two-group: triviality
would contradict the even order of the ambient group. A maximal subgroup
of this quotient has index two, and its inverse image gives the required
contradiction. This obstruction is exported for the parallel wreathed case.
The simple-group corollary uses the existing quasi-dihedral
noncommutativity reduction to exclude normal index two.

Source: `refs/latex/alperin-brauer-gorenstein.tex`, article pp.10–14.
-/

namespace ABG
/-- An even group with a normal two-complement has a normal index-two subgroup. -/
public theorem normal_index_two_of_normal_complement
    {G : Type*} [Group G] [Finite G]
    (heven : 2 ∣ Nat.card G) (hcomp : HasNormalPComplement 2 G) :
    ∃ K : Subgroup G, K.Normal ∧ K.index = 2 := by
  obtain ⟨N, hN, hcop, hquot⟩ := hcomp
  let := hN
  have hNne : N ≠ ⊤ := by
    intro h
    subst N
    have hdvd : 2 ∣ Nat.card (⊤ : Subgroup G) := by
      simpa using heven
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) (dvd_refl 2) hdvd) hcop
  let : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNne
  obtain ⟨U, hU⟩ := IsCoatomic.exists_coatom (α := Subgroup (G ⧸ N))
  have hindex := hquot.index_of_isCoatom U hU
  let K := U.comap (QuotientGroup.mk' N)
  have hKi : K.index = 2 := (U.index_comap_of_surjective (QuotientGroup.mk'_surjective N)).trans hindex
  exact ⟨K, K.normal_of_index_eq_two hKi, hKi⟩

/-- The full QD fusion pattern is exactly the absence of normal index two. -/
public theorem quasiDihedral_qdPattern_iff_no_normal_index_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (T Q : Subgroup G) (hframe : QuasiDihedralFusionFrame S T Q) :
    QuasiDihedralQDPattern T Q ↔ HasNoNormalIndexTwoSubgroup G := by
  refine ⟨fun h => h.1, fun hno => ?_⟩
  rcases quasiDihedral_fusion S T Q hframe with h | h | h | h
  · exact h
  · obtain ⟨K, hK, hKi, _⟩ := h.1
    exact (hno K hK hKi).elim
  · obtain ⟨K, hK, hKi, _⟩ := h.1
    exact (hno K hK hKi).elim
  · obtain ⟨n, hn, hcard, _⟩ := hframe.1
    have hevenS : 2 ∣ Nat.card S := by
      rw [hcard]
      exact dvd_pow_self 2 (by omega)
    have heven : 2 ∣ Nat.card G := hevenS.trans (Subgroup.card_subgroup_dvd_card (S : Subgroup G))
    obtain ⟨K, hK, hKi⟩ := normal_index_two_of_normal_complement heven h.1
    exact (hno K hK hKi).elim

/-- A simple group with this quasi-dihedral frame has the full QD pattern. -/
public theorem quasiDihedral_qdPattern_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (T Q : Subgroup G) (hframe : QuasiDihedralFusionFrame S T Q) :
    QuasiDihedralQDPattern T Q := by
  apply (quasiDihedral_qdPattern_iff_no_normal_index_two S T Q hframe).mpr
  exact fun K _ => QuasiDihedral.index_ne_two S hframe.1 K
end ABG
