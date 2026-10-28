module
public import ABG.ChapterII.Section2.CoreFreeNormalOddIndex
public import ABG.ChapterII.Section2.MinimalNormalSimple
public import ABG.ChapterII.Section1.WreathedCenter
public import ABG.ChapterII.Section1.Center

/-!
# A simple normal subgroup in an odd-core-free QD group

A finite QD group with trivial odd core contains a simple normal subgroup of
odd index. This is the core-free normal-subgroup reduction in ABG Chapter II
Section 2 Proposition 2, article pp.15-16,
`refs/latex/alperin-brauer-gorenstein-pages/page-016.tex` and `page-017.tex`.
The complete proposition additionally identifies the subgroup as QD and
passes from an arbitrary group to its odd-core quotient.

Choose a nontrivial minimal normal subgroup N. The previous odd-index theorem
applies to N. Coprimality of the relative index then puts the ambient Sylow
two-subgroup inside N. Its center is cyclic in both the quasi-dihedral and
wreathed cases; transfer this through the restricted Sylow isomorphism.
The minimal-normal simplicity theorem now proves N simple. Nontriviality of
the ambient group follows from the involution representative in its QD
fusion pattern. The Sylow-containment lemma is public so the final
proposition can recover the QD pattern inside the simple normal subgroup.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow two-subgroup lies in every normal subgroup of odd index. -/
public theorem sylow_le_odd_index (S : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hN : Odd N.index) : (S : Subgroup G) ≤ N := by
  rw [← Subgroup.relIndex_eq_one]
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  have hcop : N.index.Coprime (Nat.card S) := by
    rw [hn]
    exact Nat.prime_two.coprime_pow_of_not_dvd
      (by simpa [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hN)
  exact Nat.eq_one_of_dvd_coprimes hcop (N.relIndex_dvd_index_of_normal _)
    (N.relIndex_dvd_card _)

private theorem center_cyclic_of_shape {H : Type*} [Group H]
    (hH : Stellmacher.IsSemidihedralGroup H ∨ IsWreathedGroup H) :
    IsCyclic (Subgroup.center H) := by
  rcases hH with h | ⟨n, h⟩
  · exact isCyclic_of_prime_card (QuasiDihedral.card_center h)
  · obtain ⟨P⟩ := Wreathed.nonempty_presentation h
    exact P.center_cyclic

private theorem exists_sylow_cyclic_center (hG : IsQDGroup G)
    (hcore : pPrimeCore 2 G = ⊥) (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    ∃ S : Sylow 2 N, IsCyclic (Subgroup.center S) := by
  have hodd := hG.odd_index_of_normal_ne_bot hcore N hN
  have hshape : ∃ S : Sylow 2 G, Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S := by
    rcases hG with ⟨S, T, Q, hframe, _⟩ | ⟨S, n, U, V, hframe, _⟩
    · exact ⟨S, Or.inl hframe.1⟩
    · exact ⟨S, Or.inr ⟨n, hframe.1⟩⟩
  obtain ⟨S, hS⟩ := hshape
  have hSN := sylow_le_odd_index S N hodd
  let R : Sylow 2 N := S.subtype hSN
  refine ⟨R, ?_⟩
  let e : R ≃* S := Subgroup.subgroupOfEquivOfLe hSN
  let := center_cyclic_of_shape hS
  exact isCyclic_of_surjective (Subgroup.centerCongr e).symm
    (Subgroup.centerCongr e).symm.surjective

/-- An odd-core-free QD group has a simple normal subgroup of odd index. -/
public theorem IsQDGroup.exists_simple_normal_of_oddCore_eq_bot
    (hG : IsQDGroup G) (hcore : pPrimeCore 2 G = ⊥) :
    ∃ N : Subgroup G, N.Normal ∧ IsSimpleGroup N ∧ Odd N.index := by
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hG with ⟨S, T, Q, _, hp⟩ | ⟨S, n, U, V, _, hp⟩
    · exact hp.2.1
    · exact hp.2.1
  obtain ⟨r, hr, _⟩ := hclass
  have hne : r 0 ≠ 1 := by
    intro h
    have horder := hr 0
    rw [h, orderOf_one] at horder
    omega
  let : Nontrivial G := ⟨⟨r 0, 1, hne⟩⟩
  obtain ⟨N, hNnormal, _, hN, hmin⟩ := exists_minimal_normal_le
    (⊤ : Subgroup G) inferInstance (by exact top_ne_bot)
  let := hNnormal
  let : IsMinimalNormal N := ⟨fun K hK hKN => by
    by_cases h : K = ⊥
    · exact Or.inl h
    · exact Or.inr (hmin K hK hKN h)⟩
  obtain ⟨S, hZ⟩ := exists_sylow_cyclic_center hG hcore N hN
  exact ⟨N, hNnormal, minimal_normal_simple_of_cyclic_sylow_center hcore N hN S hZ,
    hG.odd_index_of_normal_ne_bot hcore N hN⟩

end ABG
