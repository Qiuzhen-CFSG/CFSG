module
public import ABG.ChapterII.Section1.MaximalModels
public import ABG.ChapterII.Section1.DerivedFrattini

/-!
# The maximal subgroups of a quasi-dihedral group

For the actual semidihedral presentation of order `2^n`, with `n ≥ 4`,
the subgroups `⟨a⟩`, `⟨a²,b⟩`, and `⟨a²,ab⟩` are pairwise distinct
and are precisely the maximal proper subgroups. They are respectively cyclic,
dihedral, and generalized quaternion; the last two group types are expressed
by isomorphisms with the standard Mathlib models.

The model-identification module supplies index two and the isomorphisms.
Index two gives maximality. Conversely, the Frattini calculation puts `a²`
in every maximal subgroup. Splitting the ambient normal forms by exponent
parity shows that a subgroup containing none of `a`, `b`, or `ab` lies inside
`⟨a²⟩`; it therefore cannot be maximal, since `⟨a⟩` is proper. Each
remaining possibility contains one of the three known maximal subgroups.
The actual generators distinguish the three subgroups.

This proves Chapter II, §1, Lemma 1(iii), article page 9 of
`refs/latex/alperin-brauer-gorenstein.tex`. The presentation is from article
page 2; Stellmacher's order parameter is one larger than the article's.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

private theorem pow_parity (a : G) (i : ℕ) :
    a ^ i = (a ^ 2) ^ (i / 2) * a ^ (i % 2) := by
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

private theorem outside_three_le_squares (a b : G) (H : Subgroup G)
    (hsq : a ^ 2 ∈ H) (ha : a ∉ H) (hb : b ∉ H) (hab : a*b ∉ H)
    (hnf : ∀ x : G, ∃ i : ℕ, x = a ^ i ∨ x = a ^ i * b) :
    H ≤ Subgroup.zpowers (a ^ 2) := by
  intro x hx
  obtain ⟨i, rfl | rfl⟩ := hnf x
  · have hr : a ^ (i % 2) ∈ H := by
      have ht := H.mul_mem (H.inv_mem (H.pow_mem hsq (i / 2))) hx
      simpa [pow_parity a i, mul_assoc] using ht
    have hi : i % 2 = 0 := by
      have : i % 2 < 2 := Nat.mod_lt i (by decide)
      by_contra h
      have : i % 2 = 1 := by omega
      exact ha (by simpa [this] using hr)
    rw [pow_parity a i, hi, pow_zero, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · have hr : a ^ (i % 2) * b ∈ H := by
      have ht := H.mul_mem (H.inv_mem (H.pow_mem hsq (i / 2))) hx
      simpa [pow_parity a i, mul_assoc] using ht
    have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases hi with hi | hi
    · exact (hb (by simpa [hi] using hr)).elim
    · exact (hab (by simpa [hi] using hr)).elim

private theorem maximal_eq_three (a b : G)
    (hC : IsCoatom (Subgroup.zpowers a))
    (hD : IsCoatom (Subgroup.closure ({a^2,b} : Set G)))
    (hQ : IsCoatom (Subgroup.closure ({a^2,a*b} : Set G)))
    (hnf : ∀ x : G, ∃ i : ℕ, x = a ^ i ∨ x = a ^ i * b)
    (H : Subgroup G) (hH : IsCoatom H) (hsq : a^2 ∈ H) :
    H = Subgroup.zpowers a ∨ H = Subgroup.closure ({a^2,b} : Set G) ∨
      H = Subgroup.closure ({a^2,a*b} : Set G) := by
  by_cases ha : a ∈ H
  · left
    have hle : Subgroup.zpowers a ≤ H := (Subgroup.zpowers_le).mpr ha
    exact le_antisymm ((isCoatom_iff_ge_of_le.mp hC).2 H hH.1 hle) hle
  by_cases hb : b ∈ H
  · right; left
    have hle : Subgroup.closure ({a^2,b} : Set G) ≤ H := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> assumption
    exact le_antisymm ((isCoatom_iff_ge_of_le.mp hD).2 H hH.1 hle) hle
  by_cases hab : a*b ∈ H
  · right; right
    have hle : Subgroup.closure ({a^2,a*b} : Set G) ≤ H := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> assumption
    exact le_antisymm ((isCoatom_iff_ge_of_le.mp hQ).2 H hH.1 hle) hle
  have hle := outside_three_le_squares a b H hsq ha hb hab hnf
  have hCsup : H < Subgroup.zpowers a := by
    refine lt_of_le_of_ne (hle.trans ?_) ?_
    · exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
    · intro heq
      exact ha (heq ▸ Subgroup.mem_zpowers a)
  exact (hC.1 (hH.2 _ hCsup)).elim

private theorem coatom_of_index_two (H : Subgroup G) (hi : H.index = 2) :
    IsCoatom H := by
  have : H.FiniteIndex := ⟨by omega⟩
  refine ⟨?_, ?_⟩
  · intro ht
    simp [ht] at hi
  · intro K hK
    have hklt := Subgroup.index_strictAnti hK
    have hkdvd := Subgroup.index_dvd_of_le hK.le
    rw [hi] at hklt hkdvd
    have : K.index = 1 := by
      rcases Nat.prime_two.eq_one_or_self_of_dvd K.index hkdvd with h | h
      · exact h
      · omega
    exact Subgroup.index_eq_one.mp this

private theorem top_of_generators (a b : G)
    (hgen : Subgroup.closure ({a,b} : Set G) = ⊤)
    (H : Subgroup G) (ha : a ∈ H) (hb : b ∈ H) : H = ⊤ := by
  apply top_unique
  rw [← hgen, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> assumption

private theorem three_distinct (a b : G)
    (hgen : Subgroup.closure ({a,b} : Set G) = ⊤)
    (hC : Subgroup.zpowers a ≠ ⊤)
    (hD : Subgroup.closure ({a^2,b} : Set G) ≠ ⊤) :
    Subgroup.zpowers a ≠ Subgroup.closure ({a^2,b} : Set G) ∧
    Subgroup.zpowers a ≠ Subgroup.closure ({a^2,a*b} : Set G) ∧
    Subgroup.closure ({a^2,b} : Set G) ≠ Subgroup.closure ({a^2,a*b} : Set G) := by
  have hb : b ∈ Subgroup.closure ({a^2,b} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hab : a*b ∈ Subgroup.closure ({a^2,a*b} : Set G) :=
    Subgroup.subset_closure (by simp)
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    exact hC (top_of_generators a b hgen _ (Subgroup.mem_zpowers _) (heq ▸ hb))
  · intro heq
    have hb' : b ∈ Subgroup.zpowers a := by
      have h := (Subgroup.zpowers a).mul_mem
        ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers _)) (heq ▸ hab)
      simpa [mul_assoc] using h
    exact hC (top_of_generators a b hgen _ (Subgroup.mem_zpowers _) hb')
  · intro heq
    have ha : a ∈ Subgroup.closure ({a^2,b} : Set G) := by
      have h := (Subgroup.closure ({a^2,b} : Set G)).mul_mem
        (heq ▸ hab) ((Subgroup.closure ({a^2,b} : Set G)).inv_mem hb)
      simpa [mul_assoc] using h
    exact hD (top_of_generators a b hgen _ ha hb)

/-- The three explicit, distinct maximal subgroups and their standard group types. -/
public theorem maximal_subgroups {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (hcard : Nat.card G = 2^n)
    (ha : orderOf a = 2^(n-1)) (hb : orderOf b = 2)
    (hconj : b*a*b⁻¹ = a^(2^(n-2)-1))
    (hgen : Subgroup.closure ({a,b} : Set G) = ⊤) :
    let C := Subgroup.zpowers a
    let D := Subgroup.closure ({a^2,b} : Set G)
    let Q := Subgroup.closure ({a^2,a*b} : Set G)
    C ≠ D ∧ C ≠ Q ∧ D ≠ Q ∧
      (∀ H : Subgroup G, IsCoatom H ↔ H = C ∨ H = D ∨ H = Q) ∧
      IsCyclic C ∧ Nonempty (D ≃* DihedralGroup (2^(n-2))) ∧
        Nonempty (Q ≃* QuaternionGroup (2^(n-3))) := by
  have hf := (derived_eq_frattini hn hcard a b ha hb hconj hgen).2.1
  have hm := explicit_subgroup_models hn a b hcard ha hb hconj hgen
  dsimp only at hm ⊢
  obtain ⟨hCi,hDi,hQi,hcyc,hdi,hqu⟩ := hm
  have hC := coatom_of_index_two _ hCi
  have hD := coatom_of_index_two _ hDi
  have hQ := coatom_of_index_two _ hQi
  obtain ⟨hCD,hCQ,hDQ⟩ := three_distinct a b hgen hC.1 hD.1
  refine ⟨hCD,hCQ,hDQ,?_,hcyc,hdi,hqu⟩
  intro H
  constructor
  · intro hH
    refine maximal_eq_three a b hC hD hQ ?_ H hH ?_
    · intro x
      obtain ⟨i,hi,hx⟩ := normal_form a b (2^(n-1)) (2^(n-2)-1)
        (by positivity) ha (by rw [← hb]; exact pow_orderOf_eq_one b) hconj hgen x
      exact ⟨i,hx⟩
    · apply frattini_le_coatom hH
      rw [hf]
      exact Subgroup.mem_zpowers _
  · rintro (rfl | rfl | rfl)
    · exact hC
    · exact hD
    · exact hQ

end ABG.QuasiDihedral
