module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Setup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers

/-!
# Conditional critical-fusion API and source-proof entry point

The declarations in namespace `Input` below are legacy conditional deductions,
not proofs of 14.7.66–70 from the book's hypotheses. Their record assumes
substantial portions of those conclusions and misstates several source
conditions. They are preserved for compatibility. Source-faithful work is
separate, in `CriticalFusion.SourceSetup` and the `Source` descendants.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemmas 14.7.66--70, printed pp.1070--1074 (PDF pp.1087--1090).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion

open Subgroup
open scoped commutatorElement

variable {G Gs : Type*} [Group G] [Finite G] [Group Gs] [Finite Gs]

/-- The ambient conjugacy class of the distinguished involution. -/
def conjugacyClass (z : G) : Set G :=
  {x | ∃ g : G, x = g * z * g⁻¹}

namespace Input

variable (i : Input (G := G) (Gs := Gs))

omit [Finite G] [Finite Gs] in
private theorem star_Uα_le_QStar :
    starImage i.star i.Uα ≤ starImage i.star i.Q := by
  have h : starImage i.star i.Uα ≤ starImage i.star i.R₁ :=
    Subgroup.map_mono i.Uα_le_R₁
  rw [i.QStar_eq_R₁Star]
  exact h

omit [Finite G] [Finite Gs] in
/-- Lemma 14.7.66: the actual image of the critical conjugate lies in the
marked Sylow two subgroup `Q* = R₁*`. -/
theorem lemma_14_7_66 :
    starImage i.star i.Uα ≤ starImage i.star i.Q ∧
      IsSylowTwoIn (starImage i.star i.Q) (starImage i.star i.K) := by
  refine ⟨star_Uα_le_QStar i, ?_⟩
  rw [i.QStar_eq_R₁Star]
  exact i.R₁Star_is_sylow

omit [Finite G] [Finite Gs] in
/-- Lemma 14.7.67(1)--(5): normalizer and hyperplane fusion.  The
hyperplane clause is the literal `V^g` uniqueness statement. -/
theorem lemma_14_7_67 :
    i.G₂ ≤ i.M ∧
      (∀ F : Subgroup G, F ≤ i.V → Nat.card F = 4 →
        ∀ g : G, F ≤ conjugateBy i.V g → conjugateBy i.V g = i.V) ∧
      IsLStar i.LStar i.K ∧
      normalizer (i.K : Set G) = i.H ∧ i.H ≤ i.M ∧
      i.L ⊔ i.T = normalizer (i.V : Set G) := by
  have hG₂ : i.G₂ ≤ i.M := i.G₂_le_normalizer_V₂.trans i.normalizer_V₂_le_M
  have hK : normalizer (i.K : Set G) = i.H :=
    le_antisymm i.normalizer_K_le_H i.H_le_normalizer_K
  have hV : i.L ⊔ i.T = normalizer (i.V : Set G) :=
    le_antisymm i.LT_le_normalizer_V i.normalizer_V_le_LT
  exact ⟨hG₂, i.hyperplane_unique, i.lt_star, hK, i.H_le_M, hV⟩

omit [Finite G] [Finite Gs] in
private theorem centralizes_z (i : Input (G := G) (Gs := Gs)) {g : G}
    (hg : g ∈ i.H) : g * i.z * g⁻¹ = i.z := by
  have hc : g ∈ centralizer ({i.z} : Set G) := by
    rw [← i.H_eq_centralizer_z]
    exact hg
  calc
    g * i.z * g⁻¹ = i.z * g * g⁻¹ := by rw [← hc i.z (by simp)]
    _ = i.z := by simp

omit [Finite G] [Finite Gs] in
private theorem z_mem_conjugate_inverse (i : Input (G := G) (Gs := Gs))
    {g : G} (hx : g * i.z * g⁻¹ ∈ i.U₀) :
    i.z ∈ conjugateBy i.U₀ g⁻¹ := by
  apply Subgroup.mem_map.mpr
  refine ⟨g * i.z * g⁻¹, hx, ?_⟩
  change (MulAut.conj g⁻¹) (g * i.z * g⁻¹) = i.z
  rw [MulAut.conj_apply]
  group

omit [Finite G] [Finite Gs] in
/-- Lemma 14.7.68(1): the distinguished conjugacy class meets the fixed
preimage in exactly the distinguished involution. -/
theorem lemma_14_7_68_one :
    conjugacyClass i.z ∩ (i.U₀ : Set G) = ({i.z} : Set G) := by
  ext x
  constructor
  · rintro ⟨⟨g, rfl⟩, hx⟩
    have hz' : i.z ∈ conjugateBy i.U₀ g⁻¹ :=
      z_mem_conjugate_inverse i hx
    have hg : g⁻¹ ∈ i.H := i.z_conjugate_mem_implies_H g⁻¹ hz'
    have hgg : g ∈ i.H := by simpa using Subgroup.inv_mem i.H hg
    have hgc : g * i.z * g⁻¹ = i.z := centralizes_z i hgg
    simpa only [Set.mem_singleton_iff] using hgc
  · intro hx
    have : x = i.z := by simpa only [Set.mem_singleton_iff] using hx
    subst this
    exact ⟨⟨1, by simp⟩, i.z_mem_U₀⟩

omit [Finite G] [Finite Gs] in
/-- The fixed-element fusion conclusion used in Lemma 14.7.68(2). -/
theorem fixed_element_centralizer_le (u : G) (hu : u ∈ i.U₀)
    (hne : u ≠ 1) (hfixed : i.fixed_mod_V₁ u) :
    centralizer ({u} : Set G) ≤ i.H :=
  i.centralizer_fixed_le_H u hu hne hfixed

omit [Finite G] [Finite Gs] in
/-- Lemma 14.7.68(2): fixed nonidentity elements have centralizer in `H`, and
the fixed-space preimage is the unique conjugate containing them. -/
theorem lemma_14_7_68_two (u : G) (hu : u ∈ i.U₀) (hne : u ≠ 1)
    (hfixed : i.fixed_mod_V₁ u) :
    centralizer ({u} : Set G) ≤ i.H ∧
      ∀ g : G, u ∈ conjugateBy i.U₀ g → conjugateBy i.U₀ g = i.U₀ := by
  refine ⟨i.centralizer_fixed_le_H u hu hne hfixed, ?_⟩
  intro g hUg
  have hg : g ∈ i.H := i.unique_U₀_of_fixed u hu hne hfixed g hUg
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (i.H_normalizes_U₀ hg)

omit [Finite G] in
private theorem star_card_bounds (i : Input (G := G) (Gs := Gs)) :
    1 < Nat.card (starImage i.star i.Uα) ∧
      Nat.card (starImage i.star i.Uα) < 4 ∧
      Nat.card (starImage i.star i.Uα) ∣ 4 := by
  have hle : starImage i.star i.Uα ≤ starImage i.star i.Q :=
    star_Uα_le_QStar i
  have hcard_le : Nat.card (starImage i.star i.Uα) ≤ 4 := by
    rw [← i.QStar_card]
    exact Subgroup.card_le_of_le hle
  have hne_one : Nat.card (starImage i.star i.Uα) ≠ 1 := by
    intro h
    apply i.UαStar_nontrivial
    exact Subgroup.card_eq_one.mp h
  have hgt : 1 < Nat.card (starImage i.star i.Uα) := by
    apply Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos))
    exact fun h => hne_one h.symm
  have hne_four : Nat.card (starImage i.star i.Uα) ≠ 4 := by
    intro h
    apply i.UαStar_ne_QStar
    have hcard : Nat.card (starImage i.star i.Q) ≤
        Nat.card (starImage i.star i.Uα) := by
      simp [i.QStar_card, h]
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  have hlt : Nat.card (starImage i.star i.Uα) < 4 :=
    Nat.lt_of_le_of_ne hcard_le hne_four
  have hdvd := Subgroup.card_dvd_of_le hle
  have hdvd' : Nat.card (starImage i.star i.Uα) ∣ 4 := by
    simpa [i.QStar_card] using hdvd
  exact ⟨hgt, hlt, hdvd'⟩

omit [Finite G] in
/-- Lemma 14.7.69: the actual critical image has order two.  The order is
forced from the literal subgroup inclusion, nontriviality, and exclusion of
the full marked four-group. -/
theorem lemma_14_7_69 : Nat.card (starImage i.star i.Uα) = 2 := by
  obtain ⟨hgt, hlt, hdvd⟩ := star_card_bounds i
  have hn : Nat.card (starImage i.star i.Uα) = 2 ∨
      Nat.card (starImage i.star i.Uα) = 3 := by omega
  rcases hn with h2 | h3
  · exact h2
  · exfalso
    rw [h3] at hdvd
    norm_num at hdvd

omit [Finite G] [Finite Gs] in
/-- The intersection equalities in Lemma 14.7.70(3), assembled from the
literal containments supplied by the critical-pair calculation. -/
private theorem intersection_equalities (i : Input (G := G) (Gs := Gs)) :
    i.U ⊓ i.Uα = i.U₀ ⊔ i.V ∧
      i.U ⊓ i.Uα = ⁅i.U, i.Uα⁆ ⊔ i.V ∧
      i.U ⊓ i.Uα = ⁅i.U, i.Uα⁆ ⊔ i.U₀ := by
  refine ⟨le_antisymm i.inter_le_U₀_sup_V i.U₀_sup_V_le_inter, ?_, ?_⟩
  · exact le_antisymm i.inter_le_comm_sup_V i.comm_sup_V_le_inter
  · exact le_antisymm i.inter_le_comm_sup_U₀ i.comm_sup_U₀_le_inter

omit [Finite G] [Finite Gs] in
/-- Lemma 14.7.70(1)--(4).  The permitted conjugator is returned as actual
data, and `Uα ∈ U^L` is proved from its literal conjugation equation. -/
theorem lemma_14_7_70 :
    (∃ p : PermittedConjugate i.U i.V₂ i.L, p.Zα ≤ i.V₂) ∧
      i.twoRank i.U₀ ≤ 2 ∧
      (i.U ⊓ i.Uα = i.U₀ ⊔ i.V ∧
        i.U ⊓ i.Uα = ⁅i.U, i.Uα⁆ ⊔ i.V ∧
        i.U ⊓ i.Uα = ⁅i.U, i.Uα⁆ ⊔ i.U₀) ∧
      i.b = 3 ∧ (∃ g : G, g ∈ i.L ∧ i.Uα = conjugateBy i.U g) := by
  obtain ⟨p⟩ := i.permitted
  have hrank : i.twoRank i.U₀ ≤ 2 := by
    by_contra h
    have hge : 3 ≤ i.twoRank i.U₀ := by omega
    have hle := i.U₀_rank_le_three
    have heq : i.twoRank i.U₀ = 3 := by omega
    exact i.rank_three_obstruction heq
  have hcard : i.b = 3 := by
    have hle := i.b_le_three_of_permitted p
    have hge := i.b_ge_three
    omega
  have hconj : ∃ g : G, g ∈ i.L ∧ i.Uα = conjugateBy i.U g := by
    refine ⟨i.criticalConjugator, ?_, i.Uα_eq_critical_conjugate⟩
    exact i.criticalConjugator_mem_L
  obtain ⟨hI, hIV, hIU⟩ := intersection_equalities i
  exact ⟨⟨p, p.Zα_le_V₂⟩, hrank, ⟨hI, hIV, hIU⟩, hcard, hconj⟩

/-- The complete conditional package for the source branch. -/
structure Result where
  image_le_sylow : starImage i.star i.Uα ≤ starImage i.star i.Q
  q_is_sylow : IsSylowTwoIn (starImage i.star i.Q) (starImage i.star i.K)
  g₂_le_M : i.G₂ ≤ i.M
  hyperplane_unique : ∀ F : Subgroup G, F ≤ i.V → Nat.card F = 4 →
    ∀ g : G, F ≤ conjugateBy i.V g → conjugateBy i.V g = i.V
  k_mem_LStar : IsLStar i.LStar i.K
  normalizer_K : normalizer (i.K : Set G) = i.H
  H_mem_M : i.H ≤ i.M
  normalizer_V : i.L ⊔ i.T = normalizer (i.V : Set G)
  z_class_intersection : conjugacyClass i.z ∩ (i.U₀ : Set G) = ({i.z} : Set G)
  fixed_centralizer : ∀ u : G, u ∈ i.U₀ → u ≠ 1 → i.fixed_mod_V₁ u →
    centralizer ({u} : Set G) ≤ i.H
  fixed_unique : ∀ u : G, u ∈ i.U₀ → u ≠ 1 → i.fixed_mod_V₁ u →
    ∀ g : G, u ∈ conjugateBy i.U₀ g → conjugateBy i.U₀ g = i.U₀
  image_order_two : Nat.card (starImage i.star i.Uα) = 2
  permitted : ∃ p : PermittedConjugate i.U i.V₂ i.L, p.Zα ≤ i.V₂
  rank_U₀ : i.twoRank i.U₀ ≤ 2
  intersections : i.U ⊓ i.Uα = i.U₀ ⊔ i.V ∧
    i.U ⊓ i.Uα = ⁅i.U, i.Uα⁆ ⊔ i.V ∧
    i.U ⊓ i.Uα = ⁅i.U, i.Uα⁆ ⊔ i.U₀
  b_eq_three : i.b = 3
  Uα_mem_UL : ∃ g : G, g ∈ i.L ∧ i.Uα = conjugateBy i.U g

omit [Finite G] in
/-- Assemble Lemmas 14.7.66--70 from the literal earlier source contracts. -/
theorem assemble : Result i := by
  obtain ⟨h66, hsyl⟩ := i.lemma_14_7_66
  obtain ⟨hg₂, hhyper, hk, hnormK, hM, hnormV⟩ := i.lemma_14_7_67
  obtain ⟨hz, hzu⟩ := i.lemma_14_7_68_two i.z i.z_mem_U₀ i.z_ne_one
    i.z_fixed_mod_V₁
  obtain ⟨p, hp⟩ := i.permitted
  obtain ⟨hpermitted, hrank, hinter, hb, hUL⟩ := i.lemma_14_7_70
  exact
    { image_le_sylow := h66
      q_is_sylow := hsyl
      g₂_le_M := hg₂
      hyperplane_unique := hhyper
      k_mem_LStar := hk
      normalizer_K := hnormK
      H_mem_M := hM
      normalizer_V := hnormV
      z_class_intersection := i.lemma_14_7_68_one
      fixed_centralizer := fun u hu hne hf => i.fixed_element_centralizer_le u hu hne hf
      fixed_unique := fun u hu hne hf => (i.lemma_14_7_68_two u hu hne hf).2
      image_order_two := i.lemma_14_7_69
      permitted := hpermitted
      rank_U₀ := hrank
      intersections := hinter
      b_eq_three := hb
      Uα_mem_UL := hUL }

end Input

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion

end
