module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Transporters for the intersection-generated subgroup

A conjugator taking a nonidentity member of either factor into either factor
is one of the generators of H. Once the union is strongly closed in S, this
puts S in H. Sylow conjugacy inside H then proves the unique fixed-point
assertion (f) for every nonidentity factor element, not only involutions.
The remaining lemmas express the elementary transporter reductions preceding
(b) and the fixed-point criterion (a).

Source: Aschbacher, *On finite groups of component type* (1975),
Lemma 3.4, pp.94–96, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- The subgroup version of a unique fixed point in the coset action. -/
def UniqueSubgroupConjugateMembership (H X : Subgroup G) : Prop :=
  X ≤ H ∧ ∀ g : G, conjugate X g ≤ H ↔ g ∈ H

/-- The normalizer and conjugacy criterion in source part (a). -/
theorem uniqueSubgroupConjugateMembership_iff {H X : Subgroup G} (hX : X ≤ H) :
    UniqueSubgroupConjugateMembership H X ↔
      normalizer (X : Set G) ≤ H ∧
      ∀ g : G, conjugate X g ≤ H → ∃ h ∈ H, conjugate X g = conjugate X h := by
  constructor
  · intro hu
    constructor
    · intro g hg
      apply (hu.2 g).mp
      rwa [(mem_normalizer_iff_conjugate_eq X g).mp hg]
    · intro g hg
      exact ⟨g, (hu.2 g).mp hg, rfl⟩
  · rintro ⟨hN, hf⟩
    refine ⟨hX, fun g => ⟨?_, ?_⟩⟩
    · intro hg
      obtain ⟨h, hh, he⟩ := hf g hg
      have hn : g * h⁻¹ ∈ normalizer (X : Set G) := by
        apply (mem_normalizer_iff_conjugate_eq X _).mpr
        rw [← conjugate_conjugate, he, conjugate_conjugate, mul_inv_cancel, conjugate_one]
      simpa using H.mul_mem (hN hn) hh
    · intro hg
      rintro x ⟨y, hy, rfl⟩
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) (hX hy)) (H.inv_mem (H.inv_mem hg))

/-- Every nontrivial element transporter between the factors generates H. -/
theorem transporter_mem_intersectionGenerated {a g : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) (hne : a ≠ 1)
    (hag : g⁻¹ * a * g ∈ (A₁ : Set G) ∪ A₂) :
    g ∈ intersectionGenerated A₁ A₂ := by
  have repr : ∀ x ∈ (A₁ : Set G) ∪ A₂,
      ∃ C ∈ ({A₁, A₂} : Set (Subgroup G)), x ∈ C := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨A₁, by simp, hx⟩
    · exact ⟨A₂, by simp, hx⟩
  obtain ⟨C, hC, haC⟩ := repr a ha
  obtain ⟨D, hD, hagD⟩ := repr _ hag
  apply Subgroup.subset_closure
  refine ⟨C, hC, D, hD, ?_⟩
  intro he
  have hm : g⁻¹ * a * g ∈ conjugate C g ⊓ D :=
    ⟨Subgroup.mem_map.mpr ⟨a, haC, by simp⟩, hagD⟩
  rw [he, Subgroup.mem_bot] at hm
  apply hne
  calc
    a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    _ = g * 1 * g⁻¹ := congrArg (fun x => g * x * g⁻¹) hm
    _ = 1 := by simp

/-- The set-containment clause of (*) already puts the union in H. -/
theorem Hypotheses.union_subset_generated (h : Hypotheses S A₁ A₂) :
    (A₁ : Set G) ∪ A₂ ⊆ intersectionGenerated A₁ A₂ :=
  fun _ hx => (h.closed_in_generated.1 hx).1

/-- The rank hypothesis excludes the trivial left factor. -/
theorem Hypotheses.left_ne_bot [Finite G] (h : Hypotheses S A₁ A₂) : A₁ ≠ ⊥ := by
  obtain ⟨E, hE, _⟩ := h.left_rank
  have hc := Subgroup.card_le_card_group E
  rw [hE] at hc
  intro he
  rw [he] at hc
  simp at hc

/-- The rank hypothesis excludes the trivial right factor. -/
theorem Hypotheses.right_ne_bot [Finite G] (h : Hypotheses S A₁ A₂) : A₂ ≠ ⊥ := by
  obtain ⟨E, hE, _⟩ := h.right_rank
  have hc := Subgroup.card_le_card_group E
  rw [hE] at hc
  intro he
  rw [he] at hc
  simp at hc

/-- The first normalizer clause of (*) controls the whole transporter. -/
theorem Hypotheses.transporter_mem_of_left_normalizer (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (hne : a ≠ 1)
    (hag : g⁻¹ * a * g ∈ (S : Subgroup G) ⊓ normalizer (A₁ : Set G)) :
    g ∈ intersectionGenerated A₁ A₂ :=
  transporter_mem_intersectionGenerated ha hne
    (h.closed_in_left_normalizer.2 a ha g (Subgroup.mem_top g) hag)

/-- The second normalizer clause of (*) gives the symmetric transporter bound. -/
theorem Hypotheses.transporter_mem_of_right_normalizer (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (hne : a ≠ 1)
    (hag : g⁻¹ * a * g ∈ (S : Subgroup G) ⊓ normalizer (A₂ : Set G)) :
    g ∈ intersectionGenerated A₁ A₂ :=
  transporter_mem_intersectionGenerated ha hne
    (h.closed_in_right_normalizer.2 a ha g (Subgroup.mem_top g) hag)

/-- A nontrivial subgroup of either factor has its normalizer in H. -/
theorem normalizer_le_generated_of_le_factor {X : Subgroup G}
    (hX : X ≤ A₁ ∨ X ≤ A₂) (hne : X ≠ ⊥) :
    normalizer (X : Set G) ≤ intersectionGenerated A₁ A₂ := by
  obtain ⟨a, hane⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hne)
  have ha : (a : G) ∈ X := a.property
  have hane' : (a : G) ≠ 1 := by exact_mod_cast hane
  have hu : ∀ x ∈ X, x ∈ (A₁ : Set G) ∪ A₂ := by
    intro x hx
    exact hX.elim (fun h => Or.inl (h hx)) (fun h => Or.inr (h hx))
  intro g hg
  apply transporter_mem_intersectionGenerated (hu (a : G) ha) hane'
  apply hu
  have hm : g⁻¹ * (a : G) * g ∈ conjugate X g :=
    Subgroup.mem_map.mpr ⟨(a : G), ha, by simp⟩
  rwa [(mem_normalizer_iff_conjugate_eq X g).mp hg] at hm

/-- Global strong closure puts the whole Sylow subgroup in H. -/
theorem Hypotheses.sylow_le_generated_of_closed [Finite G] (h : Hypotheses S A₁ A₂)
    (hclosed : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤) :
    (S : Subgroup G) ≤ intersectionGenerated A₁ A₂ := by
  obtain ⟨a, hane⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp h.left_ne_bot)
  have ha : (a : G) ∈ A₁ := a.property
  have hane' : (a : G) ≠ 1 := by exact_mod_cast hane
  intro g hg
  apply transporter_mem_intersectionGenerated (Or.inl ha) hane'
  apply hclosed.2 a (Or.inl ha) g (Subgroup.mem_top g)
  exact (S : Subgroup G).mul_mem
    ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hg) (h.left_le ha)) hg

/-- Source (f) follows from (e) by Sylow conjugacy inside H. -/
theorem Hypotheses.unique_of_closed [Finite G] (h : Hypotheses S A₁ A₂)
    (hclosed : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    {a : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (hne : a ≠ 1) :
    UniqueConjugateMembership (intersectionGenerated A₁ A₂) a := by
  let H := intersectionGenerated A₁ A₂
  have haH : a ∈ H := h.union_subset_generated ha
  have hSH : (S : Subgroup G) ≤ H := h.sylow_le_generated_of_closed hclosed
  refine ⟨haH, fun g => ⟨?_, fun hg => H.mul_mem (H.mul_mem (H.inv_mem hg) haH) hg⟩⟩
  intro hag
  have haS : a ∈ S := hclosed.1 ha
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_orderOf_eq_pow (⟨a, haS⟩ : S)
  have hn' : orderOf (⟨g⁻¹ * a * g, hag⟩ : H) = 2 ^ n := by
    rw [Subgroup.orderOf_mk]
    calc
      orderOf (g⁻¹ * a * g) = orderOf a := by
        simpa [MulAut.conj_apply] using (MulAut.conj g⁻¹).orderOf_eq a
      _ = orderOf (⟨a, haS⟩ : S) := by
        exact Subgroup.orderOf_coe (⟨a, haS⟩ : S)
      _ = 2 ^ n := hn
  obtain ⟨b, hb⟩ := (S.subtype hSH).exists_isConj_of_orderOf_eq_prime_pow hn'
  obtain ⟨k, hk⟩ := isConj_iff.mp hb
  have hk' : (k : G) * (g⁻¹ * a * g) * (k : G)⁻¹ = ((b : H) : G) :=
    congrArg Subtype.val hk
  have hak : (g * (k : G)⁻¹)⁻¹ * a * (g * (k : G)⁻¹) ∈ S := by
    have he : (g * (k : G)⁻¹)⁻¹ * a * (g * (k : G)⁻¹) = ((b : H) : G) := by
      rw [← hk']
      group
    rw [he]
    exact b.property
  have hmem : g * (k : G)⁻¹ ∈ H :=
    transporter_mem_intersectionGenerated ha hne
      (hclosed.2 a ha _ (Subgroup.mem_top _) hak)
  simpa using H.mul_mem hmem k.property

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
