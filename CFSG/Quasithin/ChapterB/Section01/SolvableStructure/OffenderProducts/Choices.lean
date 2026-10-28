module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Internal
public import Mathlib.GroupTheory.Sylow

/-!
# Actual Sylow choices in the internal factors

A choice is either the trivial subgroup or the inclusion-image of a Sylow
2-subgroup of an actual factor. A product is the join of these commuting,
independent choices and must have a nontrivial coordinate. These definitions
record the right-hand side of B.1.8(4); they do not assert its equivalence with
being an offender.

The concrete SL₂(2) equivalence gives factor order six and Sylow order two.
A six-word calculation proves that the conjugates of each Sylow subgroup
generate its factor, as used in the valid first assertion of B.1.8(5).

Source: Aschbacher–Smith, printed p. 70 (PDF p. 81).
-/

@[expose] public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

/-- Inclusion-image of a genuine Sylow subgroup of the factor. -/
def factorSylow (i : Fin d.count) (S : Sylow 2 (d.factor i)) : Subgroup G :=
  (S : Subgroup (d.factor i)).map (d.factor i).subtype

/-- A trivial coordinate or an actual factor Sylow subgroup. -/
def IsSylowChoice (i : Fin d.count) (A : Subgroup G) : Prop :=
  A = ⊥ ∨ ∃ S : Sylow 2 (d.factor i), A = d.factorSylow i S

/-- A nonempty product of Sylow choices in distinct internal factors. -/
def IsSylowProduct (A : Subgroup G) : Prop :=
  ∃ choices : Fin d.count → Subgroup G,
    (∀ i, d.IsSylowChoice i (choices i)) ∧
      (∃ i, choices i ≠ ⊥) ∧ A = ⨆ i, choices i

theorem factorSylow_le (i : Fin d.count) (S : Sylow 2 (d.factor i)) :
    d.factorSylow i S ≤ d.factor i := by
  rintro x ⟨s, _, rfl⟩
  exact s.property

theorem IsSylowChoice.le {i : Fin d.count} {A : Subgroup G}
    (h : d.IsSylowChoice i A) : A ≤ d.factor i := by
  rcases h with rfl | ⟨S, rfl⟩
  · exact bot_le
  · exact d.factorSylow_le i S

theorem factor_card (i : Fin d.count) : Nat.card (d.factor i) = 6 := by
  rw [Nat.card_congr (d.factorModel i).toEquiv, Nat.card_eq_fintype_card]
  decide

theorem factorSylow_card (i : Fin d.count) (S : Sylow 2 (d.factor i)) :
    Nat.card (d.factorSylow i S) = 2 := by
  let : Finite (d.factor i) := Finite.of_equiv _ (d.factorModel i).toEquiv.symm
  rw [factorSylow, Subgroup.card_map_of_injective Subtype.val_injective]
  change Nat.card S = 2
  rw [S.card_eq_multiplicity, d.factor_card]
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide),
    Nat.prime_two.factorization, Nat.prime_three.factorization]
  norm_num

theorem factorSylow_ne_bot (i : Fin d.count) (S : Sylow 2 (d.factor i)) :
    d.factorSylow i S ≠ ⊥ := by
  intro h
  have hc := d.factorSylow_card i S
  rw [h, Subgroup.card_bot] at hc
  omega

theorem factorSylow_isSylowProduct (i : Fin d.count) (S : Sylow 2 (d.factor i)) :
    d.IsSylowProduct (d.factorSylow i S) := by
  classical
  refine ⟨fun j => if j = i then d.factorSylow i S else ⊥, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j = i
    · subst j
      simp only [ite_true]
      exact Or.inr ⟨S, rfl⟩
    · simp only [h, ite_false]
      exact Or.inl rfl
  · exact ⟨i, by simpa only [ite_true] using d.factorSylow_ne_bot i S⟩
  · apply le_antisymm
    · simpa only [ite_true] using
        (le_iSup (fun j => if j = i then d.factorSylow i S else ⊥) i)
    · apply iSup_le
      intro j
      dsimp only
      split_ifs <;> simp

theorem IsSylowProduct.ne_bot {A : Subgroup G} (h : d.IsSylowProduct A) : A ≠ ⊥ := by
  obtain ⟨choices, _, ⟨i, hi⟩, rfl⟩ := h
  intro he
  exact hi (bot_unique (he ▸ le_iSup choices i))

theorem IsSylowProduct.le_offenderSubgroup {A : Subgroup G} (h : d.IsSylowProduct A) :
    A ≤ offenderSubgroup ρ := by
  obtain ⟨choices, hc, _, rfl⟩ := h
  exact iSup_le fun i => (IsSylowChoice.le d (hc i)).trans (d.factor_le_offenderSubgroup i)

private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private theorem involution_words : ∀ t : SL, t ≠ 1 → t ^ 2 = 1 →
    ∃ g : SL, ∀ x : SL,
      let u := g * t * g⁻¹
      x = 1 ∨ x = t ∨ x = u ∨ x = t * u ∨ x = u * t ∨ x = t * u * t := by
  decide

/-- Each Sylow subgroup normally generates its own factor, using conjugation
by actual elements of that factor. -/
theorem factorSylow_conjugates_generate (i : Fin d.count) (S : Sylow 2 (d.factor i)) :
    (⨆ g : d.factor i, (d.factorSylow i S).map
      (MulAut.conj (g : G)).toMonoidHom) = d.factor i := by
  let Q := ⨆ g : d.factor i, (d.factorSylow i S).map
    (MulAut.conj (g : G)).toMonoidHom
  have hSQ : ∀ g : d.factor i, ∀ a ∈ d.factorSylow i S,
      (g : G) * a * (g : G)⁻¹ ∈ Q := by
    intro g a ha
    exact (le_iSup (fun g : d.factor i => (d.factorSylow i S).map
      (MulAut.conj (g : G)).toMonoidHom) g) ⟨a, ha, rfl⟩
  apply le_antisymm
  · refine iSup_le fun g => ?_
    rintro x ⟨a, ha, rfl⟩
    exact (d.factor i).mul_mem
      ((d.factor i).mul_mem g.property (d.factorSylow_le i S ha))
      ((d.factor i).inv_mem g.property)
  · have hc : Nat.card S = 2 := by
      have := d.factorSylow_card i S
      rwa [factorSylow, Subgroup.card_map_of_injective Subtype.val_injective] at this
    have hS : (S : Subgroup (d.factor i)) ≠ ⊥ := by
      intro h
      have : Nat.card S = 1 := Subgroup.card_eq_one.mpr h
      omega
    obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS
    have ht2 : (t : d.factor i) ^ 2 = 1 := by
      have h : t ^ 2 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := t))
      exact congrArg Subtype.val h
    have htm : d.factorModel i (t : d.factor i) ≠ 1 := by
      intro h
      apply ht
      apply Subtype.ext
      exact (d.factorModel i).injective (h.trans (map_one _).symm)
    obtain ⟨g, hwords⟩ := involution_words (d.factorModel i (t : d.factor i)) htm
      (by rw [← map_pow, ht2, map_one])
    let b := (d.factorModel i).symm g
    have hb : d.factorModel i b = g := (d.factorModel i).apply_symm_apply g
    have htQ : (t : G) ∈ Q := by
      simpa using hSQ 1 (t : G) ⟨t, t.property, rfl⟩
    have huQ : (b : G) * (t : G) * (b : G)⁻¹ ∈ Q :=
      hSQ b (t : G) ⟨t, t.property, rfl⟩
    intro x hx
    have hxwords := hwords (d.factorModel i ⟨x, hx⟩)
    change _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ at hxwords
    rw [← hb] at hxwords
    simp only [← map_mul, ← map_inv, ← map_one (d.factorModel i),
      (d.factorModel i).injective.eq_iff] at hxwords
    rcases hxwords with h | h | h | h | h | h
    · have : x = 1 := congrArg Subtype.val h
      rw [this]
      exact Q.one_mem
    · have : x = (t : G) := congrArg Subtype.val h
      rw [this]
      exact htQ
    · have : x = (b : G) * (t : G) * (b : G)⁻¹ := congrArg Subtype.val h
      rw [this]
      exact huQ
    · have : x = (t : G) * ((b : G) * (t : G) * (b : G)⁻¹) := congrArg Subtype.val h
      rw [this]
      exact Q.mul_mem htQ huQ
    · have : x = ((b : G) * (t : G) * (b : G)⁻¹) * (t : G) := congrArg Subtype.val h
      rw [this]
      exact Q.mul_mem huQ htQ
    · have : x = (t : G) * ((b : G) * (t : G) * (b : G)⁻¹) * (t : G) :=
        congrArg Subtype.val h
      rw [this]
      exact Q.mul_mem (Q.mul_mem htQ huQ) htQ

end CFSG.Quasithin.ChapterB.SolvableFFFactors
