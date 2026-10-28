module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Coordinates
public import Theory.ElementaryAbelian.Basic

/-!
# The five binary coordinates in the A₈ argument

A subset of five independent involutions specifies its product. We encode
these products in C₂⁵ before mapping into the ambient group. The marked
embedding keeps the fifth generator equal to z and the other four in rᴸ;
its existence from the permutation model is a separate obligation.

Source: Aschbacher–Smith, proof of 16.4.9(2), printed p.1192.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.AlternatingEight
open Subgroup

abbrev Space := Multiplicative (Fin 5 → ZMod 2)

/-- The product of the coordinates indexed by s. -/
def word (s : Finset (Fin 5)) : Space :=
  Multiplicative.ofAdd (fun i => if i ∈ s then 1 else 0)

@[simp] theorem word_empty : word ∅ = 1 := by
  rfl

/-- Inserting a new coordinate multiplies by its generator. -/
theorem word_insert {s : Finset (Fin 5)} {i : Fin 5} (hi : i ∉ s) :
    word (insert i s) = word {i} * word s := by
  ext j
  change (if j ∈ insert i s then (1 : ZMod 2) else 0) =
    (if j ∈ ({i} : Finset (Fin 5)) then 1 else 0) + (if j ∈ s then 1 else 0)
  by_cases hji : j = i
  · subst j
    simp [hi]
  · simp [hji]

/-- Subset products in the five coordinates are independent. -/
theorem word_injective : Function.Injective word := by
  intro s t he
  ext i
  have hi := congrArg (fun v : Space => v.toAdd i) he
  change (if i ∈ s then (1 : ZMod 2) else 0) = (if i ∈ t then 1 else 0) at hi
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

/-- Every vector is a subset product, including the empty product. -/
theorem word_surjective : Function.Surjective word := by
  intro v
  refine ⟨Finset.univ.filter (fun i => v.toAdd i = 1), ?_⟩
  ext i
  change (if i ∈ Finset.univ.filter (fun j => v.toAdd j = 1) then (1 : ZMod 2) else 0) = v.toAdd i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (show ∀ c : ZMod 2, (if c = 1 then (1 : ZMod 2) else 0) = c by decide +kernel) _

/-- Each coordinate word has square one. -/
theorem word_sq (s : Finset (Fin 5)) : word s ^ 2 = 1 := by
  rw [pow_two]
  ext i
  change (if i ∈ s then (1 : ZMod 2) else 0) + (if i ∈ s then 1 else 0) = 0
  split_ifs <;> decide

/-- The ordinary finite product agrees with the binary-coordinate word. -/
theorem word_eq_prod (s : Finset (Fin 5)) : word s = ∏ i ∈ s, word {i} := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [word_insert hi, Finset.prod_insert hi, ih]

variable {G : Type*} [Group G]

/-- A faithful five-coordinate subgroup with the actual source markings.
This record assumes no fusion exclusions or conjugate-component placements. -/
structure MarkedEmbedding (L : Subgroup G) (z r : G) where
  hom : Space →* G
  injective : Function.Injective hom
  central : hom (word {4}) = z
  conjugates : ∀ i : Fin 5, i ≠ 4 → ∃ l ∈ L, MulAut.conj l r = hom (word {i})

namespace MarkedEmbedding
variable {L : Subgroup G} {z r : G}

/-- The source subgroup A. -/
abbrev subgroup (F : MarkedEmbedding L z r) : Subgroup G := F.hom.range

/-- The five marked generators. -/
def mark (F : MarkedEmbedding L z r) (i : Fin 5) : G := F.hom (word {i})

/-- Independence is retained in the ambient group. -/
theorem products_injective (F : MarkedEmbedding L z r) :
    Function.Injective (fun s => F.hom (word s)) := F.injective.comp word_injective

/-- Every element of A has a unique subset of marked coordinates. -/
theorem mem_subgroup_iff (F : MarkedEmbedding L z r) (a : G) :
    a ∈ F.subgroup ↔ ∃ s : Finset (Fin 5), F.hom (word s) = a := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨s, rfl⟩ := word_surjective v
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨word s, rfl⟩

/-- The marked elements are distinct. -/
theorem mark_injective (F : MarkedEmbedding L z r) : Function.Injective F.mark := by
  intro i j he
  exact Finset.singleton_injective (F.products_injective he)

/-- Every element of A squares to one. -/
theorem square_eq_one (F : MarkedEmbedding L z r) {a : G} (ha : a ∈ F.subgroup) :
    a ^ 2 = 1 := by
  obtain ⟨s, rfl⟩ := (F.mem_subgroup_iff a).mp ha
  rw [← map_pow, word_sq, map_one]

/-- The five marked generators generate the actual subgroup A. -/
theorem closure_marks (F : MarkedEmbedding L z r) :
    closure (Set.range F.mark) = F.subgroup := by
  apply le_antisymm
  · apply (closure_le F.subgroup).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨word {i}, rfl⟩
  · intro a ha
    obtain ⟨s, rfl⟩ := (F.mem_subgroup_iff a).mp ha
    clear ha
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [word_insert hi, map_mul]
      exact mul_mem (subset_closure ⟨i, rfl⟩) ih

/-- The source elementary subgroup has order 32. -/
theorem card_subgroup (F : MarkedEmbedding L z r) : Nat.card F.subgroup = 32 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective F.injective).toEquiv]
  change Nat.card (Fin 5 → ZMod 2) = 32
  rw [Nat.card_fun]
  norm_num

/-- The marked set has five elements. -/
theorem card_marks (F : MarkedEmbedding L z r) : Nat.card (Set.range F.mark) = 5 := by
  rw [← Nat.card_congr (Equiv.ofInjective F.mark F.mark_injective)]
  simp

/-- The range is an actual elementary abelian subgroup. -/
theorem elementary (F : MarkedEmbedding L z r) : IsElementaryAbelian 2 F.subgroup := by
  refine {
    toIsMulCommutative := isMulCommutative_iff.mpr ?_
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · rintro ⟨a, v, rfl⟩ ⟨b, w, rfl⟩
    apply Subtype.ext
    exact (map_mul F.hom v w).symm.trans ((congrArg F.hom (mul_comm v w)).trans (map_mul F.hom w v))
  · intro a
    exact Subtype.ext (F.square_eq_one a.property)

/-- Once r is fused to z, all five marked generators are fused to z. -/
theorem mark_isConj (F : MarkedEmbedding L z r) (hr : IsConj z r) (i : Fin 5) :
    IsConj z (F.mark i) := by
  by_cases hi : i = 4
  · subst i
    simpa only [mark, F.central] using IsConj.refl z
  · obtain ⟨l, _, hl⟩ := F.conjugates i hi
    exact hr.trans (isConj_iff.mpr ⟨l, hl⟩)

end MarkedEmbedding
end CFSG.Quasithin.Chapter16.Intersections.AlternatingEight
