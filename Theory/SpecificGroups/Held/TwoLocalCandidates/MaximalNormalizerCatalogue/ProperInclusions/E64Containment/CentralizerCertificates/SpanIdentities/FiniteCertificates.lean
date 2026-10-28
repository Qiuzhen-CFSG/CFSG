module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.Intrinsic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.List.FinRange

/-!
# Centralizer counts from a certified finite word enumeration

A finite injective family containing one and closed under right multiplication
by every generator exhausts the generated group: each transition is injective,
hence surjective, so inverse transitions exist too. Folding the transitions
then computes every product. Counting commuting indices computes the cardinality
of the actual singleton centralizer, and Lagrange converts that count to index.

The final theorem identifies the intrinsic span using word witnesses for both
containments. The Held applications retain the original degree-2058 embedding.
This supports the E64 rows in GLS3 Table 5.3p and quasithin condition E; it does
not assume or identify an ambient centralizer or a two-core.
-/

@[expose] public section

open Subgroup
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates
variable {G : Type*} [Group G] {ι : Type*} {n : ℕ}
def eval (g : ι → G) (w : List ι) : G := (w.map g).prod
/-- Evaluate a word after applying a homomorphism, using a named table of images. -/
lemma eval_map {H : Type*} [Group H] (f : G →* H) (g : ι → G) (p : ι → H)
    (hp : ∀ a, p a = f (g a)) (w : List ι) : eval p w = f (eval g w) := by
  simp only [eval, map_list_prod, List.map_map, Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro a _
  exact hp a

structure Enumeration (g : ι → G) (n : ℕ) where
  code : Fin n → List ι
  root : Fin n
  step : Fin n → ι → Fin n
  root_eq : eval g (code root) = 1
  step_eq : ∀ i a, eval g (code (step i a)) = eval g (code i) * g a
  injective : Function.Injective (fun i => eval g (code i))
namespace Enumeration
variable {g : ι → G} (d : Enumeration g n)
def element (i : Fin n) : G := eval g (d.code i)
def mulIdx (i k : Fin n) : Fin n := (d.code k).foldl d.step i
lemma eval_fold (w : List ι) (i : Fin n) :
    d.element (w.foldl d.step i) = d.element i * eval g w := by
  induction w generalizing i with
  | nil => simp [eval]
  | cons a w ih =>
    rw [List.foldl_cons, ih]
    change eval g (d.code (d.step i a)) * eval g w = _
    rw [d.step_eq]
    simp [eval, element, mul_assoc]
lemma mul_eq (i k : Fin n) : d.element (d.mulIdx i k) = d.element i * d.element k :=
  d.eval_fold _ _
lemma cover {x : G} (hx : x ∈ closure (Set.range g)) : ∃ i, d.element i = x := by
  apply closure_induction_right (p := fun x _ => ∃ i, d.element i = x) ?_ ?_ ?_ hx
  · exact ⟨d.root, d.root_eq⟩
  · rintro x _ _ ⟨a, rfl⟩ ⟨i, rfl⟩
    exact ⟨d.step i a, d.step_eq i a⟩
  · rintro x _ _ ⟨a, rfl⟩ ⟨i, rfl⟩
    have hinj : Function.Injective (fun k => d.step k a) := by
      intro k l h
      apply d.injective
      have he := congrArg d.element h
      change eval g (d.code (d.step k a)) = eval g (d.code (d.step l a)) at he
      rw [d.step_eq, d.step_eq] at he
      exact mul_right_cancel he
    obtain ⟨k, hk⟩ := (Finite.surjective_of_injective hinj) i
    refine ⟨k, ?_⟩
    have he : d.element i = d.element k * g a := hk ▸ d.step_eq k a
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
lemma element_mem (i : Fin n) : d.element i ∈ closure (Set.range g) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact subset_closure ⟨a, rfl⟩
noncomputable def equiv : Fin n ≃ closure (Set.range g) :=
  Equiv.ofBijective (fun i => ⟨d.element i, d.element_mem i⟩)
    ⟨fun _ _ h => d.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨i, hi⟩ := d.cover x.property
      exact ⟨i, Subtype.ext hi⟩⟩
include d in
lemma card : Nat.card (closure (Set.range g)) = n := by
  rw [← Nat.card_congr d.equiv]
  simp

def count (i : Fin n) : ℕ :=
  (List.finRange n).countP (fun k => decide (d.mulIdx i k = d.mulIdx k i))
lemma centralizer_card (i : Fin n) :
    Nat.card (centralizer ({d.equiv i} : Set (closure (Set.range g)))) = d.count i := by
  let f : {k : Fin n // d.mulIdx i k = d.mulIdx k i} ≃
      centralizer ({d.equiv i} : Set (closure (Set.range g))) :=
    Equiv.subtypeEquiv d.equiv (fun k => by
      rw [mem_centralizer_singleton_iff]
      change _ ↔ (⟨d.element k, _⟩ : closure (Set.range g)) * ⟨d.element i, _⟩ =
        ⟨d.element i, _⟩ * ⟨d.element k, _⟩
      rw [Subtype.ext_iff]
      change _ ↔ d.element k * d.element i = d.element i * d.element k
      rw [← d.mul_eq, ← d.mul_eq]
      exact d.injective.eq_iff.symm.trans eq_comm)
  rw [← Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← List.toFinset_finRange n, (List.nodup_finRange n).card_eq_countP]
  rfl
lemma selected_iff (i : Fin n) :
    (centralizer ({d.equiv i} : Set (closure (Set.range g)))).index ≤ 2 ↔
      n ≤ 2 * d.count i := by
  let : Finite (closure (Set.range g)) := Finite.of_equiv (Fin n) d.equiv
  have hp : 0 < Nat.card (centralizer ({d.equiv i} : Set (closure (Set.range g)))) :=
    Nat.card_pos
  have h := (centralizer ({d.equiv i} : Set (closure (Set.range g)))).index_mul_card
  rw [d.card, d.centralizer_card] at h
  rw [d.centralizer_card] at hp
  constructor
  · intro hi
    calc n = _ := h.symm
         _ ≤ _ := Nat.mul_le_mul_right _ hi
  · intro hi
    exact Nat.le_of_mul_le_mul_right (by omega :
      (centralizer ({d.equiv i} : Set (closure (Set.range g)))).index * d.count i ≤
        2 * d.count i) hp

open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
lemma span_eq {κ : Type*} (t : κ → G)
    (upper : ∀ i, n ≤ 2 * d.count i → d.element i ∈ closure (Set.range t))
    (lower : ∀ a, ∃ w : List (Fin n),
      (∀ i ∈ w, n ≤ 2 * d.count i) ∧ eval d.element w = t a) :
    indexTwoSpan (closure (Set.range g)) =
      (closure (Set.range t)).subgroupOf (closure (Set.range g)) := by
  let Q := closure (Set.range g)
  let E := closure (Set.range t)
  let S := (indexTwoSpan Q).map Q.subtype
  have hlower : E ≤ S := by
    apply (closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    obtain ⟨w, hw, he⟩ := lower a
    rw [← he]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact mem_map.mpr ⟨d.equiv i, subset_closure ((d.selected_iff i).mpr (hw i hi)), rfl⟩
  have hupper : S ≤ E := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    intro x hx
    obtain ⟨i, rfl⟩ := d.equiv.surjective x
    exact upper i ((d.selected_iff i).mp hx)
  have hEQ : E ≤ Q := hlower.trans (map_subtype_le _)
  apply Subgroup.map_injective Q.subtype_injective
  exact (le_antisymm hupper hlower).trans (map_subgroupOf_eq_of_le hEQ).symm
end Enumeration
end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates
