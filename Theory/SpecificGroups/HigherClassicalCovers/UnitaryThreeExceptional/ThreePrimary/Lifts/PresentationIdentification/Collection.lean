module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.Presentation
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.List.OfFn

/-!
# Collection in the six-root unitary presentation

The descending swaps conjugate every later generator into the subgroup of
later generators. Starting with the last root, each such subgroup is finite;
its one-sided conjugation invariance is therefore normalizer membership.
The resulting successive cyclic extensions collect every word into six
exponents in `Fin 3`. This argument uses only the published cubes and swaps.

Source: the positive SU₄(3) coordinates used for Aschbacher--Smith I.1.4(5),
printed p.408, and GLS3 §6.1. The matrix and projective identifications are
proved in the sibling matrix module and the parent assembly.
-/

@[expose] public noncomputable section
open scoped Pointwise
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts

variable {G : Type*} [Group G]

def ternaryWord {M : Type*} [Monoid M] {n : ℕ} (x : Fin n → M) (v : Fin n → Fin 3) : M :=
  (List.ofFn fun i => x i ^ (v i).val).prod

private theorem cyclic_ternary {x g : G} (hx : x ^ 3 = 1)
    (hg : g ∈ Subgroup.zpowers x) : ∃ a : Fin 3, x ^ a.val = g := by
  have hf : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, hx⟩
  obtain ⟨m, rfl⟩ := hf.mem_powers_iff_mem_zpowers.mpr hg
  refine ⟨⟨m % 3, Nat.mod_lt _ (by decide)⟩, ?_⟩
  change x ^ (m % 3) = x ^ m
  rw [← pow_mod_orderOf x m, ← pow_mod_orderOf x (m % 3),
    Nat.mod_mod_of_dvd _ (orderOf_dvd_of_pow_eq_one hx)]

private theorem ordered_collection {n : ℕ} (x : Fin n → G)
    (hc : ∀ i, x i ^ 3 = 1)
    (hs : ∀ i j, i < j → (x i)⁻¹ * x j * x i ∈
      Subgroup.closure (x '' {k | i < k})) :
    ∀ g ∈ Subgroup.closure (Set.range x), ∃ v, ternaryWord x v = g := by
  induction n with
  | zero =>
    intro g hg
    have h : Set.range x = ∅ := by ext a; simp
    rw [h, Subgroup.closure_empty, Subgroup.mem_bot] at hg
    subst g
    exact ⟨Fin.elim0, rfl⟩
  | succ n ih =>
    let y : Fin n → G := fun i => x i.succ
    have ht (i : Fin n) : x '' {k | i.succ < k} = y '' {k | i < k} := by
      ext g
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine Fin.cases (fun h => by simp at h) (fun k hk => ?_) k hk
        exact ⟨k, Fin.succ_lt_succ_iff.mp hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k.succ, Fin.succ_lt_succ_iff.mpr hk, rfl⟩
    have hy := ih y (fun i => hc i.succ) (fun i j hij => by
      simpa only [ht i] using hs i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij))
    let H := Subgroup.closure (Set.range y)
    have hw (v : Fin n → Fin 3) : ternaryWord y v ∈ H := by
      apply H.list_prod_mem
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact H.pow_mem (Subgroup.subset_closure ⟨i, rfl⟩) _
    let w : (Fin n → Fin 3) → H := fun v => ⟨ternaryWord y v, hw v⟩
    have hws : Function.Surjective w := by
      rintro ⟨g, hg⟩
      obtain ⟨v, hv⟩ := hy g hg
      exact ⟨v, Subtype.ext hv⟩
    let : Finite H := Finite.of_surjective w hws
    have h0 : x '' {k | (0 : Fin (n+1)) < k} = Set.range y := by
      ext g
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine Fin.cases (fun h => by simp at h) (fun k _ => ⟨k, rfl⟩) k hk
      · rintro ⟨k, rfl⟩
        exact ⟨k.succ, Fin.succ_pos _, rfl⟩
    have hn : x 0 ∈ Subgroup.normalizer H := by
      apply ((Subgroup.normalizer (H : Set G)).inv_mem_iff).mp
      apply Subgroup.mem_normalizer_fintype
      have hh : H ≤ H.comap (MulAut.conj ((x 0)⁻¹)).toMonoidHom := by
        apply (Subgroup.closure_le _).mpr
        rintro g ⟨i, rfl⟩
        change (x 0)⁻¹ * x i.succ * ((x 0)⁻¹)⁻¹ ∈ H
        simpa only [inv_inv, h0] using hs 0 i.succ (Fin.succ_pos _)
      intro g hg
      exact hh hg
    have heq : Subgroup.closure (Set.range x) = Subgroup.zpowers (x 0) ⊔ H := by
      apply le_antisymm
      · apply (Subgroup.closure_le _).mpr
        rintro g ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (show Subgroup.zpowers (x 0) ≤ Subgroup.zpowers (x 0) ⊔ H from le_sup_left) (Subgroup.mem_zpowers _)
        · exact (show H ≤ Subgroup.zpowers (x 0) ⊔ H from le_sup_right) (Subgroup.subset_closure ⟨j, rfl⟩)
      · apply sup_le
        · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨0, rfl⟩)
        · apply (Subgroup.closure_le _).mpr
          rintro g ⟨i, rfl⟩
          exact Subgroup.subset_closure ⟨i.succ, rfl⟩
    intro g hg
    rw [heq] at hg
    have hm := Subgroup.coe_mul_of_left_le_normalizer_right
      (Subgroup.zpowers (x 0)) H (Subgroup.zpowers_le.mpr hn)
    change g ∈ (↑(Subgroup.zpowers (x 0) ⊔ H) : Set G) at hg
    rw [hm] at hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    obtain ⟨r, rfl⟩ := cyclic_ternary (hc 0) ha
    obtain ⟨v, rfl⟩ := hy b hb
    refine ⟨Fin.cons r v, ?_⟩
    simp only [ternaryWord, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]
    rfl


theorem map_ternaryWord {M N : Type*} [Monoid M] [Monoid N] {n : ℕ}
    (f : M →* N) (x : Fin n → M) (v : Fin n → Fin 3) :
    f (ternaryWord x v) = ternaryWord (fun i => f (x i)) v := by
  simp only [ternaryWord, MonoidHom.map_list_prod, List.map_ofFn, Function.comp_def, map_pow]

def presentationRoot (i : Fin 6) : Presentation := PresentedGroup.of i

theorem presentationRoot_cube (i : Fin 6) : presentationRoot i ^ 3 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := relators)
    (Or.inl (show FreeGroup.of i ^ 3 ∈ Set.range (fun j : Fin 6 => FreeGroup.of j ^ 3)
      from ⟨i, rfl⟩))
  simpa only [map_pow, presentationRoot, PresentedGroup.of] using h

theorem presentationRoot_swap (i j : Fin 6) (hij : i < j) :
    presentationRoot j * presentationRoot i =
      presentationRoot i * presentationRoot j * swapTail presentationRoot i j := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators)
    (show swapRelator i j ∈ relators from Or.inr ⟨i, j, hij, rfl⟩)
  simp only [map_mul, map_swapTail] at h
  have ht : (fun r : Fin 6 => (PresentedGroup.mk relators) (FreeGroup.of r)) =
      presentationRoot := rfl
  rw [ht] at h
  simpa only [presentationRoot, PresentedGroup.of] using h

private theorem swapTail_mem_later (x : Fin 6 → G) (i j : Fin 6) :
    swapTail x i j ∈ Subgroup.closure (x '' {k | i < k}) := by
  let H := Subgroup.closure (x '' {k | i < k})
  have hr (k : Fin 6) (hk : i < k) : x k ∈ H := Subgroup.subset_closure ⟨k, hk, rfl⟩
  change swapTail x i j ∈ H
  unfold swapTail
  split_ifs with h h h h
  · exact H.mul_mem (H.pow_mem (hr 4 (by rw [h.1]; decide)) _) (hr 5 (by rw [h.1]; decide))
  · exact H.mul_mem (hr 3 (by rw [h.1]; decide)) (hr 5 (by rw [h.1]; decide))
  · exact H.pow_mem (hr 5 (by rw [h.1]; decide)) _
  · exact hr 5 (by rw [h.1]; decide)
  · exact H.one_mem

/-- Any six roots with the published cubic and descending-swap relations collect. -/
theorem normal_form_of_root_relations (x : Fin 6 → G) (hc : ∀ i, x i ^ 3 = 1)
    (hs : ∀ i j, i < j → x j * x i = x i * x j * swapTail x i j)
    (g : G) (hg : g ∈ Subgroup.closure (Set.range x)) :
    ∃ v : Fin 6 → Fin 3, ternaryWord x v = g := by
  refine ordered_collection x hc ?_ g hg
  intro i j hij
  have h : (x i)⁻¹ * x j * x i = x j * swapTail x i j := by
    rw [mul_assoc, hs i j hij]
    simp only [← mul_assoc, inv_mul_cancel, one_mul]
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨j, hij, rfl⟩)
    (swapTail_mem_later x i j)

/-- The fifteen swaps collect every abstract word into six ternary powers. -/
theorem presentation_normal_form (g : Presentation) :
    ∃ v : Fin 6 → Fin 3, ternaryWord presentationRoot v = g := by
  apply normal_form_of_root_relations presentationRoot presentationRoot_cube presentationRoot_swap g
  rw [show presentationRoot = PresentedGroup.of from rfl, PresentedGroup.closure_range_of]
  trivial

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
