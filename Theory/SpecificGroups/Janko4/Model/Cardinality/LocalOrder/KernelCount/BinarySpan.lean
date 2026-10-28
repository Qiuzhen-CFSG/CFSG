module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.Kernel
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.FinCases

/-!
# Binary products of the local kernel conjugates

A family of commuting involutions has a binary-product parametrization of
its generated subgroup. If the parametrization is injective, its cardinality
is 2 to the size of the family. We also specify the eleven successive
conjugates used for the ATLAS local kernel and prove that invariance under
the two local generators identifies their span with the normal closure of
the seed. Finite conjugation-invariant sets are normalized, which avoids any
additional assumptions about orders of the two conjugating elements.

Source for the local words: ATLAS `J4G1-max1W1`, as documented in
`Cardinality.Subgroup`. The group-theoretic arguments here are independent
of any asserted order of J₄ or identification of its local quotient.
-/

@[expose] public section

namespace Janko4.Cardinality.KernelCount
variable {G : Type*} [Monoid G]
def binaryProduct {n : ℕ} (e : Fin n → G) (v : Fin n → Bool) : G :=
  (List.ofFn (fun i => if v i then e i else 1)).prod
lemma binaryProduct_zero {n : ℕ} (e : Fin n → G) :
    binaryProduct e (fun _ => false) = 1 := by simp [binaryProduct]
lemma binaryProduct_succ {n : ℕ} (e : Fin (n+1) → G) (v : Fin (n+1) → Bool) :
    binaryProduct e v = (if v 0 then e 0 else 1) *
      binaryProduct (fun i => e i.succ) (fun i => v i.succ) := by
  simp only [binaryProduct, List.ofFn_succ, List.prod_cons]
lemma commute_binaryProduct {n : ℕ} (e : Fin n → G) (v : Fin n → Bool) (g : G)
    (hc : ∀ i, Commute g (e i)) : Commute g (binaryProduct e v) := by
  apply Commute.list_prod_right
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  split_ifs
  · exact hc i
  · exact Commute.one_right _
lemma binaryProduct_mul {n : ℕ} (e : Fin n → G)
    (hs : ∀ i, e i * e i = 1) (hc : ∀ i j, Commute (e i) (e j))
    (v w : Fin n → Bool) :
    binaryProduct e v * binaryProduct e w = binaryProduct e (fun i => v i ^^ w i) := by
  induction n with
  | zero => simp [binaryProduct]
  | succ n ih =>
    rw [binaryProduct_succ, binaryProduct_succ, binaryProduct_succ]
    have hcomm : Commute (if w 0 then e 0 else 1)
        (binaryProduct (fun i : Fin n => e i.succ) (fun i => v i.succ)) := by
      split_ifs
      · exact commute_binaryProduct _ _ _ (fun i => hc 0 i.succ)
      · exact Commute.one_left _
    rw [mul_assoc, ← mul_assoc (binaryProduct _ _), ← hcomm.eq, mul_assoc,
      ← mul_assoc, ih _ (fun i => hs i.succ) (fun i j => hc i.succ j.succ)]
    cases v 0 <;> cases w 0 <;> simp [hs]
lemma binaryProduct_single {n : ℕ} (e : Fin n → G) (i : Fin n) :
    binaryProduct e (fun j => decide (j = i)) = e i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [binaryProduct_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [binaryProduct_zero]
    · simpa [Ne.symm (Fin.succ_ne_zero j)] using ih (fun j => e j.succ) j
variable {G : Type*} [Group G]
lemma binaryProduct_mem {n : ℕ} (e : Fin n → G) (v : Fin n → Bool)
    (K : Subgroup G) (h : ∀ i, e i ∈ K) : binaryProduct e v ∈ K := by
  apply K.list_prod_mem
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  split_ifs
  · exact h i
  · exact K.one_mem
lemma mem_closure_iff_binaryProduct {n : ℕ} (e : Fin n → G)
    (hs : ∀ i, e i * e i = 1) (hc : ∀ i j, Commute (e i) (e j)) (g : G) :
    g ∈ Subgroup.closure (Set.range e) ↔ ∃ v, binaryProduct e v = g := by
  constructor
  · intro h
    induction h using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨_, binaryProduct_single e i⟩
    | one => exact ⟨_, binaryProduct_zero e⟩
    | mul a b ha hb ia ib =>
      obtain ⟨v, rfl⟩ := ia
      obtain ⟨w, rfl⟩ := ib
      exact ⟨_, (binaryProduct_mul e hs hc v w).symm⟩
    | inv a ha ia =>
      obtain ⟨v, rfl⟩ := ia
      refine ⟨v, ?_⟩
      apply eq_inv_of_mul_eq_one_left
      simpa [binaryProduct_zero] using binaryProduct_mul e hs hc v v
  · rintro ⟨v, rfl⟩
    exact binaryProduct_mem e v _ (fun i => Subgroup.subset_closure (Set.mem_range_self i))
lemma map_binaryProduct {M : Type*} [Monoid M] (f : G →* M)
    {n : ℕ} (e : Fin n → G) (v : Fin n → Bool) :
    f (binaryProduct e v) = binaryProduct (fun i => f (e i)) v := by
  simp only [binaryProduct, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  split_ifs with h <;> simp [h]

lemma card_closure_binaryProduct {n : ℕ} (e : Fin n → G)
    (hs : ∀ i, e i * e i = 1) (hc : ∀ i j, Commute (e i) (e j))
    (hinj : Function.Injective (binaryProduct e)) :
    Nat.card (Subgroup.closure (Set.range e)) = 2 ^ n := by
  let f : (Fin n → Bool) → Subgroup.closure (Set.range e) := fun v =>
    ⟨binaryProduct e v, binaryProduct_mem e v _
      (fun i => Subgroup.subset_closure (Set.mem_range_self i))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      exact hinj (congrArg Subtype.val h)
    · intro g
      obtain ⟨v, hv⟩ := (mem_closure_iff_binaryProduct e hs hc g).mp g.property
      exact ⟨v, Subtype.ext hv⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Nat.card_eq_fintype_card]

/-- The successive conjugates used in the concrete binary kernel certificate. -/
def conjugates (x y u : G) : Fin 11 → G :=
  let e0 := u
  let e1 := x⁻¹ * e0 * x
  let e2 := y⁻¹ * e0 * y
  let e3 := x⁻¹ * e2 * x
  let e4 := y⁻¹ * e3 * y
  let e5 := y⁻¹ * e4 * y
  let e6 := x⁻¹ * e5 * x
  let e7 := y⁻¹ * e6 * y
  let e8 := y⁻¹ * e7 * y
  let e9 := x⁻¹ * e8 * x
  let e10 := y⁻¹ * e9 * y
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]

lemma conjugates_mem (x y u : G) (K : Subgroup G) [hK : K.Normal]
    (hu : u ∈ K) (i : Fin 11) : conjugates x y u i ∈ K := by
  have step (g a : G) (ha : a ∈ K) := hK.conj_mem' a ha g
  fin_cases i <;> dsimp [conjugates]
  all_goals repeat first | exact hu | apply step

lemma closure_conjugates_eq_normalClosure [Finite G] (x y u : G)
    (hgen : Subgroup.closure {x, y} = ⊤)
    (hx : ∀ i, x⁻¹ * conjugates x y u i * x ∈
      Subgroup.closure (Set.range (conjugates x y u)))
    (hy : ∀ i, y⁻¹ * conjugates x y u i * y ∈
      Subgroup.closure (Set.range (conjugates x y u))) :
    Subgroup.closure (Set.range (conjugates x y u)) = Subgroup.normalClosure {u} := by
  let K := Subgroup.closure (Set.range (conjugates x y u))
  have normalizes (g : G)
      (hg : ∀ i, g⁻¹ * conjugates x y u i * g ∈ K) :
      g ∈ Subgroup.normalizer (K : Set G) := by
    have hm : K ≤ K.comap (MulAut.conj g⁻¹).toMonoidHom := by
      apply (Subgroup.closure_le _).mpr
      rintro a ⟨i, rfl⟩
      simpa using hg i
    have hi : g⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mem_normalizer_fintype (fun a ha => hm ha)
    simpa using (Subgroup.normalizer (K : Set G)).inv_mem hi
  have htop : Subgroup.normalizer (K : Set G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact normalizes _ hx
    · rw [Set.mem_singleton_iff] at hg
      subst g
      exact normalizes y hy
  let : K.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro a ⟨i, rfl⟩
    exact conjugates_mem x y u _ (Subgroup.subset_normalClosure (Set.mem_singleton _)) i
  · apply Subgroup.normalClosure_le_normal (N := K)
    rw [Set.singleton_subset_iff]
    exact Subgroup.subset_closure ⟨0, rfl⟩
end Janko4.Cardinality.KernelCount
