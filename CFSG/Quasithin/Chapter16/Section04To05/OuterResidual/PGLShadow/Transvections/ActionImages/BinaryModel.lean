module

public import Theory.GroupTheory.ElementaryEightFixedPointOrder24
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Binary coordinates for the marked transvection images

The three automorphisms are the actual linear maps specified by the markings
in Aschbacher–Smith, Lemma 16.4.6, printed pp.1185–1186. Six explicit words
exhaust the first generated subgroup; its faithful restriction to the three
nonidentity plane points identifies it with S₃. Adding the third transvection
gives twenty-four words and a transitive action outside the fixed line.
All finite calculations are checked by the kernel. These computations use no
weak-closure assumptions; the ambient transport is in the parent module.
-/

public section

set_option synthInstance.maxSize 4096

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections.ActionModel
abbrev C := Multiplicative (ZMod 2)
abbrev E := C × C × C
private instance : DecidableEq (MulAut E) := fun f g =>
  decidable_of_iff (∀ x : E, f x = g x) MulEquiv.ext_iff.symm
@[expose]
def r : E := (.ofAdd 1, 1, 1)
@[expose]
def z : E := (1, .ofAdd 1, 1)
@[expose]
def v : E := (1, 1, .ofAdd 1)
@[expose]
def u : E := r * (z * v)
@[expose]
def w : E := v * z

@[expose]
def s : MulAut E where
  toFun x := (x.1 * x.2.1 * x.2.2, x.2.2, x.2.1)
  invFun x := (x.1 * x.2.1 * x.2.2, x.2.2, x.2.1)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose]
def t : MulAut E where
  toFun x := (x.1, x.2.1, x.1 * x.2.2)
  invFun x := (x.1, x.2.1, x.1 * x.2.2)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose]
def a : MulAut E where
  toFun x := (x.1, x.1 * x.2.1, x.2.2)
  invFun x := (x.1, x.1 * x.2.1, x.2.2)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

abbrev H3 := zpowers s ⊔ zpowers t
abbrev H4 := H3 ⊔ zpowers a

private def words3 : Fin 6 → MulAut E := ![1, s, t, s*t, t*s, s*t*s]

private theorem words3_mem (i : Fin 6) : words3 i ∈ H3 := by
  have hs : s ∈ H3 := mem_sup_left (mem_zpowers s)
  have ht : t ∈ H3 := mem_sup_right (mem_zpowers t)
  fin_cases i <;> dsimp [words3] <;> solve_by_elim [Subgroup.one_mem, Subgroup.mul_mem]

private def enumGroup {n : ℕ} (f : Fin n → MulAut E)
    (h1 : ∃ i, f i = 1)
    (hm : ∀ i j, ∃ k, f i * f j = f k)
    (hi : ∀ i, ∃ j, (f i)⁻¹ = f j) : Subgroup (MulAut E) where
  carrier := Set.range f
  one_mem' := h1
  mul_mem' := by rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩; obtain ⟨k,hk⟩ := hm i j; exact ⟨k,hk.symm⟩
  inv_mem' := by rintro _ ⟨i,rfl⟩; obtain ⟨j,hj⟩ := hi i; exact ⟨j,hj.symm⟩

private theorem enum3 : (H3 : Set (MulAut E)) = Set.range words3 := by
  let B := enumGroup words3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h : H3 = B := le_antisymm
    (sup_le (zpowers_le.mpr ⟨1, rfl⟩) (zpowers_le.mpr ⟨2, rfl⟩))
    (by rintro x ⟨i,rfl⟩; exact words3_mem i)
  exact congrArg (fun K : Subgroup (MulAut E) => (K : Set (MulAut E))) h

private theorem words3_injective : Function.Injective words3 := by decide +kernel

theorem card3 : Nat.card H3 = 6 := by
  let f : Fin 6 → H3 := fun i => ⟨words3 i, words3_mem i⟩
  have hf : Function.Bijective f := ⟨fun i j h => words3_injective (congrArg Subtype.val h), by
    intro x
    obtain ⟨i,hi⟩ := show x.val ∈ Set.range words3 from enum3 ▸ x.property
    exact ⟨i, Subtype.ext hi⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (Nat.card_fin 6)

@[expose]
def plane : Subgroup E where
  carrier := {x | x = 1 ∨ x = u ∨ x = v ∨ x = u*v}
  one_mem' := Or.inl rfl
  mul_mem' := by
    change ∀ a b : E, _
    simp only [Set.mem_ofPred_eq]
    decide +kernel
  inv_mem' := by decide +kernel

@[expose]
def line : Subgroup E where
  carrier := {x | x = 1 ∨ x = w}
  one_mem' := Or.inl rfl
  mul_mem' := by
    change ∀ a b : E, _
    simp only [Set.mem_ofPred_eq]
    decide +kernel
  inv_mem' := by decide +kernel

private instance : DecidablePred (· ∈ plane) := fun x =>
  inferInstanceAs (Decidable (x = 1 ∨ x = u ∨ x = v ∨ x = u*v))
private instance : DecidablePred (· ∈ line) := fun x =>
  inferInstanceAs (Decidable (x = 1 ∨ x = w))

theorem plane_eq : plane = zpowers u ⊔ zpowers v := by
  apply le_antisymm
  · rintro x (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem_sup (mem_zpowers _) (mem_zpowers _)
  · exact sup_le (zpowers_le.mpr (by decide +kernel)) (zpowers_le.mpr (by decide +kernel))

theorem line_eq : line = zpowers w := by
  apply le_antisymm
  · rintro x (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _
  · exact zpowers_le.mpr (Or.inr rfl)

theorem plane_card : Nat.card plane = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem line_card : Nat.card line = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem preserves_plane : ∀ b : H3, ∀ x : E, (b.val x ∈ plane ↔ x ∈ plane) := by
  intro b
  obtain ⟨i,hi⟩ := show b.val ∈ Set.range words3 from enum3 ▸ b.property
  rw [← hi]
  exact (by decide +kernel : ∀ i : Fin 6, ∀ x : E, words3 i x ∈ plane ↔ x ∈ plane) i

theorem fixes_line : ∀ b : H3, b.val w = w := by
  intro b
  obtain ⟨i,hi⟩ := show b.val ∈ Set.range words3 from enum3 ▸ b.property
  rw [← hi]
  exact (by decide +kernel : ∀ i : Fin 6, words3 i w = w) i

private abbrev X := {x : E // x ∈ plane ∧ x ≠ 1}
private def rep : H3 →* Equiv.Perm X where
  toFun b := Equiv.Perm.subtypePerm b.val.toEquiv (fun x =>
    and_congr (preserves_plane b x) (not_congr (map_eq_one_iff b.val b.val.injective)))
  map_one' := by apply Equiv.ext; intro x; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Equiv.ext; intro x; apply Subtype.ext; rfl

private theorem rep_injective : Function.Injective rep := by
  intro b c h
  obtain ⟨i,hi⟩ := show b.val ∈ Set.range words3 from enum3 ▸ b.property
  obtain ⟨j,hj⟩ := show c.val ∈ Set.range words3 from enum3 ▸ c.property
  have he : ∀ x : X, words3 i x.val = words3 j x.val := by
    intro x
    exact hi ▸ hj ▸ congrArg Subtype.val (Equiv.congr_fun h x)
  have hh : ∀ i j : Fin 6, (∀ x : X, words3 i x.val = words3 j x.val) → words3 i = words3 j := by
    decide +kernel
  exact Subtype.ext (hi.symm.trans ((hh i j he).trans hj))

noncomputable def equiv3 : H3 ≃* Equiv.Perm (Fin 3) := by
  have hc : Nat.card X = 3 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  classical
  have hp : Nat.card (Equiv.Perm X) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hc]; rfl
  exact (MulEquiv.ofBijective rep
    ((Nat.bijective_iff_injective_and_card rep).mpr ⟨rep_injective, card3.trans hp.symm⟩)).trans
    (Equiv.permCongrHom (Finite.equivFinOfCardEq hc))


private def words4 : Fin 24 → MulAut E := ![1, s, t, a, s*t, s*a, t*s, t*a, a*s, s*t*s, s*t*a, s*a*s, t*s*a, t*a*s, a*s*t, s*t*s*a, s*t*a*s, s*a*s*t, t*s*a*s, t*a*s*t, s*t*s*a*s, s*t*a*s*t, t*s*a*s*t, s*t*s*a*s*t]

private theorem words4_mem (i : Fin 24) : words4 i ∈ H4 := by
  have hs : s ∈ H4 := mem_sup_left (mem_sup_left (mem_zpowers s))
  have ht : t ∈ H4 := mem_sup_left (mem_sup_right (mem_zpowers t))
  have ha : a ∈ H4 := mem_sup_right (mem_zpowers a)
  fin_cases i <;> dsimp [words4] <;> solve_by_elim (maxDepth := 12) [Subgroup.one_mem, Subgroup.mul_mem]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem enum4 : (H4 : Set (MulAut E)) = Set.range words4 := by
  let B := enumGroup words4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h : H4 = B := le_antisymm
    (sup_le (sup_le (zpowers_le.mpr ⟨1, rfl⟩) (zpowers_le.mpr ⟨2, rfl⟩))
      (zpowers_le.mpr ⟨3, rfl⟩))
    (by rintro x ⟨i,rfl⟩; exact words4_mem i)
  exact congrArg (fun K : Subgroup (MulAut E) => (K : Set (MulAut E))) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem words4_injective : Function.Injective words4 := by decide +kernel

theorem card4 : Nat.card H4 = 24 := by
  let f : Fin 24 → H4 := fun i => ⟨words4 i, words4_mem i⟩
  have hf : Function.Bijective f := ⟨fun i j h => words4_injective (congrArg Subtype.val h), by
    intro x
    obtain ⟨i,hi⟩ := show x.val ∈ Set.range words4 from enum4 ▸ x.property
    exact ⟨i, Subtype.ext hi⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (Nat.card_fin 24)

theorem fixes4 : ∀ b : H4, b.val w = w := by
  intro b
  obtain ⟨i,hi⟩ := show b.val ∈ Set.range words4 from enum4 ▸ b.property
  rw [← hi]
  exact (by decide +kernel : ∀ i : Fin 24, words4 i w = w) i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transitive4 (x y : E) (hx : x ∉ line) (hy : y ∉ line) :
    ∃ b : H4, b.val x = y := by
  have h : ∀ x y : E, x ∉ line → y ∉ line → ∃ i : Fin 24, words4 i x = y := by
    change ∀ x y : E, ¬ (x = 1 ∨ x = w) → ¬ (y = 1 ∨ y = w) → ∃ i : Fin 24, words4 i x = y
    decide +kernel
  obtain ⟨i,hi⟩ := h x y hx hy
  exact ⟨⟨words4 i, words4_mem i⟩, hi⟩

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections.ActionModel
