module

public import Theory.SpecificGroups.G2Even.TwoRank.Elementary
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.LinearCombination

/-!
# Elementary subgroup bounds in the even G₂ Sylow subgroup

The six-root multiplication law bounds each elementary subgroup by q³.
If the sixth coordinate is nonzero somewhere, commutation with such an
involution makes coordinates one, two, and six determine every element.
Otherwise the middle four coordinates span a totally isotropic subspace
of a nondegenerate alternating four-space. Its dimension is at most two;
the highest-root coordinate contributes the remaining factor q.

Source: Aschbacher–Smith, the G₂ rank on printed p.356 and the inspection
in 16.3.9, printed p.1180. Root identities are from the licensed ATLAS
port in Theory.AtlasPort.LinearGroups.G2.Unipotent.
-/

public section

open scoped IsMulCommutative

namespace Atlas.G2.EvenTwoRank
variable (F : Type*) [Field F]

private def fourForm : LinearMap.BilinForm F (Fin 4 → F) :=
  LinearMap.mk₂ F (fun x y => x 0 * y 3 + x 3 * y 0 + x 1 * y 2 + x 2 * y 1)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)

private theorem fourForm_ker : (fourForm F).ker = ⊥ := by
  apply LinearMap.separatingLeft_iff_ker_eq_bot.mp
  intro x hx
  have h0 := hx ![0,0,0,1]
  have h1 := hx ![0,0,1,0]
  have h2 := hx ![0,1,0,0]
  have h3 := hx ![1,0,0,0]
  simp [fourForm, LinearMap.mk₂_apply] at h0 h1 h2 h3
  ext i
  fin_cases i <;> assumption

private theorem span_card_le [Finite F] (S : Set (Fin 4 → F))
    (hS : ∀ x ∈ S, ∀ y ∈ S,
      x 0 * y 3 + x 3 * y 0 + x 1 * y 2 + x 2 * y 1 = 0) :
    Nat.card (Submodule.span F S) ≤ Nat.card F ^ 2 := by
  classical
  let W := Submodule.span F S
  have hW : ∀ x ∈ W, ∀ y ∈ W, fourForm F x y = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hS x hx y hy
      | zero => exact map_zero _
      | add y z _ _ hy hz => rw [map_add, hy, hz, zero_add]
      | smul a y _ hy => rw [map_smul, hy, smul_zero]
    | zero => intro y _; simp
    | add x y _ _ hx hy => intro z hz; simp [hx z hz, hy z hz]
    | smul a x _ hx => intro y hy; simp [hx y hy]
  have hle : W ≤ (fourForm F).orthogonal W := by
    intro y hy x hx
    exact hW x hx y hy
  have hd := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := fourForm F) W
  have hm := Submodule.finrank_mono hle
  rw [fourForm_ker F] at hd
  have hz : W ⊓ (⊥ : Submodule F (Fin 4 → F)) = ⊥ := inf_bot_eq _
  rw [hz, finrank_bot, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, add_zero] at hd
  have hb : Module.finrank F W ≤ 2 := by omega
  change Nat.card W ≤ _
  rw [Module.natCard_eq_pow_finrank (K := F) (V := W)]
  exact pow_le_pow_right' Nat.card_pos hb

end Atlas.G2.EvenTwoRank

namespace Atlas.G2.EvenTwoRank
variable {F : Type*} [Field F] [CharP F 2]

private theorem three : (3 : F) = 1 := by
  linear_combination (CharTwo.two_eq_zero : (2 : F) = 0)

private theorem six : (6 : F) = 0 := by
  linear_combination 3 * (CharTwo.two_eq_zero : (2 : F) = 0)

private theorem square_coordinates (t : Fin 6 → F)
    (ht : unipotentProduct t ^ 2 = 1) :
    t 4 * t 5 = 0 ∧ t 2 * t 5 + t 3 * t 5 ^ 2 + t 4 * t 5 ^ 3 = 0 := by
  rw [pow_two, unipotentProduct_mul, ← unipotentProduct_zero] at ht
  have he := unipotentProduct_injective ht
  have h3 := congrFun he 3
  have h1 := congrFun he 1
  change t 3 - t 4 * t 5 + t 3 = 0 at h3
  change t 1 - 3 * t 2 * t 5 + 3 * t 3 * t 5 ^ 2 - t 4 * t 5 ^ 3 + t 1 = 0 at h1
  rw [three] at h1
  constructor
  · linear_combination -h3 + t 3 * (CharTwo.two_eq_zero : (2 : F) = 0)
  · linear_combination -h1 + t 1 * (CharTwo.two_eq_zero : (2 : F) = 0) +
      t 3 * t 5 ^ 2 * (CharTwo.two_eq_zero : (2 : F) = 0)

omit [CharP F 2] in
private theorem commute_fourth (t u : Fin 6 → F)
    (h : Commute (unipotentProduct t) (unipotentProduct u)) :
    u 4 * t 5 = t 4 * u 5 := by
  have he := h.eq
  rw [unipotentProduct_mul, unipotentProduct_mul] at he
  have hc := congrFun (unipotentProduct_injective he) 3
  change u 3 - u 4 * t 5 + t 3 = t 3 - t 4 * u 5 + u 3 at hc
  linear_combination -hc

private theorem commute_second (t u : Fin 6 → F)
    (ht : t 4 = 0) (hu : u 4 = 0)
    (h : Commute (unipotentProduct t) (unipotentProduct u)) :
    u 2 * t 5 + u 3 * t 5 ^ 2 = t 2 * u 5 + t 3 * u 5 ^ 2 := by
  have he := h.eq
  rw [unipotentProduct_mul, unipotentProduct_mul] at he
  have hc := congrFun (unipotentProduct_injective he) 1
  simp only [unipotentProductParameters, Matrix.cons_val_one, Matrix.cons_val_zero,
    ht, hu, three, one_mul, zero_mul, sub_zero] at hc
  simp only [CharTwo.sub_eq_add] at hc
  linear_combination hc

private theorem commute_first (t u : Fin 6 → F)
    (ht : t 4 = 0) (hu : u 4 = 0)
    (h : Commute (unipotentProduct t) (unipotentProduct u)) :
    u 2 * t 3 + u 3 ^ 2 * t 5 = t 2 * u 3 + t 3 ^ 2 * u 5 := by
  have he := h.eq
  rw [unipotentProduct_mul, unipotentProduct_mul] at he
  have hc := congrFun (unipotentProduct_injective he) 0
  simp [unipotentProductParameters, ht, hu, three, six,
    CharTwo.sub_eq_add] at hc
  linear_combination hc

private theorem commute_radical (t u : Fin 6 → F)
    (ht : t 5 = 0) (hu : u 5 = 0)
    (h : Commute (unipotentProduct t) (unipotentProduct u)) :
    t 1 * u 4 + t 4 * u 1 + t 2 * u 3 + t 3 * u 2 = 0 := by
  have he := h.eq
  rw [unipotentProduct_mul, unipotentProduct_mul] at he
  have hc := congrFun (unipotentProduct_injective he) 0
  simp [unipotentProductParameters, ht, hu, three, CharTwo.sub_eq_add] at hc
  linear_combination hc +
    (t 1 * u 4 + t 2 * u 3) * (CharTwo.two_eq_zero : (2 : F) = 0)

private theorem coordinates_recover (v t u : Fin 6 → F)
    (hv : v 5 ≠ 0) (hsq : unipotentProduct v ^ 2 = 1)
    (hvt : Commute (unipotentProduct v) (unipotentProduct t))
    (hvu : Commute (unipotentProduct v) (unipotentProduct u))
    (h0 : t 0 = u 0) (h1 : t 1 = u 1) (h5 : t 5 = u 5) : t = u := by
  obtain ⟨hev, hcv⟩ := square_coordinates v hsq
  have hv4 : v 4 = 0 := (mul_eq_zero.mp hev).resolve_right hv
  have ht4 : t 4 = 0 := by
    have h := commute_fourth v t hvt
    rw [hv4, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hv
  have hu4 : u 4 = 0 := by
    have h := commute_fourth v u hvu
    rw [hv4, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hv
  rw [hv4, zero_mul, add_zero] at hcv
  have hv2 : v 2 = v 3 * v 5 := by
    apply (mul_right_inj' hv).mp
    linear_combination hcv - v 3 * v 5 ^ 2 *
      (CharTwo.two_eq_zero : (2 : F) = 0)
  have hbt := commute_second v t hv4 ht4 hvt
  have hbu := commute_second v u hv4 hu4 hvu
  have hat := commute_first v t hv4 ht4 hvt
  have hau := commute_first v u hv4 hu4 hvu
  rw [h5] at hbt hat
  rw [hv2] at hbt hbu hat hau
  have hd : (t 3 ^ 2 - u 3 ^ 2) * v 5 ^ 2 = 0 := by
    linear_combination v 5 * (hat - hau) - v 3 * (hbt - hbu) +
      (t 3 - u 3) * v 3 * v 5 ^ 2 * (CharTwo.two_eq_zero : (2 : F) = 0)
  have h3 : t 3 = u 3 := CharTwo.sq_injective
    (sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right (pow_ne_zero _ hv)))
  have h2 : t 2 = u 2 := by
    apply (mul_right_inj' hv).mp
    rw [h3] at hbt
    linear_combination hbt - hbu
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact ht4.trans hu4.symm
  · exact h5


omit [CharP F 2] in
private theorem reconstruct (g : unipotent (K := F)) :
    unipotentProduct (unipotentParameters g.val) = g.val := by
  have hg : g.val ∈ unipotentRange := by
    simpa only [← unipotent_eq_range] using g.property
  obtain ⟨t, ht⟩ := hg
  rw [← ht, unipotentParameters_product]

/-- Every elementary abelian subgroup of the actual six-root Sylow
subgroup has order at most q³. -/
theorem unipotent_elementary_card_le [Finite F]
    (A : Subgroup (unipotent (K := F))) (hA : IsElementaryAbelian 2 A) :
    Nat.card A ≤ Nat.card F ^ 3 := by
  classical
  let := hA
  let p : A → Fin 6 → F := fun x => unipotentParameters x.val.val
  have hrep (x : A) : unipotentProduct (p x) = x.val.val := reconstruct x.val
  have hpinj : Function.Injective p := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    rw [← hrep x, ← hrep y, h]
  have hsquare (x : A) : unipotentProduct (p x) ^ 2 = 1 := by
    rw [hrep]
    exact congrArg (fun y : A => y.val.val)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p x)
  have hcomm (x y : A) : Commute (unipotentProduct (p x)) (unipotentProduct (p y)) := by
    rw [hrep, hrep]
    exact congrArg (fun z : A => z.val.val) (mul_comm x y)
  by_cases hnonzero : ∃ v : A, p v 5 ≠ 0
  · obtain ⟨v, hv⟩ := hnonzero
    let f : A → Fin 3 → F := fun x => ![p x 0, p x 1, p x 5]
    have hf : Function.Injective f := by
      intro x y h
      apply hpinj
      exact coordinates_recover (p v) (p x) (p y) hv (hsquare v)
        (hcomm v x) (hcomm v y) (congrFun h 0) (congrFun h 1) (congrFun h 2)
    simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective f hf
  · have hzero (x : A) : p x 5 = 0 := by simpa using not_exists.mp hnonzero x
    let r : A → Fin 4 → F := fun x => ![p x 1, p x 2, p x 3, p x 4]
    let W := Submodule.span F (Set.range r)
    have hW : Nat.card W ≤ Nat.card F ^ 2 := by
      apply span_card_le
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact commute_radical (p x) (p y) (hzero x) (hzero y) (hcomm x y)
    let f : A → F × W := fun x => ⟨p x 0, ⟨r x, Submodule.subset_span ⟨x, rfl⟩⟩⟩
    have hf : Function.Injective f := by
      intro x y h
      have h0 : p x 0 = p y 0 := congrArg Prod.fst h
      have hr : r x = r y := congrArg (fun z : F × W => z.2.val) h
      apply hpinj
      funext i
      fin_cases i
      · exact h0
      · exact congrFun hr 0
      · exact congrFun hr 1
      · exact congrFun hr 2
      · exact congrFun hr 3
      · exact (hzero x).trans (hzero y).symm
    calc
      Nat.card A ≤ Nat.card (F × W) := Nat.card_le_card_of_injective f hf
      _ = Nat.card F * Nat.card W := Nat.card_prod _ _
      _ ≤ Nat.card F * Nat.card F ^ 2 := Nat.mul_le_mul_left _ hW
      _ = Nat.card F ^ 3 := by ring

end Atlas.G2.EvenTwoRank
