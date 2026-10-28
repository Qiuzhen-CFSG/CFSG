module

public import Theory.GroupTheory.PGroup.C4SquareBasis
public import Mathlib.GroupTheory.Sylow

/-!
# The four automorphisms in the exotic action

On the coordinate C₄-square, the two inner involutions, interchange, and
inversion generate at least sixteen automorphisms. Sixteen words are
distinguished by their values on the coordinate basis. This finite check
allows generation in an abstract extension to be recovered from its faithful
action of order sixteen. Moreover every subgroup of order sixteen contains
inversion: it has index at most two in a Sylow subgroup, where inversion is
a central square.

These are the base actions in Janko–Thompson, Math. Z. 113 (1970), 1.4(c),
printed p.386. No assertion about existence of the actions in an abstract
extension, or about squares of their lifts, is made here.
-/

namespace ExoticTwoGroup.ActionModel

open C4SquareExtension Subgroup

/-- The first coordinate generator. -/
public def u : Model := (Multiplicative.ofAdd 1, 1)
/-- The second coordinate generator. -/
public def v : Model := (1, Multiplicative.ofAdd 1)

public theorem u_eq : u = (Multiplicative.ofAdd 1, 1) := by decide
public theorem v_eq : v = (1, Multiplicative.ofAdd 1) := by decide

private def act₁ (x : Model) : Model :=
  (Multiplicative.ofAdd (-x.1.toAdd + 2 * x.2.toAdd),
    Multiplicative.ofAdd (-x.2.toAdd))
private def act₂ (x : Model) : Model :=
  (Multiplicative.ofAdd (-x.1.toAdd),
    Multiplicative.ofAdd (2 * x.1.toAdd - x.2.toAdd))
private theorem act₁_invol : ∀ x : Model, act₁ (act₁ x) = x := by decide
private theorem act₂_invol : ∀ x : Model, act₂ (act₂ x) = x := by decide

/-- The action `a ↦ a⁻¹`, `b ↦ a²b⁻¹`. -/
public def inner₁ : MulAut Model where
  toFun := act₁
  invFun := act₁
  left_inv := act₁_invol
  right_inv := act₁_invol
  map_mul' x y := by
    ext <;> simp only [act₁, Prod.fst_mul, Prod.snd_mul,
      toAdd_mul, toAdd_ofAdd] <;> ring

/-- The action `a ↦ a⁻¹b²`, `b ↦ b⁻¹`. -/
public def inner₂ : MulAut Model where
  toFun := act₂
  invFun := act₂
  left_inv := act₂_invol
  right_inv := act₂_invol
  map_mul' x y := by
    ext <;> simp only [act₂, Prod.fst_mul, Prod.snd_mul,
      toAdd_mul, toAdd_ofAdd] <;> ring

/-- Interchange of the coordinate generators. -/
public def swap : MulAut Model := MulEquiv.prodComm
/-- Simultaneous inversion of the coordinate generators. -/
public def inversion : MulAut Model := MulEquiv.inv Model

public theorem inner₁_u : inner₁ u = u⁻¹ := by decide
public theorem inner₁_v : inner₁ v = u ^ 2 * v⁻¹ := by decide
public theorem inner₂_u : inner₂ u = u⁻¹ * v ^ 2 := by decide
public theorem inner₂_v : inner₂ v = v⁻¹ := by decide
public theorem swap_u : swap u = v := by decide
public theorem swap_v : swap v = u := by decide
public theorem inversion_u : inversion u = u⁻¹ := by decide
public theorem inversion_v : inversion v = v⁻¹ := by decide
public theorem u_four : u ^ 4 = 1 := by decide
public theorem v_four : v ^ 4 = 1 := by decide

private theorem decomp : ∀ x : Model, ∃ i j : Fin 4,
    x = u ^ i.val * v ^ j.val := by decide

/-- The two displayed basis actions determine a model automorphism. -/
public theorem aut_ext {α β : MulAut Model}
    (hu : α u = β u) (hv : α v = β v) : α = β := by
  apply MulEquiv.ext
  intro x
  obtain ⟨i, j, rfl⟩ := decomp x
  simp only [map_mul, map_pow, hu, hv]

public theorem basis : closure ({u, v} : Set Model) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, j, rfl⟩ := decomp x
  exact mul_mem (pow_mem (subset_closure (by simp)) _)
    (pow_mem (subset_closure (by simp)) _)

public theorem omega_basis : omega₁ Model (p := 2) =
    closure ({u ^ 2, v ^ 2} : Set Model) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    have hs : ∀ x : Model, x ^ 2 = 1 →
        x = 1 ∨ x = u ^ 2 ∨ x = v ^ 2 ∨ x = u ^ 2 * v ^ 2 := by decide
    rcases hs x (by simpa using hx) with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · apply (closure_le _).mpr
    intro x hx
    rcases (by simpa using hx : x = u ^ 2 ∨ x = v ^ 2) with rfl | rfl
    · exact subset_closure (by decide)
    · exact subset_closure (by decide)

private abbrev Bits := Fin 2 × Fin 2 × Fin 2 × Fin 2
private def word (q : Bits) : MulAut Model :=
  inner₁ ^ q.1.val * inner₂ ^ q.2.1.val * swap ^ q.2.2.1.val * inversion ^ q.2.2.2.val

private theorem word_injective : Function.Injective word := by
  have h : Function.Injective (fun q : Bits => (word q u, word q v)) := by decide
  intro q r heq
  exact h (congrArg (fun f : MulAut Model => (f u, f v)) heq)

/-- Any automorphism subgroup containing the four prescribed actions has
order at least sixteen. -/
public theorem sixteen_le_card (A : Subgroup (MulAut Model))
    (h₁ : inner₁ ∈ A) (h₂ : inner₂ ∈ A) (ht : swap ∈ A) (hz : inversion ∈ A) :
    16 ≤ Nat.card A := by
  let f : Bits → A := fun q => ⟨word q,
    mul_mem (mul_mem (mul_mem (pow_mem h₁ _) (pow_mem h₂ _)) (pow_mem ht _))
      (pow_mem hz _)⟩
  have hi : Function.Injective f := fun q r h => word_injective (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective f hi
  simpa only [Nat.card_prod, Nat.card_fin] using h

private def quarterTurn : MulAut Model :=
  MulEquiv.prodComm.trans ((MulEquiv.refl _).prodCongr (MulEquiv.inv _))

private theorem quarterTurn_square : quarterTurn ^ 2 = inversion := by
  apply MulEquiv.ext
  exact (by decide : ∀ x : Model, (quarterTurn ^ 2) x = inversion x)

private theorem quarterTurn_four : quarterTurn ^ 4 = 1 := by
  apply MulEquiv.ext
  exact (by decide : ∀ x : Model, (quarterTurn ^ 4) x = x)

private theorem inversion_central (β : MulAut Model) : Commute β inversion := by
  apply MulEquiv.ext
  intro x
  change β x⁻¹ = (β x)⁻¹
  exact map_inv β x

open scoped Pointwise in
/-- An automorphism subgroup of order sixteen always contains inversion.
Inversion is a central square in every Sylow two-subgroup, and the supplied
subgroup has index at most two in a Sylow containing it. -/
public theorem inversion_mem_of_card_sixteen (A : Subgroup (MulAut Model))
    (hA : Nat.card A = 16) : inversion ∈ A := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 4) hA
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  have hroot : IsPGroup 2 (zpowers quarterTurn) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one quarterTurn_four)
  obtain ⟨T, hT⟩ := hroot.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut Model) T S
  have hy : (MulAut.conj g) quarterTurn ∈ S := by
    rw [← hg]
    change (MulAut.conj g) • quarterTurn ∈ (MulAut.conj g) • (T : Set (MulAut Model))
    exact Set.smul_mem_smul_set (hT (mem_zpowers quarterTurn))
  let y : S := ⟨(MulAut.conj g) quarterTurn, hy⟩
  have hysq : (y : MulAut Model) ^ 2 = inversion := by
    change ((MulAut.conj g) quarterTurn) ^ 2 = inversion
    rw [← map_pow, quarterTurn_square]
    change g * inversion * g⁻¹ = inversion
    rw [(inversion_central g).eq, mul_inv_cancel_right]
  let K : Subgroup S := A.subgroupOf S
  have hK : Nat.card K = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv]
    exact hA
  have hS : Nat.card S ≤ 32 := by
    have hdiv := model_aut_subgroup_card_dvd (S : Subgroup (MulAut Model))
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    have hnle : n ≤ 5 := by
      by_contra! hnlarge
      have hbad : 64 ∣ 96 := (Nat.pow_dvd_pow 2 (show 6 ≤ n by omega)).trans
        (hn ▸ hdiv)
      norm_num at hbad
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) hnle
  have hi : K.index = 1 ∨ K.index = 2 := by
    have hc := K.card_mul_index
    rw [hK] at hc
    have hp : 0 < Nat.card S := Nat.card_pos
    omega
  have hmem : y ^ 2 ∈ K := by
    rcases hi with hi | hi
    · rw [index_eq_one.mp hi]
      trivial
    · exact K.sq_mem_of_index_two hi y
  change (y : MulAut Model) ^ 2 ∈ A at hmem
  rwa [hysq] at hmem

end ExoticTwoGroup.ActionModel
