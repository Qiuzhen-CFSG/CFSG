module

public import Theory.GroupTheory.PGroup.NormalEightCentralAction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index

/-!
# Conjugation on a normal C₄ × C₄ subgroup

Let D be normal, abelian and self-centralizing in a finite 2-group with central
omega subgroup of order four and no normal elementary subgroup of order eight.
Every elementary abelian subgroup has conjugation image on D of order at most
four when D is isomorphic to C₄ × C₄.

Ambient conjugation fixes every involution in D. The subgroup of automorphisms
with this property is abelian and has order at most sixteen. Five explicit
nonidentity automorphisms I + 2M invert only elements of square one, so the
normal elementary eight obstruction excludes them from the elementary action
image. Their product is one. An image of order greater than four would have
index two in the full subgroup, contradicting this odd product of outsiders.
The small coordinate identities below are checked by the kernel using `decide`.

Source: the MacWilliams–Sah bound quoted in Janko–Thompson, Math. Z. 113 (1970),
1.1, printed p.385, in
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace IsPGroup
namespace C4SquareAction

private abbrev V := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
private abbrev B := Fin 2 × Fin 2 × Fin 2 × Fin 2

-- The congruence automorphism I + 2M, with the four entries of M binary.
private def act (m : B) (x : V) : V :=
  (Multiplicative.ofAdd ((1 + 2 * (m.1.val : ZMod 4)) * x.1.toAdd +
    2 * (m.2.1.val : ZMod 4) * x.2.toAdd),
   Multiplicative.ofAdd (2 * (m.2.2.1.val : ZMod 4) * x.1.toAdd +
    (1 + 2 * (m.2.2.2.val : ZMod 4)) * x.2.toAdd))

private theorem act_invol : ∀ m : B, ∀ x : V, act m (act m x) = x := by decide

private def aut (m : B) : MulAut V where
  toFun := act m
  invFun := act m
  left_inv := act_invol m
  right_inv := act_invol m
  map_mul' x y := by
    ext <;> simp only [act, Prod.fst_mul, Prod.snd_mul,
      toAdd_mul, toAdd_ofAdd] <;> ring

-- The full subgroup fixing every element of square one.
private def K : Subgroup (MulAut V) where
  carrier := {f | ∀ x : V, x ^ 2 = 1 → f x = x}
  one_mem' := by simp
  mul_mem' := by
    intro f g hf hg x hx
    change f (g x) = x
    rw [hg x hx, hf x hx]
  inv_mem' := by
    intro f hf x hx
    apply f.injective
    simpa using (hf x hx).symm

private theorem aut_mem : ∀ m : B, aut m ∈ K := by
  change ∀ m : B, ∀ x : V, x ^ 2 = 1 → act m x = x
  decide

private def u : V := (Multiplicative.ofAdd 1, 1)
private def v : V := (1, Multiplicative.ofAdd 1)

private theorem decomp : ∀ x : V, x = u ^ x.1.toAdd.val * v ^ x.2.toAdd.val := by decide

private theorem hom_ext (f g : MulAut V) (hu : f u = g u) (hv : f v = g v) : f = g := by
  apply MulEquiv.ext
  intro x
  rw [decomp x, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hu, hv]

-- Images of the two standard generators determine an automorphism.
private theorem K_card : Nat.card K ≤ 16 := by
  let W := {p : V × V // p.1 ^ 2 = u ^ 2 ∧ p.2 ^ 2 = v ^ 2}
  let f : K → W := fun a => ⟨(a.1 u, a.1 v), by
    constructor
    · rw [← map_pow]; exact a.2 _ (by decide)
    · rw [← map_pow]; exact a.2 _ (by decide)⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply hom_ext
    · exact congrArg (fun p : W => p.1.1) h
    · exact congrArg (fun p : W => p.1.2) h
  have hc : Nat.card W = 16 := by rw [Nat.card_eq_fintype_card]; decide
  exact hc ▸ Nat.card_le_card_of_injective f hf

private theorem square : ∀ x : V, (x ^ 2) ^ 2 = 1 := by decide

-- Conjugation differences have square one, so both automorphisms fix them.
private theorem K_comm (f g : K) : Commute (f : MulAut V) (g : MulAut V) := by
  have diff (f : K) (x : V) : (f.1 x * x⁻¹) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, f.2 _ (square x), inv_pow, mul_inv_cancel]
  have calcfg (f g : K) (x : V) : f.1 (g.1 x) = f.1 x * (g.1 x * x⁻¹) := by
    have h := f.2 _ (diff g x)
    rw [map_mul, map_inv] at h
    calc
      f.1 (g.1 x) = (f.1 (g.1 x) * (f.1 x)⁻¹) * f.1 x := by group
      _ = _ := by rw [h]; ac_rfl
  apply MulEquiv.ext
  intro x
  change f.1 (g.1 x) = g.1 (f.1 x)
  rw [calcfg, calcfg]
  ac_rfl

private def b₁ : B := (0, 1, 0, 0)
private def b₂ : B := (0, 0, 1, 0)
private def b₃ : B := (1, 1, 1, 0)
private def b₄ : B := (0, 1, 1, 1)
private def b₅ : B := (1, 1, 1, 1)

private def Bad (m : B) : Prop := m = b₁ ∨ m = b₂ ∨ m = b₃ ∨ m = b₄ ∨ m = b₅
private instance (m : B) : Decidable (Bad m) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

private theorem bad_inverted : ∀ m : B, Bad m → ∀ x : V, aut m x = x⁻¹ → x ^ 2 = 1 := by decide

private theorem bad_ne : ∀ m : B, Bad m → act m u ≠ u ∨ act m v ≠ v := by decide

private theorem bad_product : aut b₁ * aut b₂ * aut b₃ * aut b₄ * aut b₅ = 1 := by
  apply MulEquiv.ext
  exact (by decide : ∀ x : V,
    act b₁ (act b₂ (act b₃ (act b₄ (act b₅ x)))) = x)

private def ka (m : B) : K := ⟨aut m, aut_mem m⟩

-- An image larger than four has index two. The five outsiders have product one.
private theorem bound (H : Subgroup K) (hH : IsPGroup 2 H)
    (hex : ∀ m, Bad m → ka m ∉ H) : Nat.card H ≤ 4 := by
  by_contra! hlarge
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  have hn3 : 3 ≤ n := by
    by_contra! h
    have hn4 : 2 ^ n ≤ 4 := by interval_cases n <;> decide
    omega
  have h8 : 8 ≤ Nat.card H := by
    rw [hn]
    exact (show (2 : ℕ) ^ 3 ≤ 2 ^ n from Nat.pow_le_pow_right (by omega) hn3)
  have hproper : H ≠ ⊤ := by
    intro h
    exact hex b₁ (Or.inl rfl) (by rw [h]; trivial)
  have hi := H.one_lt_index_of_ne_top hproper
  have hc := H.card_mul_index
  have hk := K_card
  have hi2 : H.index = 2 := by nlinarith
  have hp : ka b₁ * ka b₂ * ka b₃ * ka b₄ * ka b₅ = 1 :=
    Subtype.ext bad_product
  have he₁ := hex b₁ (by simp [Bad])
  have he₂ := hex b₂ (by simp [Bad])
  have he₃ := hex b₃ (by simp [Bad])
  have he₄ := hex b₄ (by simp [Bad])
  have he₅ := hex b₅ (by simp [Bad])
  have hm : ka b₁ * ka b₂ * ka b₃ * ka b₄ * ka b₅ ∈ H := hp ▸ H.one_mem
  simp only [Subgroup.mul_mem_iff_of_index_two hi2, he₁, he₂, he₃, he₄, he₅] at hm
  tauto

end C4SquareAction

open Subgroup C4SquareAction

/-- The exponent-four homocyclic case of the elementary conjugation-image bound. -/
public theorem conj_image_card_le_four_of_c4_square_of_no_normal_eight {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (Subgroup.center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : Subgroup.centralizer (D : Set P) ≤ D)
    (e : D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤ 4 := by
  let c : P →* MulAut D := MulAut.conjNormal
  let F : P →* MulAut V := (MulAut.congr e).toMonoidHom.comp c
  have hF (g : P) : F g ∈ K := by
    intro x hx
    change e (c g (e.symm x)) = x
    have hs : (e.symm x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    rw [IsPGroup.conjNormal_fixed_of_square_eq_one_of_no_normal_eight hno hZ D hD g _ hs]
    exact e.apply_symm_apply x
  let Fk : P →* K := F.codRestrict K hF
  let H := (Fk.comp A.subtype).range
  have hex (m : B) (hm : Bad m) : ka m ∉ H := by
    rintro ⟨a, ha⟩
    have hact : F (a : P) = aut m := congrArg Subtype.val ha
    have hx : (a : P) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (a : P) a.property
    have hcomm (g : P) : Commute (c g) (c (a : P)) := by
      apply Commute.of_map (MulAut.congr e).injective
      exact K_comm (Fk g) (Fk (a : P))
    have hinv (d : P) (hd : d ∈ D) (hinv : (a : P) * d * (a : P)⁻¹ = d⁻¹) :
        d ^ 2 = 1 := by
      let d' : D := ⟨d, hd⟩
      have heq : aut m (e d') = (e d')⁻¹ := by
        rw [← hact]
        change e (c (a : P) (e.symm (e d'))) = (e d')⁻¹
        rw [e.symm_apply_apply, ← map_inv]
        apply congrArg e
        exact Subtype.ext hinv
      have hh := bad_inverted m hm (e d') heq
      have hd' : d' ^ 2 = 1 := e.injective (by simpa only [map_pow, map_one] using hh)
      exact congrArg Subtype.val hd'
    have haD := IsPGroup.involution_mem_normal_abelian_of_central_action_of_no_normal_eight
      hno hZ D hD a hx hcomm hinv
    have hid : c (a : P) = 1 := by
      apply MulEquiv.ext
      intro d
      apply Subtype.ext
      change (a : P) * (d : P) * (a : P)⁻¹ = d
      have hc := ((@IsMulCommutative.is_comm D _ _).comm (⟨a, haD⟩ : D) d)
      have hc' := congrArg Subtype.val hc
      change (a : P) * (d : P) = (d : P) * (a : P) at hc'
      rw [hc', mul_inv_cancel_right]
    have haut : aut m = 1 := by
      rw [← hact]
      change (MulAut.congr e) (c (a : P)) = 1
      rw [hid, map_one]
    rcases bad_ne m hm with hb | hb
    · exact hb (congrArg (fun f : MulAut V => f u) haut)
    · exact hb (congrArg (fun f : MulAut V => f v) haut)
  have hHp : IsPGroup 2 H :=
    (hP.to_subgroup A).of_surjective
      (Fk.comp A.subtype).rangeRestrict (Fk.comp A.subtype).rangeRestrict_surjective
  have hbound := bound H hHp hex
  let j : (c.comp A.subtype).range → H := fun t =>
    ⟨⟨(MulAut.congr e) t.1, by
      obtain ⟨a, ha⟩ := t.2
      rw [← ha]
      exact hF a⟩, by
      obtain ⟨a, ha⟩ := t.2
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact congrArg (MulAut.congr e) ha⟩
  have hj : Function.Injective j := by
    intro t s h
    apply Subtype.ext
    apply (MulAut.congr e).injective
    exact congrArg (fun x : H => (x.1 : MulAut V)) h
  exact (Nat.card_le_card_of_injective j hj).trans hbound

end IsPGroup
