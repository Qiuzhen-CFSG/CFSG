module

public import Theory.ElementaryAbelian.BinaryAlternatingPencilRadicals
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.LinearAlgebra.BinaryAlternatingPencilSpan
public import Mathlib.FieldTheory.Finiteness

/-!
# The order of the canonical radical span

For a separating alternating pairing from an elementary abelian group of
order 32 to one of order four, if every line radical has order two, their
span has order at least eight. Two target coordinates give scalar forms
whose three radicals are lines with trivial common intersection. The linear
span theorem then gives dimension at least three, hence order at least eight.

Source: MacWilliams, Trans. AMS 150 (1970), §4; JT 1.4(c), p.386.
-/

open scoped IsMulCommutative
open Module
namespace BinaryAlternatingPencil

private abbrev subspace {G : Type*} [Group G] [IsElementaryAbelian 2 G] :
    Subgroup G ≃o Submodule (ZMod 2) (Additive G) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

private theorem card_subspace {G : Type*} [Group G] [Finite G]
    [IsElementaryAbelian 2 G] (H : Subgroup G) :
    Nat.card H = 2 ^ finrank (ZMod 2) (subspace H) := by
  have hc : Nat.card H = Nat.card (subspace H) := by rfl
  rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

private theorem finrank_of_card {G : Type*} [Group G] [Finite G]
    [IsElementaryAbelian 2 G] {n : ℕ} (hG : Nat.card G = 2 ^ n) :
    finrank (ZMod 2) (Additive G) = n := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G)
  exact (h.trans (by rw [Nat.card_zmod])).symm.trans hG

private def scalarForm {V W : Type*} [Group V] [Group W]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (b : V →* (V →* W)) (φ : Additive W →ₗ[ZMod 2] ZMod 2) :
    LinearMap.BilinForm (ZMod 2) (Additive V) :=
  ({ toFun x := φ.comp ((MonoidHom.toAdditive (b x.toMul)).toZModLinearMap 2)
     map_zero' := by
       ext y
       change φ (Additive.ofMul (b 1 y.toMul)) = 0
       simp
     map_add' x y := by
       ext z
       change φ (Additive.ofMul (b (x.toMul * y.toMul) z.toMul)) =
         φ (Additive.ofMul (b x.toMul z.toMul)) +
           φ (Additive.ofMul (b y.toMul z.toMul))
       rw [map_mul]
       exact map_add φ _ _ } : Additive V →+ (Additive V →ₗ[ZMod 2] ZMod 2)).toZModLinearMap 2

private theorem scalar_radical_data {V W : Type*} [Group V] [Group W]
    [Finite V] [Finite W] [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (b : V →* (V →* W))
    (hr : ∀ L : Subgroup W, Nat.card L = 2 → Nat.card (radicalOver b L) = 2)
    (φ : Additive W →ₗ[ZMod 2] ZMod 2) (hφ : φ ≠ 0) :
    finrank (ZMod 2) (scalarForm b φ).ker = 1 ∧
      (scalarForm b φ).ker ≤ subspace (radicalSpan b) := by
  have hdW : finrank (ZMod 2) (Additive W) = 2 := finrank_of_card hW
  have hdφ : finrank (ZMod 2) φ.ker = 1 := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    omega
  let L : Subgroup W := subspace.symm φ.ker
  have heq : subspace L = φ.ker := subspace.apply_symm_apply φ.ker
  have hL : Nat.card L = 2 := by rw [card_subspace, heq, hdφ]; rfl
  have hker : (scalarForm b φ).ker = subspace (radicalOver b L) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.ext_iff]
    change (∀ y : Additive V, φ (Additive.ofMul (b x.toMul y.toMul)) = 0) ↔
      x.toMul ∈ radicalOver b L
    rw [mem_radicalOver]
    rfl
  constructor
  · rw [hker]
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact (card_subspace (radicalOver b L)).symm.trans (hr L hL)
  · rw [hker]
    exact subspace.monotone (radicalOver_le_radicalSpan b L hL)

/-- Line radicals of a separating binary pencil in dimension five generate at least eight elements. -/
public theorem radicalSpan_card_ge_eight
    {V W : Type*} [Group V] [Group W] [Finite V] [Finite W]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hV : Nat.card V = 32) (hW : Nat.card W = 4)
    (b : V →* (V →* W)) (halt : ∀ x, b x x = 1)
    (hsep : ∀ x, (∀ y, b x y = 1) → x = 1)
    (hr : ∀ L : Subgroup W, Nat.card L = 2 → Nat.card (radicalOver b L) = 2) :
    8 ≤ Nat.card (radicalSpan b) := by
  have hdV : finrank (ZMod 2) (Additive V) = 5 := finrank_of_card hV
  have hdW : finrank (ZMod 2) (Additive W) = 2 := finrank_of_card hW
  let e := Module.finBasisOfFinrankEq (ZMod 2) (Additive W) hdW
  let φ := e.coord 0
  let ψ := e.coord 1
  have hφ : φ ≠ 0 := by
    intro hh
    have hh' := LinearMap.congr_fun hh (e 0)
    simp [φ] at hh'
  have hψ : ψ ≠ 0 := by
    intro hh
    have hh' := LinearMap.congr_fun hh (e 1)
    simp [ψ] at hh'
  have hφψ : φ+ψ ≠ 0 := by
    intro hh
    have hh' := LinearMap.congr_fun hh (e 0)
    simp [φ, ψ] at hh'
  let B := scalarForm b φ
  let C := scalarForm b ψ
  have hadd : scalarForm b (φ+ψ) = B+C := by ext x y; rfl
  obtain ⟨hdB, hBS⟩ := scalar_radical_data hW b hr φ hφ
  obtain ⟨hdC, hCS⟩ := scalar_radical_data hW b hr ψ hψ
  obtain ⟨hdBC, hBCS⟩ := scalar_radical_data hW b hr (φ+ψ) hφψ
  rw [hadd] at hdBC hBCS
  have hB : B.IsAlt := by
    intro x
    change φ (Additive.ofMul (b x.toMul x.toMul)) = 0
    rw [halt]
    exact map_zero φ
  have hC : C.IsAlt := by
    intro x
    change ψ (Additive.ofMul (b x.toMul x.toMul)) = 0
    rw [halt]
    exact map_zero ψ
  have hdis : Disjoint B.ker C.ker := by
    apply Submodule.disjoint_def.mpr
    intro x hx hy
    apply Additive.toMul.injective
    change x.toMul = 1
    apply hsep
    intro y
    have hz : Additive.ofMul (b x.toMul y) = 0 := by
      apply e.forall_coord_eq_zero_iff.mp
      intro i
      fin_cases i
      · exact LinearMap.congr_fun hx (Additive.ofMul y)
      · exact LinearMap.congr_fun hy (Additive.ofMul y)
    exact congrArg Additive.toMul hz
  have hd := three_le_finrank_radical_span hdV B C hB hC hdB hdC hdBC hdis
  have hm := Submodule.finrank_mono (sup_le (sup_le hBS hCS) hBCS)
  have hdS : 3 ≤ finrank (ZMod 2) (subspace (radicalSpan b)) := le_trans hd hm
  rw [card_subspace]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hdS

end BinaryAlternatingPencil
