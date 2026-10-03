module

public import Theory.ElementaryAbelian.BinaryAlternatingPencilRadicals
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.LinearAlgebra.AlternatingFinrank
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness

/-!
# Orders of the line radicals of a binary alternating pencil

For a separating alternating pencil from a five-dimensional binary space to
a two-dimensional binary space, transitivity on nonzero target vectors forces
every line radical to have dimension one. A scalar form has even rank, so each
radical has odd dimension. Two distinct line radicals are disjoint and have
equal dimension, forcing that dimension to be at most two.

This is the radical-order step in MacWilliams, Trans. AMS 150 (1970), §4;
cf. Janko–Thompson, Math. Z. 113 (1970), Lemma 1.4(c), p.386.
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

private theorem exists_other_line {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (L : Subgroup W) (hL : Nat.card L = 2) :
    ∃ M : Subgroup W, Nat.card M = 2 ∧ L ≠ M := by
  have hdW : finrank (ZMod 2) (Additive W) = 2 := finrank_of_card hW
  have hdL : finrank (ZMod 2) (subspace L) = 1 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact (card_subspace L).symm.trans hL
  obtain ⟨M, hM⟩ := IsElementaryAbelian.exists_isCompl 2 W L
  have hcomp := subspace.isCompl_iff.mp hM
  have hdim := Submodule.finrank_add_eq_of_isCompl hcomp
  have hdM : finrank (ZMod 2) (subspace M) = 1 := by omega
  refine ⟨M, ?_, ?_⟩
  · rw [card_subspace, hdM]; rfl
  · intro heq
    have hb : L = ⊥ := disjoint_self.mp (heq ▸ hM.disjoint)
    rw [hb, Subgroup.card_bot] at hL
    omega

private theorem scalar_with_ker {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (L : Subgroup W) (hL : Nat.card L = 2) :
    ∃ φ : Additive W →ₗ[ZMod 2] ZMod 2, φ.ker = subspace L := by
  have hdW : finrank (ZMod 2) (Additive W) = 2 := finrank_of_card hW
  have hdL : finrank (ZMod 2) (subspace L) = 1 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact (card_subspace L).symm.trans hL
  have hlt : subspace L < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro heq
    rw [heq, finrank_top, hdW] at hdL
    omega
  obtain ⟨φ, hφ, hker⟩ := (subspace L).exists_le_ker_of_lt_top hlt
  refine ⟨φ, (Submodule.eq_of_le_of_finrank_eq hker ?_).symm⟩
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  omega

private theorem radical_even_codimension
    {V W : Type*} [Group V] [Group W] [Finite V] [Finite W]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (b : V →* (V →* W)) (halt : ∀ x, b x x = 1)
    (L : Subgroup W) (hL : Nat.card L = 2) :
    Even (finrank (ZMod 2) (Additive V) -
      finrank (ZMod 2) (subspace (radicalOver b L))) := by
  obtain ⟨φ, hφ⟩ := scalar_with_ker hW L hL
  let row (x : Additive V) : Additive V →ₗ[ZMod 2] Additive W :=
    (MonoidHom.toAdditive (b x.toMul)).toZModLinearMap 2
  let B : LinearMap.BilinForm (ZMod 2) (Additive V) :=
    ({ toFun x := φ.comp (row x)
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
  have hB : B.IsAlt := by
    intro x
    change φ (Additive.ofMul (b x.toMul x.toMul)) = 0
    rw [halt]
    exact map_zero φ
  have hker : B.ker = subspace (radicalOver b L) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.ext_iff]
    change (∀ y : Additive V, φ (Additive.ofMul (b x.toMul y.toMul)) = 0) ↔
      x.toMul ∈ radicalOver b L
    rw [mem_radicalOver]
    have hz (w : W) : φ (Additive.ofMul w) = 0 ↔ w ∈ L := by
      change Additive.ofMul w ∈ φ.ker ↔ _
      rw [hφ]
      rfl
    exact forall_congr' fun y => hz (b x.toMul y)
  rw [← hker]
  exact AlternatingForm.even_finrank_sub_finrank_ker B hB

/-- Transitive binary alternating pencils in dimension five have line radicals of order two. -/
public theorem radicalOver_card_two
    {V W : Type*} [Group V] [Group W] [Finite V] [Finite W]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hV : Nat.card V = 32) (hW : Nat.card W = 4)
    (b : V →* (V →* W)) (halt : ∀ x, b x x = 1)
    (hsep : ∀ x, (∀ y, b x y = 1) → x = 1)
    (htrans : ∀ z₁ z₂ : W, z₁ ≠ 1 → z₂ ≠ 1 →
      ∃ (a : MulAut V) (c : MulAut W), c z₁ = z₂ ∧
        ∀ x y, b (a x) (a y) = c (b x y)) :
    ∀ L : Subgroup W, Nat.card L = 2 → Nat.card (radicalOver b L) = 2 := by
  intro L hL
  obtain ⟨M, hM, hLM⟩ := exists_other_line hW L hL
  have hdis := radicalOver_disjoint b hsep L M hL hM hLM
  have hcard := radicalOver_card_eq b htrans L M hL hM
  have hdim : finrank (ZMod 2) (subspace (radicalOver b L)) =
      finrank (ZMod 2) (subspace (radicalOver b M)) := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    simpa only [← card_subspace] using hcard
  have hdV : finrank (ZMod 2) (Additive V) = 5 := finrank_of_card hV
  have hdis' : Disjoint (subspace (radicalOver b L)) (subspace (radicalOver b M)) :=
    hdis.map subspace
  have hbound := Submodule.finrank_add_finrank_le_of_disjoint hdis'
  have hparity := radical_even_codimension hW b halt L hL
  rw [hdV] at hbound hparity
  have hdone : finrank (ZMod 2) (subspace (radicalOver b L)) = 1 := by
    obtain ⟨k, hk⟩ := hparity
    omega
  rw [card_subspace, hdone]
  rfl

end BinaryAlternatingPencil
