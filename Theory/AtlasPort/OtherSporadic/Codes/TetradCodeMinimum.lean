/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TetradCodeQuotient

/-!
# TetradCodeMinimum

The recovered Kleinian code of a tetrad code has minimum weight four and is monomially
equivalent to the hexacode. Adjusting constant tetrad bits would otherwise produce a
forbidden binary word of weight below eight.

Source: `Atlas/Codes/TetradCodeMinimum.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

/-- The constants in the unique even-block decomposition. -/
def tetradRemainder (E : Submodule Bit BinaryWord) : tetradEvenSubcode E →ₗ[Bit] (Fin 6 → Bit) where
  toFun w i := w.val.val (hexPos i,0)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem tetradEven_decomposition (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (w : tetradEvenSubcode E) :
    w.val.val = jWord (tetradDecode E w) + rho (tetradRemainder E w) := by
  funext p
  obtain ⟨i,k⟩ := p
  have hb := even_block_decomposition (fun k => w.val.val (i,k))
    ((tetradEvenSubcode_mem E hE w.val).mp w.prop i)
  simpa [jWord,rho,tetradDecode,tetradRemainder] using congrFun hb k

theorem tetradEven_change_constants (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (w : tetradEvenSubcode E) (s : Fin 6 → Bit)
    (hs : ∑ i, s i = ∑ i, tetradRemainder E w i) :
    jWord (tetradDecode E w) + rho s ∈ E := by
  have hp : tetradRemainder E w + s ∈ P6 := by
    apply (parityCode_mem 5 _).mpr
    simp [Finset.sum_add_distrib,hs]
  have he := E.add_mem w.val.prop (hE.repetitions (show rho (tetradRemainder E w+s) ∈ R0 from ⟨_,hp,rfl⟩))
  rw [tetradEven_decomposition E hE w,map_add] at he
  have hx : jWord (tetradDecode E w) + rho (tetradRemainder E w) +
      (rho (tetradRemainder E w) + rho s) = jWord (tetradDecode E w) + rho s := by
    funext p
    simp only [Pi.add_apply,add_assoc]
    rw [← add_assoc (rho (tetradRemainder E w) p),bit_self_add,zero_add]
  exact hx ▸ he

/-- Complementing a nonconstant even tetrad leaves its weight equal to two. -/
theorem j_constant_nonzero_weight : ∀ u : K, u ≠ 0 → ∀ r : Bit,
    hammingNorm (j u + fun _ => r) = 2 := by decide

theorem tetradHexacode_minimum (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (h : HexWord) (hh : h ∈ tetradHexacode E) (hn : h ≠ 0) : 4 ≤ hammingNorm h := by
  classical
  obtain ⟨w,rfl⟩ := hh
  obtain ⟨i,hi⟩ : ∃ i, tetradDecode E w i ≠ 0 := Function.ne_iff.mp hn
  let s : Fin 6 → Bit := Pi.single (hexIndexEquiv i) (∑ k, tetradRemainder E w k)
  let v := jWord (tetradDecode E w) + rho s
  have hv : v ∈ E := tetradEven_change_constants E hE w s (by simp [s])
  have hd : ∀ j, blockDecode (fun k => v (j,k)) = tetradDecode E w j := by
    intro j
    change blockDecode (Atlas.Codes.j (tetradDecode E w j) + fun _ => s (hexIndexEquiv j)) = _
    simp
  have hvn : v ≠ 0 := by
    intro hz
    have ht := hd i
    rw [hz] at ht
    exact hi (by simpa using ht.symm)
  have hwt : hammingNorm v = 2 * hammingNorm (tetradDecode E w) := by
    rw [hammingNorm_prod,hammingNorm_eq_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change hammingNorm (Atlas.Codes.j (tetradDecode E w j) + fun _ => s (hexIndexEquiv j)) = _
    by_cases hj : tetradDecode E w j = 0
    · have hji : j ≠ i := by intro he; subst j; exact hi hj
      simp [hj,s,Ne.symm hji]
      rfl
    · rw [j_constant_nonzero_weight _ hj]
      simp [hj]
  have hm := hE.minimum v hv hvn
  rw [hwt] at hm
  omega

theorem tetradHexacode_unique (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    MonomiallyEquivalent (tetradHexacode E) hexacode :=
  hexacode_unique_of_dimension_minimum _ (tetradHexacode_finrank E hE)
    (tetradHexacode_minimum E hE)

theorem tetradHexacode_even (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (h : HexWord) (hh : h ∈ tetradHexacode E) : Even (hammingNorm h) := by
  obtain ⟨g,hg⟩ := tetradHexacode_unique E hE
  have he := hexacode_even (Monomial.act g h) ((hg h).mp hh)
  simpa only [Monomial.act_weight] using he

end Atlas.Codes
