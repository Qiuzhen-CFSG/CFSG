module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Linear
import Mathlib.Tactic

/-!
# A restriction on the printed moving-layer pairing

A bilinear map from the natural three-space and its dual to the natural
three-space, equivariant for the same SL₃(2) marking, is zero. The proof
uses a transvection and a three-cycle. Their equations on the nine pairs
of basis vectors force all 27 coefficients to vanish. Only the two small
matrix calculations use finite kernel reduction; the coefficient elimination
is ordinary linear algebra in characteristic two.

The doubled version is used with the actual quotient actions in
`PairingObstruction`. This does not rule out the moving quotient in (iv).
It rules out a nonzero bilinear pairing of this particular type as its
recognition argument.

Source: the commutator-map sentence in the proof of MS93 (4.5.4)(iv),
Meierfrankenfeld--Stellmacher (1993), printed p.899.
-/

@[expose] public section

open Matrix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Linear
private def t : S := ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩
private def c : S := ⟨!![0,0,1; 1,0,0; 0,1,0], by decide⟩
private def e (i : Fin 3) : W := Pi.single i 1
private theorem ti : t⁻¹ = t := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel
private theorem ci : (c⁻¹).val.transpose = c.val := by
  have h : c⁻¹ = (⟨!![0,1,0; 0,0,1; 1,0,0], by decide⟩ : S) := by
    apply inv_eq_of_mul_eq_one_right
    decide +kernel
  rw [h]
  decide +kernel
private theorem te : ∀ i : Fin 3, t.val.mulVec (e i) =
    if i = 1 then e 0 + e 1 else e i := by decide +kernel
private theorem td : ∀ i : Fin 3, dual t (e i) =
    if i = 0 then e 0 + e 1 else e i := by
  simp only [dual, ti]
  decide +kernel
private theorem ce : ∀ i : Fin 3, c.val.mulVec (e i) = e (i + 1) := by decide +kernel
private theorem cd : ∀ i : Fin 3, dual c (e i) = e (i + 1) := by
  intro i
  rw [dual,ci,ce]
/-- There is no nonzero bilinear equivariant map natural × dual → natural. -/
theorem natural_dual_bilinear_zero (b : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W)
    (hb : ∀ g : S, ∀ v w : W,
      b (g.val.mulVec v) (dual g w) = g.val.mulVec (b v w)) : b = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h11 : (1 : Fin 3) + 1 = 2 := rfl
  have h21sum : (2 : Fin 3) + 1 = 0 := rfl
  have h (g : S) (i j k : Fin 3) := congrFun (hb g (e i) (e j)) k
  have ht000 := h t 0 0 0
  simp only [te, td] at ht000
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht000
  have ht001 := h t 0 0 1
  simp only [te, td] at ht001
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht001
  have ht002 := h t 0 0 2
  simp only [te, td] at ht002
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht002
  have ht020 := h t 0 2 0
  simp only [te, td] at ht020
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht020
  have ht100 := h t 1 0 0
  simp only [te, td] at ht100
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht100
  have ht101 := h t 1 0 1
  simp only [te, td] at ht101
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht101
  have ht102 := h t 1 0 2
  simp only [te, td] at ht102
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht102
  have ht120 := h t 1 2 0
  simp only [te, td] at ht120
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht120
  have ht122 := h t 1 2 2
  simp only [te, td] at ht122
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht122
  have ht200 := h t 2 0 0
  simp only [te, td] at ht200
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht200
  have ht201 := h t 2 0 1
  simp only [te, td] at ht201
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht201
  have ht202 := h t 2 0 2
  simp only [te, td] at ht202
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht202
  have ht220 := h t 2 2 0
  simp only [te, td] at ht220
  norm_num [map_add, LinearMap.add_apply, t, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at ht220
  have hc000 := h c 0 0 0
  simp only [ce, cd] at hc000
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc000
  have hc001 := h c 0 0 1
  simp only [ce, cd] at hc001
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc001
  have hc002 := h c 0 0 2
  simp only [ce, cd] at hc002
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc002
  have hc010 := h c 0 1 0
  simp only [ce, cd] at hc010
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc010
  have hc011 := h c 0 1 1
  simp only [ce, cd] at hc011
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc011
  have hc012 := h c 0 1 2
  simp only [ce, cd] at hc012
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc012
  have hc020 := h c 0 2 0
  simp only [ce, cd] at hc020
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc020
  have hc022 := h c 0 2 2
  simp only [ce, cd] at hc022
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc022
  have hc100 := h c 1 0 0
  simp only [ce, cd] at hc100
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc100
  have hc102 := h c 1 0 2
  simp only [ce, cd] at hc102
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc102
  have hc110 := h c 1 1 0
  simp only [ce, cd] at hc110
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc110
  have hc112 := h c 1 1 2
  simp only [ce, cd] at hc112
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc112
  have hc120 := h c 1 2 0
  simp only [ce, cd] at hc120
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc120
  have hc122 := h c 1 2 2
  simp only [ce, cd] at hc122
  norm_num [map_add, LinearMap.add_apply, c, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, h20, h21, h11, h21sum] at hc122
  have hz (i j k : Fin 3) : (b (e i) (e j)) k = 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht000 + ht002 + ht100 + ht102 + ht202 + hc000 + hc002 + hc102
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht000 + ht001 + ht002 + ht100 + ht101 + ht102 + ht202 + hc000 + hc001 + hc002 + hc102
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht000 + ht001 + ht100 + ht101 + ht202 + hc000 + hc001 + hc102
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht001 + ht002 + ht100 + ht101 + ht102 + ht202 + hc000 + hc001 + hc002 + hc102
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht001
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht002
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht001 + ht002 + ht100 + ht101 + ht102 + ht120 + ht202 + hc000 + hc001 + hc002 + hc011 + hc102
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht020
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht122
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht122 + hc020
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht202 + hc102
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht020 + hc022
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht000 + ht001 + ht100 + ht101 + ht202 + hc001 + hc102
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht000 + ht002 + ht100 + ht102 + ht202 + hc000 + hc001 + hc002 + hc102
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht000 + ht001 + ht002 + ht100 + ht101 + ht102 + ht202 + hc000 + hc001 + hc102
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht002 + hc010
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht001 + ht002 + ht100 + ht101 + ht102 + ht202 + hc000 + hc001 + hc002 + hc011 + hc102
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht001 + hc012
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht001 + hc012 + hc120
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht020 + ht200 + hc022 + hc100
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht001 + ht002 + ht100 + ht101 + ht102 + ht202 + hc000 + hc001 + hc002 + hc011 + hc102 + hc122
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht020 + hc022 + hc100
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht201
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht202
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht000 + ht001 + ht002 + ht100 + ht101 + ht102 + ht202 + hc000 + hc001 + hc102 + hc110
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht220
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) ht000 + ht002 + ht100 + ht102 + ht202 + hc000 + hc001 + hc002 + hc102 + hc112
  have hbasis (i j : Fin 3) : b (e i) (e j) = 0 := funext (hz i j)
  have hexp (v : W) : v = ∑ i : Fin 3, v i • e i := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply]
  have hrow (i : Fin 3) (w : W) : b (e i) w = 0 := by
    rw [hexp w, map_sum]
    simp [hbasis]
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change b v w = 0
  rw [hexp v, map_sum]
  simp [hrow]

private def pairEmbedding (i : Bool) : W →ₗ[ZMod 2] W × W where
  toFun v := if i then (v, 0) else (0, v)
  map_add' v w := by cases i <;> simp
  map_smul' r v := by cases i <;> simp

private def pairingFactor (b : (W × W) →ₗ[ZMod 2] (W × W) →ₗ[ZMod 2] W) (i j : Bool) :
    W →ₗ[ZMod 2] W →ₗ[ZMod 2] W where
  toFun v := (b (pairEmbedding i v)).comp (pairEmbedding j)
  map_add' v w := by ext x k; simp
  map_smul' r v := by ext x k; simp

/-- The same vanishing holds for the two doubled source factors. -/
theorem naturalPair_dualPair_bilinear_zero
    (b : (W × W) →ₗ[ZMod 2] (W × W) →ₗ[ZMod 2] W)
    (hb : ∀ (g : S) (v w : W × W),
      b (g.val.mulVec v.1, g.val.mulVec v.2) (dual g w.1, dual g w.2) =
        g.val.mulVec (b v w)) : b = 0 := by
  have hf (i j : Bool) : pairingFactor b i j = 0 := by
    apply natural_dual_bilinear_zero
    intro g v w
    have hh := hb g (pairEmbedding i v) (pairEmbedding j w)
    cases i <;> cases j <;>
      simpa only [pairingFactor, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
        pairEmbedding, Bool.false_eq_true, Bool.true_eq, reduceIte, dual,
        Matrix.mulVec_zero] using hh
  have hz (i j : Bool) (v w : W) : b (pairEmbedding i v) (pairEmbedding j w) = 0 :=
    congrArg (fun f : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W => f v w) (hf i j)
  have hexp (v : W × W) : v = pairEmbedding true v.1 + pairEmbedding false v.2 := by
    simp [pairEmbedding]
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change b v w = 0
  rw [hexp v, map_add, LinearMap.add_apply]
  rw [hexp w]
  simp only [map_add, hz, add_zero]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Linear
