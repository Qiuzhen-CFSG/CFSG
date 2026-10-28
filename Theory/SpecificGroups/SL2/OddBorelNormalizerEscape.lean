module
public import Theory.SpecificGroups.SL2.OddBorelMarking
public import Theory.GroupTheory.InvertingHallNormalizerEscape

/-!
# Odd subgroup normalizers escape a binary SL₂ Borel

Simultaneously diagonalize the odd subgroup inside its Sylow normalizer.
The Weyl matrix inverts every diagonal element and lies outside the upper
Borel. Conjugating back gives an element of the prescribed subgroup's
normalizer outside the original Sylow normalizer.

This intrinsic result retains the actual subgroup and Sylow. It is used to
choose a normalizing conjugator in Aschbacher–Smith 5.1.17, printed p.641,
without a decomposition theorem for the generated core quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem odd_subgroup_normalizer_not_le_sylow_normalizer
    (P : Sylow 2 SL(2,F)) (C : Subgroup SL(2,F))
    (hC : C ≤ normalizer (P : Set SL(2,F))) (ho : Odd (Nat.card C)) :
    ¬ normalizer (C : Set SL(2,F)) ≤ normalizer (P : Set SL(2,F)) := by
  obtain ⟨a,d,hP,hd⟩ := sylow_odd_subgroup_diagonal_coordinates P C hC ho
  let w : SL(2,F) := ⟨!![0,-1;1,0], by simp⟩
  let g := a⁻¹*w*a
  have hinv (x : C) : g*(x : SL(2,F))*g⁻¹ = (x : SL(2,F))⁻¹ := by
    have hw : w * diag2 (d x : F) (Units.ne_zero _) * w⁻¹ =
        (diag2 (d x : F) (Units.ne_zero _))⁻¹ := by
      rw [diag2_inv]
      apply Subtype.ext
      change (w.val * (diag2 (d x : F) (Units.ne_zero _)).val) * adjugate w.val =
        (diag2 (d x : F)⁻¹ (inv_ne_zero (Units.ne_zero _))).val
      rw [diag2_coe',diag2_coe']
      change (!![0,-1;1,0] * !![(d x : F),0;0,(d x : F)⁻¹]) *
        adjugate !![0,-1;1,0] = !![(d x : F)⁻¹,0;0,((d x : F)⁻¹)⁻¹]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [adjugate_fin_two,mul_apply,Fin.sum_univ_two]
    rw [← hd] at hw
    calc
      _ = a⁻¹*(w*(a*x*a⁻¹)*w⁻¹)*a := by dsimp [g]; group
      _ = a⁻¹*(a*(x : SL(2,F))*a⁻¹)⁻¹*a := by rw [hw]
      _ = _ := by group
  have hg := mem_normalizer_of_inverts_subgroup C g (fun x hx => hinv ⟨x,hx⟩)
  intro hn
  have hh := mem_map_of_mem (MulAut.conj a).toMonoidHom (hn hg)
  change (MulAut.conj a) g ∈ (normalizer ((P : Subgroup SL(2,F)) : Set SL(2,F))).map (MulAut.conj a).toMonoidHom at hh
  rw [map_equiv_normalizer_eq,hP] at hh
  have he : (MulAut.conj a) g = w := by change a*(a⁻¹*w*a)*a⁻¹ = w; group
  rw [he] at hh
  have hz := (mem_rankOneBorel_iff w).mp hh
  simp [w] at hz
end Matrix.SpecialLinearGroup
