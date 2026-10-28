module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry
public import Mathlib.GroupTheory.Sylow

/-!
# The concrete Sylow subgroup of PSL₃ over an even field

The intersection of the two local fixing groups consists exactly of upper
unitriangular matrices. The coordinate equivalences below reuse the marked
UT₃ group and commute with its literal SL₃ and PSL₃ embeddings.
The ambient order is counted through the actual scalar kernel of order
`gcd(3,q-1)`. The index of the unipotent group is odd when `q=2^n`,
so its order `q^3` makes it Sylow.

Source: Aschbacher–Smith, F.1.12(I)(1), printed pp.262–264.
-/

@[expose] public section
open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F]
theorem mem_unipotentSL_iff (g : SL(3,F)) : g ∈ unipotentSL F ↔
    g.val = !![1,g.val 0 1,g.val 0 2; 0,1,g.val 1 2; 0,0,1] := by
  rw [unipotentSL, Subgroup.mem_inf, mem_pointLocalSL_iff, mem_lineLocalSL_iff]
  constructor
  · rintro ⟨⟨h00,h10,h20⟩,⟨_,h21,h22⟩⟩
    have h11 : g.val 1 1 = 1 := by
      have h := g.property
      rw [Matrix.det_fin_three, h00,h10,h20,h21,h22] at h
      simpa only [zero_mul, mul_zero, one_mul, mul_one, add_zero, sub_zero] using h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00,h10,h20,h11,h21,h22]
  · intro h
    have h00 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) h
    have h10 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 1 0) h
    have h20 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 0) h
    have h21 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 1) h
    have h22 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 2) h
    exact ⟨⟨h00,h10,h20⟩,⟨h20,h21,h22⟩⟩

theorem specialLinear_range : (specialLinear F).range = unipotentSL F := by
  ext g
  constructor
  · rintro ⟨u,rfl⟩
    rw [mem_unipotentSL_iff]
    rfl
  · intro hg
    refine ⟨⟨g.val 0 1,g.val 1 2,g.val 0 2⟩, ?_⟩
    exact Subtype.ext ((mem_unipotentSL_iff F g).mp hg).symm

noncomputable def unipotentSLEquiv : U F ≃* unipotentSL F :=
  (matrixEquiv F).trans (MulEquiv.subgroupCongr (specialLinear_range F))

theorem projective_range : (projective F).range = unipotent F := by
  change ((projection F).comp (specialLinear F)).range = _
  rw [unipotent, ← specialLinear_range, MonoidHom.range_comp]

noncomputable def unipotentEquiv : U F ≃* unipotent F :=
  (projectiveEquiv F).trans (MulEquiv.subgroupCongr (projective_range F))

@[simp] theorem unipotentSLEquiv_apply (u : U F) :
    (unipotentSLEquiv F u : SL(3,F)) = specialLinear F u := rfl
@[simp] theorem unipotentEquiv_apply (u : U F) :
    (unipotentEquiv F u : PSL(3,F)) = projection F (specialLinear F u) := rfl

variable [Finite F]

theorem card_unipotentSL : Nat.card (unipotentSL F) = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (unipotentSLEquiv F).toEquiv, card_U]
theorem card_unipotent : Nat.card (unipotent F) = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (unipotentEquiv F).toEquiv, card_U]

theorem card_projective_mul_scalar :
    Nat.card PSL(3,F) * Nat.gcd 3 (Nat.card F - 1) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  change Nat.card PSL(3,F) * Nat.gcd 3 (q-1) * (q-1) = _ at h
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have h1 : q^3-q = q*(q^2-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q^3-q^2 = q^2*(q-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  rw [h1,h2] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q-1 by omega)
  change Nat.card PSL(3,F) * Nat.gcd 3 (q-1) * (q-1) = _
  rw [h]
  ring

theorem card_projective :
    Nat.card PSL(3,F) =
      (Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) /
        Nat.gcd 3 (Nat.card F - 1) := by
  rw [← card_projective_mul_scalar F, Nat.mul_div_cancel]
  exact Nat.gcd_pos_of_pos_left _ (by decide)

theorem index_unipotent_mul_scalar :
    (unipotent F).index * Nat.gcd 3 (Nat.card F - 1) =
      (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  have h := card_projective_mul_scalar F
  rw [← (unipotent F).card_mul_index, card_unipotent F] at h
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F ^ 3 from pow_pos Nat.card_pos _)
  simpa only [Nat.mul_assoc] using h

theorem index_unipotent :
    (unipotent F).index = ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) /
      Nat.gcd 3 (Nat.card F - 1) := by
  rw [← index_unipotent_mul_scalar F, Nat.mul_div_cancel]
  exact Nat.gcd_pos_of_pos_left _ (by decide)

theorem unipotent_isTwoGroup {n : ℕ} (hF : Nat.card F = 2^n) :
    IsPGroup 2 (unipotent F) := by
  apply IsPGroup.of_card (n := n*3)
  rw [card_unipotent F, hF, pow_mul]

theorem odd_index_unipotent {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    ¬ 2 ∣ (unipotent F).index := by
  have he : Nat.card F % 2 = 0 := by simp [hF, Nat.pow_mod, Nat.ne_of_gt hn]
  have he2 : (Nat.card F ^ 2) % 2 = 0 := by simp [Nat.pow_mod, he]
  have he3 : (Nat.card F ^ 3) % 2 = 0 := by simp [Nat.pow_mod, he]
  have hp2 : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos _
  have hp3 : 0 < Nat.card F ^ 3 := pow_pos Nat.card_pos _
  have hn2 : ¬ 2 ∣ Nat.card F ^ 2 - 1 := by omega
  have hn3 : ¬ 2 ∣ Nat.card F ^ 3 - 1 := by omega
  intro h
  have hd := dvd_mul_of_dvd_left h (Nat.gcd 3 (Nat.card F - 1))
  rw [index_unipotent_mul_scalar F] at hd
  exact (Nat.prime_two.not_dvd_mul hn3 hn2) hd

noncomputable def unipotentSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    Sylow 2 PSL(3,F) :=
  (unipotent_isTwoGroup F hF).toSylow (odd_index_unipotent F hn hF)

@[simp] theorem coe_unipotentSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    (unipotentSylow F hn hF : Subgroup PSL(3,F)) = unipotent F := rfl
end Matrix.PSL3.LinearThree
