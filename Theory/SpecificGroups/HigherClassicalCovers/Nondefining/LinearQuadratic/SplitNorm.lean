module

public import Theory.SpecificGroups.PSL4.OddSplitTorus
public import Theory.GroupTheory.PerfectCentralCoverCyclicNorm

/-!
# The cubic norm on the odd split torus of PSL₄

An odd finite subgroup U of the coefficient field's units gives an embedded
rank-three determinant-one diagonal torus in the literal quotient SL₄/Z(SL₄).
The scalar kernel is trivial because its order divides both |U| and four.
The determinant-one permutation of the first three coordinates normalizes
this torus. Its fixed points have coordinates (a,a,a), and (a,1,1) is a
preimage under the cubic orbit norm.

Consequently, for an actual perfect central cover, an abelian preimage of
this torus and prime-to-r index of the torus with its cubic supplement imply
that r does not divide the covering kernel. These two premises are retained
explicitly: this module does not yet establish the Sylow-index or commuting-
lifts calculations, or the separate nonsplit rank-two torus case.

Source: the degree-four linear covering calculation used in Aschbacher–Smith
A.2.17, printed p.39, with covering/transfer conventions I.1.1–I.1.2, printed
p.407. The diagonal map reuses `Matrix.PSL4.OddSplitTorus.torusFourHom`.
-/

@[expose] public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearQuadratic

variable {F : Type*} [Field F]

/-- The determinant-one cycle of the first three coordinates. -/
def cycleSL : SL(4,F) :=
  ⟨!![0,1,0,0; 0,0,1,0; 1,0,0,0; 0,0,0,1], by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Matrix.submatrix, Fin.succAbove]⟩

def cycle : PSL(4,F) := QuotientGroup.mk' _ (cycleSL (F := F))

def torusHom (U : Subgroup Fˣ) : (Fin 3 → U) →* PSL(4,F) :=
  ((QuotientGroup.mk' _).comp (Matrix.PSL4.OddSplitTorus.torusFourHom F)).comp
    {toFun := fun a i => (a i).val, map_one' := rfl, map_mul' := fun _ _ => rfl}

def torus (U : Subgroup Fˣ) : Subgroup PSL(4,F) := (torusHom U).range

theorem cycle_cube : (cycle (F := F)) ^ 3 = 1 := by
  rw [cycle, ← map_pow]
  have h : (cycleSL (F := F)) ^ 3 = 1 := by
    apply Subtype.ext
    simp only [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [h, map_one]

theorem cycle_torus (U : Subgroup Fˣ) (a : Fin 3 → U) :
    cycle * torusHom U a * cycle⁻¹ = torusHom U ![a 1,a 2,a 0] := by
  change QuotientGroup.mk' _ (cycleSL (F := F)) *
    QuotientGroup.mk' _ (Matrix.PSL4.OddSplitTorus.torusFour F (fun i => (a i).val)) *
    (QuotientGroup.mk' _ (cycleSL (F := F)))⁻¹ =
    QuotientGroup.mk' _ (Matrix.PSL4.OddSplitTorus.torusFour F
      (fun i => (![a 1,a 2,a 0] i).val))
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change (cycleSL (F := F) : Matrix (Fin 4) (Fin 4) F) *
      diagonal ![((a 0).val : F), ((a 1).val : F), ((a 2).val : F),
        ↑((a 0).val * (a 1).val * (a 2).val)⁻¹] =
    diagonal ![((a 1).val : F), ((a 2).val : F), ((a 0).val : F),
        ↑((a 1).val * (a 2).val * (a 0).val)⁻¹] *
      (cycleSL (F := F) : Matrix (Fin 4) (Fin 4) F)
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [cycleSL, mul_comm, mul_assoc]

theorem torusHom_injective (U : Subgroup Fˣ) [Finite U] (ho : Odd (Nat.card U)) :
    Function.Injective (torusHom U) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hh : QuotientGroup.mk' _
      (Matrix.PSL4.OddSplitTorus.torusFour F (fun i => (a i).val)) = 1 := ha
  obtain ⟨v,hv,he⟩ := SpecialLinearGroup.mem_center_iff.mp
    ((QuotientGroup.eq_one_iff _).mp hh)
  have hcoord (i : Fin 3) : v = ((a i).val : F) := by
    have h := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m i.castSucc i.castSucc) he
    fin_cases i <;> exact h
  have hfour : (a 0) ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one, Fintype.card_fin, hcoord 0] using hv
  have hone : a 0 = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (show (Nat.card U).Coprime 4 from ho.coprime_two_right.pow_right 2)
    (orderOf_dvd_natCard _) (orderOf_dvd_of_pow_eq_one hfour))
  have hvone : v = 1 := (hcoord 0).trans (congrArg (fun u : U => (u.val : F)) hone)
  funext i
  apply Subtype.ext
  apply Units.ext
  exact (hcoord i).symm.trans hvone

theorem cycle_normalizes (U : Subgroup Fˣ) :
    cycle (F := F) ∈ normalizer (torus U : Set PSL(4,F)) := by
  apply mem_normalizer_iff.mpr
  intro t
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨![a 1,a 2,a 0], (cycle_torus U a).symm⟩
  · rintro ⟨a,ha⟩
    refine ⟨![a 2,a 0,a 1], ?_⟩
    apply (MulAut.conj (cycle (F := F))).injective
    change cycle * torusHom U ![a 2,a 0,a 1] * cycle⁻¹ = cycle * t * cycle⁻¹
    rw [cycle_torus, ← ha]
    congr 1
    ext i
    fin_cases i <;> rfl

/-- The cubic orbit norm surjects onto the fixed part of the odd split torus.
The fourth diagonal entry is the inverse product, so the fixed torus has one
free parameter and its norm preimage is `(a,1,1)`. -/
theorem exists_norm_of_commute (U : Subgroup Fˣ) [Finite U] (ho : Odd (Nat.card U))
    (t : PSL(4,F)) (ht : t ∈ torus U) (hc : Commute t cycle) :
    ∃ u ∈ torus U, t = u * (cycle*u*cycle⁻¹) * (cycle^2*u*(cycle^2)⁻¹) := by
  obtain ⟨a,rfl⟩ := ht
  have hr : ![a 1,a 2,a 0] = a := torusHom_injective U ho (by
    rw [← cycle_torus, hc.symm.eq, mul_inv_cancel_right])
  have h10 : a 1 = a 0 := congrFun hr 0
  have h21 : a 2 = a 1 := congrFun hr 1
  have h2 (b : Fin 3 → U) : cycle^2 * torusHom U b * (cycle^2)⁻¹ =
      torusHom U ![b 2,b 0,b 1] := by
    calc
      _ = cycle * (cycle * torusHom U b * cycle⁻¹) * cycle⁻¹ := by rw [pow_two]; group
      _ = _ := by rw [cycle_torus, cycle_torus]; rfl
  refine ⟨torusHom U ![a 0,1,1], ⟨![a 0,1,1],rfl⟩, ?_⟩
  rw [cycle_torus, h2, ← map_mul, ← map_mul]
  congr 1
  ext i
  fin_cases i <;> simp [h21, h10]

/-- The projective odd torus retains all three independent parameters. -/
theorem card_torus (U : Subgroup Fˣ) [Finite U] (ho : Odd (Nat.card U)) :
    Nat.card (torus U) = Nat.card U ^ 3 := by
  rw [torus, ← Nat.card_congr (MonoidHom.ofInjective (torusHom_injective U ho)).toEquiv,
    Nat.card_fun, Nat.card_fin]

open scoped IsMulCommutative in
/-- The actual split-torus norm discharges the norm premise of central transfer.
Abelianity of the full torus preimage and the local index remain geometric
inputs; no multiplier formula or natural-cover lift is assumed. -/
theorem not_dvd_kernel_of_abelian_preimage_of_index [Finite F]
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E PSL(4,F)) {r : ℕ} [Fact r.Prime]
    (U : Subgroup Fˣ) (ho : Odd (Nat.card U))
    (hT : IsMulCommutative ((torus U).comap f.toMonoidHom))
    (hi : ¬ r ∣ (torus U ⊔ zpowers (cycle (F := F))).index) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker :=
  f.not_dvd_card_kernel_of_cubic_norm (torus U) cycle (cycle_normalizes U) hT
    cycle_cube (exists_norm_of_commute U ho) hi

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearQuadratic
