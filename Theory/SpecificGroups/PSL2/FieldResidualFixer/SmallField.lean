module

public import Theory.GroupAction.FixedResidualFixerTransport
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index

/-!
# The small-field residual fixer

The matrix [[0,1],[1,1]] has order dividing three and is fixed by every
coefficient automorphism. Its image therefore belongs to the actual embedded
two-residual of the fixed group. Direct matrix multiplication shows that its
centralizer has no involutions, hence has odd order. The inner part of the full
pointwise fixer is an image of this odd centralizer. Semilinear coverage bounds
the outer quotient by the field automorphism group, of order two when the
field has four elements. Consequently four cannot divide the fixer order.

This treats the PSL₂(4) endpoint without asserting that its fixed PSL₂(2) is
perfect: the latter's residual is a proper cubic subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(4) and the inspection in 16.4.9(1), printed pp.1171 and 1189.
-/

public section
open Subgroup Matrix BenderSuzuki.MatrixGroups BenderSuzuki.ZD.Linear
namespace Theory.PSL2.FieldResidualFixer
variable {F : Type*} [Field F] [CharP F 2]

private def cubic : SpecialLinearGroup (Fin 2) F := ⟨!![0,1;1,1], by simp [CharTwo.neg_eq]⟩

private theorem cubic_pow : (cubic (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  change (!![0,1;1,1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

private theorem cubic_fixed (σ : F ≃+* F) :
    BenderSuzuki.Converse.pi F (cubic (F := F)) ∈ (BenderSuzuki.ZD.Linear.fieldAut σ).fixedSubgroup := by
  rw [MulAut.mem_fixedSubgroup, fieldAut_apply_pi]
  congr 1
  ext i j
  change σ ((cubic (F := F)).val i j) = (cubic (F := F)).val i j
  fin_cases i <;> fin_cases j <;> simp [cubic]

private theorem cubic_mem_residual (σ : F ≃+* F) :
    BenderSuzuki.Converse.pi F (cubic (F := F)) ∈
      MulAut.embeddedFixedResidual 2 (BenderSuzuki.ZD.Linear.fieldAut σ) := by
  let c : (BenderSuzuki.ZD.Linear.fieldAut σ).fixedSubgroup := ⟨_, cubic_fixed σ⟩
  have hc : c ^ 3 = 1 := by
    apply Subtype.ext
    change (BenderSuzuki.Converse.pi F (cubic (F := F))) ^ 3 = 1
    rw [← map_pow, cubic_pow, map_one]
  exact ⟨c, mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hc)), rfl⟩

private theorem cubic_centralizer_sq (g : SpecialLinearGroup (Fin 2) F)
    (h : g * cubic = cubic * g) (h2 : g ^ 2 = 1) : g = 1 := by
  have h00 := congrArg (fun x : SpecialLinearGroup (Fin 2) F => x.val 0 0) h
  have h01 := congrArg (fun x : SpecialLinearGroup (Fin 2) F => x.val 0 1) h
  change ((g : Matrix (Fin 2) (Fin 2) F) * (cubic (F := F) : Matrix (Fin 2) (Fin 2) F)) 0 0 = ((cubic (F := F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) 0 0 at h00
  change ((g : Matrix (Fin 2) (Fin 2) F) * (cubic (F := F) : Matrix (Fin 2) (Fin 2) F)) 0 1 = ((cubic (F := F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) 0 1 at h01
  have hb : g.val 1 0 = g.val 0 1 := by
    simpa [cubic, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using h00.symm
  have hd : g.val 1 1 = g.val 0 0 + g.val 0 1 := by
    simpa [cubic, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using h01.symm
  have hh := congrArg (fun x : SpecialLinearGroup (Fin 2) F => x.val 0 1) h2
  have hb0 : g.val 0 1 = 0 := by
    have he : g.val 0 1 * g.val 0 1 = 0 := by
      simpa [pow_two, SpecialLinearGroup.coe_pow, Matrix.mul_apply, Fin.sum_univ_two, hd, mul_add,
        ← add_assoc, mul_comm, CharTwo.add_self_eq_zero] using hh
    exact (mul_self_eq_zero.mp he)
  have ha : g.val 0 0 = 1 := by
    apply CharTwo.sq_injective
    simpa only [Matrix.det_fin_two, hb, hd, hb0, pow_two, add_zero, mul_zero, sub_zero, one_mul] using g.property
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb, hd, hb0, ha]

private theorem residual_centralizer_odd [Finite F] (σ : F ≃+* F) :
    Odd (Nat.card (centralizer (MulAut.embeddedFixedResidual 2
      (BenderSuzuki.ZD.Linear.fieldAut σ) : Set (PSL2MatrixGroup F)))) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro hdiv
  let C := centralizer (MulAut.embeddedFixedResidual 2
    (BenderSuzuki.ZD.Linear.fieldAut σ) : Set (PSL2MatrixGroup F))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hdiv
  have hx2 : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  obtain ⟨g, hg⟩ := BenderSuzuki.Converse.pi_surjective (x : PSL2MatrixGroup F)
  have hg2 : g ^ 2 = 1 := BenderSuzuki.Converse.pi_injective (by
    simpa only [map_pow, hg, Subgroup.coe_pow, Subgroup.coe_one, map_one] using congrArg Subtype.val hx2)
  have hgc : g * cubic = cubic * g := BenderSuzuki.Converse.pi_injective (by
    have hh := x.property _ (cubic_mem_residual σ)
    simpa only [map_mul, hg] using hh.symm)
  have hx1 : x = 1 := Subtype.ext (by
    rw [cubic_centralizer_sq g hgc hg2, map_one] at hg
    exact hg.symm)
  simp only [hx1, orderOf_one] at hx
  omega

private noncomputable def fieldActionHom :
    (F ≃+* F) →* MulAut (PSL2MatrixGroup F) where
  toFun := BenderSuzuki.ZD.Linear.fieldAut
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := BenderSuzuki.Converse.pi_surjective x
    rw [fieldAut_apply_pi]
    rfl
  map_mul' σ τ := by
    ext x
    obtain ⟨y, rfl⟩ := BenderSuzuki.Converse.pi_surjective x
    change BenderSuzuki.ZD.Linear.fieldAut (σ * τ) (BenderSuzuki.Converse.pi F y) =
      BenderSuzuki.ZD.Linear.fieldAut σ
        (BenderSuzuki.ZD.Linear.fieldAut τ (BenderSuzuki.Converse.pi F y))
    rw [fieldAut_apply_pi, fieldAut_apply_pi, fieldAut_apply_pi]
    rfl

private theorem outer_index_dvd_two [Finite F] (hF : Nat.card F = 4) :
    (MulAut.innerSubgroup (PSL2MatrixGroup F)).index ∣ 2 := by
  let B := PSL2MatrixGroup F
  let I := MulAut.innerSubgroup B
  let q := QuotientGroup.mk' I
  let f := q.comp (fieldActionHom (F := F))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective I x
    obtain ⟨g, σ, rfl⟩ := semilinear_coverage a
    refine ⟨σ, ?_⟩
    have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    change q (BenderSuzuki.ZD.Linear.fieldAut σ) =
      q (MulAut.conj g * BenderSuzuki.ZD.Linear.fieldAut σ)
    rw [map_mul, hg, one_mul]
  change Nat.card (MulAut B ⧸ I) ∣ 2
  have hc : Nat.card (F ≃+* F) = 2 :=
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card F = 2 ^ 2 by simpa using hF)
  exact (card_dvd_of_surjective f hf).trans (dvd_of_eq hc)

private theorem fixer_card_dvd {G : Type*} [_root_.Group G] [Finite G] (P : Subgroup G) :
    Nat.card (fixingSubgroup (MulAut G) (P : Set G)) ∣
      Nat.card (centralizer (P : Set G)) * (MulAut.innerSubgroup G).index := by
  let A := fixingSubgroup (MulAut G) (P : Set G)
  let I := (MulAut.innerSubgroup G).subgroupOf A
  let C := centralizer (P : Set G)
  have hf (x : C) : MulAut.conj (x : G) ∈ A := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    change (x : G) * y * (x : G)⁻¹ = y
    rw [← x.property y hy, mul_inv_cancel_right]
  let f : C →* I :=
    { toFun := fun x => ⟨⟨MulAut.conj (x : G), hf x⟩, ⟨x, rfl⟩⟩
      map_one' := Subtype.ext (Subtype.ext (map_one MulAut.conj))
      map_mul' x y := Subtype.ext (Subtype.ext (map_mul MulAut.conj x.val y.val)) }
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨x, hx⟩ := a.property
    change MulAut.conj x = (a.val : MulAut G) at hx
    have hc : x ∈ C := by
      intro y hy
      have he := (mem_fixingSubgroup_iff (MulAut G)).mp a.val.property y hy
      rw [← hx] at he
      change x * y * x⁻¹ = y at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    exact ⟨⟨x, hc⟩, Subtype.ext (Subtype.ext hx)⟩
  have hc : Nat.card I ∣ Nat.card C := card_dvd_of_surjective f hs
  have hi : I.index ∣ (MulAut.innerSubgroup G).index :=
    relIndex_dvd_index_of_normal (MulAut.innerSubgroup G) A
  calc
    Nat.card A = Nat.card I * I.index := I.card_mul_index.symm
    _ ∣ Nat.card C * (MulAut.innerSubgroup G).index := Nat.mul_dvd_mul hc hi

/-- The full automorphism fixer of the actual embedded residual has two-part at most two. -/
theorem four_not_dvd_fixer_of_card_four [Finite F] (hF : Nat.card F = 4)
    (σ : F ≃+* F) :
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut (PSL2MatrixGroup F))
      (MulAut.embeddedFixedResidual 2 (BenderSuzuki.ZD.Linear.fieldAut σ) :
        Set (PSL2MatrixGroup F))) := by
  intro hfour
  have hdiv := hfour.trans (fixer_card_dvd
    (MulAut.embeddedFixedResidual 2 (BenderSuzuki.ZD.Linear.fieldAut σ)))
  have hcop : Nat.Coprime 4 (Nat.card (centralizer
      (MulAut.embeddedFixedResidual 2 (BenderSuzuki.ZD.Linear.fieldAut σ) :
        Set (PSL2MatrixGroup F)))) := by
    exact (Nat.coprime_two_left.mpr (residual_centralizer_odd σ)).pow_left 2
  have hbad := (hcop.dvd_of_dvd_mul_left hdiv).trans (outer_index_dvd_two hF)
  norm_num at hbad

end Theory.PSL2.FieldResidualFixer
