module

public import Theory.Representation.BinaryOffender.Basic
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Two

/-!
# Offenders inside the natural SL₂ layer

A nonidentity matrix has at most `|F|` fixed vectors. Thus the binary offender
inequality on `F²` forces an internal offender to have order at least `|F|`.
The upper-unipotent Sylow construction supplies the reverse inequality and
proves Sylow maximality, without a formula for the order of SL₂.

We also show that an involutory element acting linearly over `F` lies in the
natural SL₂ layer of a faithful ambient action. Together these results reduce
recognition of arbitrary offenders to excluding a nontrivial field action.

Source: the natural-module case of Aschbacher--Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), B.4.2(1), printed p.86.
The internal result does not assert containment for arbitrary ambient offenders.
-/

public section

namespace Representation.SL2NaturalOffenders
open Representation.BinaryOffender
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group H] [Finite H]

omit [Algebra (ZMod 2) F] in
/-- A nonidentity two by two matrix has at most one field line of fixed vectors. -/
theorem fixedVectors_card_le (M : Matrix (Fin 2) (Fin 2) F) (hM : M ≠ 1) :
    Nat.card {v : Fin 2 → F // M.mulVec v = v} ≤ Nat.card F := by
  have he : ∃ i, M i 0 - (1 : Matrix (Fin 2) (Fin 2) F) i 0 ≠ 0 ∨
      M i 1 - (1 : Matrix (Fin 2) (Fin 2) F) i 1 ≠ 0 := by
    by_contra! h
    apply hM
    ext i j
    fin_cases j
    · exact sub_eq_zero.mp (h i).1
    · exact sub_eq_zero.mp (h i).2
  obtain ⟨i, hi⟩ := he
  have equation (v : {v : Fin 2 → F // M.mulVec v = v}) :
      (M i 0 - (1 : Matrix (Fin 2) (Fin 2) F) i 0) * v.val 0 +
      (M i 1 - (1 : Matrix (Fin 2) (Fin 2) F) i 1) * v.val 1 = 0 := by
    have h := congrFun v.property i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] at h ⊢ <;>
      linear_combination h
  rcases hi with hi | hi
  · apply Nat.card_le_card_of_injective (fun v : {v : Fin 2 → F // M.mulVec v = v} => v.val 1)
    intro v w h
    change v.val 1 = w.val 1 at h
    have h0 : v.val 0 = w.val 0 := by
      apply mul_left_cancel₀ hi
      have hv := equation v
      have hw := equation w
      rw [h] at hv
      linear_combination hv - hw
    apply Subtype.ext
    ext j
    fin_cases j <;> assumption
  · apply Nat.card_le_card_of_injective (fun v : {v : Fin 2 → F // M.mulVec v = v} => v.val 0)
    intro v w h
    change v.val 0 = w.val 0 at h
    have h1 : v.val 1 = w.val 1 := by
      apply mul_left_cancel₀ hi
      have hv := equation v
      have hw := equation w
      rw [h] at hv
      linear_combination hv - hw
    apply Subtype.ext
    ext j
    fin_cases j <;> assumption

omit [Finite H] in
/-- A nontrivial subgroup of the natural SL₂ layer fixes at most `|F|` vectors. -/
theorem fixedSpace_card_le_of_le (L : Subgroup H)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    {A : Subgroup H} (hne : A ≠ ⊥) (hAL : A ≤ L) :
    Nat.card (fixedSpace ρ A) ≤ Nat.card F := by
  obtain ⟨⟨a, ha⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let g : L := ⟨a, hAL ha⟩
  have hM : (e g).val ≠ 1 := by
    intro he
    have heg : e g = 1 := Subtype.ext he
    have hg : g = 1 := e.injective (heg.trans e.map_one.symm)
    exact hne (Subtype.ext (congrArg (fun x : L => (x : H)) hg))
  let f : fixedSpace ρ A → {v : Fin 2 → F // (e g).val.mulVec v = v} :=
    fun v => ⟨v.val, (hnat g v.val).symm.trans (v.property ⟨a, ha⟩)⟩
  exact (Nat.card_le_card_of_injective f (fun v w h =>
    Subtype.ext (congrArg
      (fun x : {v : Fin 2 → F // (e g).val.mulVec v = v} => x.val) h))).trans
        (fixedVectors_card_le (e g).val hM)

/-- The offender dimension inequality, written in cardinalities. -/
theorem card_sq_le_card_mul_fixedSpace (ρ : Representation (ZMod 2) H (Fin 2 → F))
    {A : Subgroup H} (hA : IsOffender ρ A) :
    Nat.card F * Nat.card F ≤ Nat.card A * Nat.card (fixedSpace ρ A) := by
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
    ((fixedCodim_le_rank_iff ρ A).mp hA.2)
  have hcV : Nat.card (Fin 2 → F) = 2 ^ Module.finrank (ZMod 2) (Fin 2 → F) := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fin 2 → F))
  have hcW : Nat.card (fixedSpace ρ A) = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A))
  rw [weight, pow_add, ← hA.1.card_eq_two_pow_rank,
    ← hcW, ← hcV] at hpow
  simpa [Nat.card_fun, pow_two] using hpow

/-- Every Sylow two-subgroup of the natural SL₂ layer has the field's order. -/
theorem sylow_card (L : Subgroup H)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) (P : Sylow 2 L) :
    Nat.card P = Nat.card F := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  calc
    Nat.card P = Nat.card Q := Nat.card_congr
      ((P : Subgroup L).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    _ = Nat.card (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2) :=
      Nat.card_congr (Q.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)).toEquiv
    _ = Nat.card F := Matrix.SpecialLinearGroup.card_upperUnipotent F

/-- An offender contained in the natural SL₂ layer fills a Sylow two-subgroup. -/
theorem exists_sylow_of_le (L : Subgroup H)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    {A : Subgroup H} (hA : IsOffender ρ A) (hAL : A ≤ L) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = A := by
  let : IsElementaryAbelian 2 A := hA.1.2
  have hPG : IsPGroup 2 (A.subgroupOf L) := (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  obtain ⟨P, hP⟩ := hPG.exists_le_sylow
  have hAF : Nat.card F ≤ Nat.card A := by
    have h := (card_sq_le_card_mul_fixedSpace ρ hA).trans
      (Nat.mul_le_mul_left (Nat.card A) (fixedSpace_card_le_of_le L e ρ hnat hA.1.1 hAL))
    exact Nat.le_of_mul_le_mul_right h (Nat.card_pos (α := F))
  have heq : A.subgroupOf L = (P : Subgroup L) :=
    Subgroup.eq_of_le_of_card_ge hP (by
      rw [sylow_card L e P]
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv])
  exact ⟨P, heq ▸ Subgroup.map_subgroupOf_eq_of_le hAL⟩
end Representation.SL2NaturalOffenders


namespace Representation.SL2NaturalOffenders
open Matrix.SpecialLinearGroup
variable {F H : Type*} [Field F] [Algebra (ZMod 2) F] [Group H]

/-- An involutory element acting linearly over the matrix field belongs to the
natural SL₂ layer: its determinant squares to one, hence is one in characteristic two. -/
theorem mem_of_linear_square_one (L : Subgroup H)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    {a : H} (ha : a ^ 2 = 1)
    (hlin : ∀ (c : F) (v : Fin 2 → F), ρ a (c • v) = c • ρ a v) : a ∈ L := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let T : Module.End F (Fin 2 → F) :=
    { toFun := ρ a
      map_add' := (ρ a).map_add
      map_smul' := hlin }
  have hT : T * T = 1 := by
    apply LinearMap.ext
    intro v
    change ρ a (ρ a v) = v
    simpa only [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
      using LinearMap.congr_fun (congrArg ρ ha) v
  let M := LinearMap.toMatrix' T
  have hM : M * M = 1 := by
    rw [← LinearMap.toMatrix'_mul, hT, LinearMap.toMatrix'_one]
  have hdet : M.det = 1 := by
    have hsq : M.det ^ 2 = 1 := by
      simpa [Matrix.det_mul, pow_two] using congrArg Matrix.det hM
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  let g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨M, hdet⟩
  have heq : ρ ((e.symm g : L) : H) = ρ a := by
    apply LinearMap.ext
    intro v
    rw [hnat, e.apply_symm_apply]
    exact LinearMap.toMatrix'_mulVec T v
  have haeq := hfaith heq
  exact haeq ▸ (e.symm g).property
end Representation.SL2NaturalOffenders
