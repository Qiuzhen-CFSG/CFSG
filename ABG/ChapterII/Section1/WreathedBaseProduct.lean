module
public import ABG.ChapterII.Section1.WreathedNormalForm
public import ABG.ChapterII.Section1.WreathedBase

/-!
# Product coordinates of the wreathed base

The base subgroup in ABG Chapter II §1 Lemma 2(ii), article pp.9–10, has type
`(2^n, 2^n)`. Evaluating a pair of residues as `s^i*t^j` gives a homomorphism
from the product of two cyclic groups: the generator commutation relation
collects powers, and their periods make evaluation independent of reduction.
The base membership theorem proves surjectivity and unique normal form proves
injectivity. Inverting this homomorphism gives the coordinate equivalence.

The public coordinate formulas identify the projection kernels with the cyclic
generator subgroups, supporting the invariant-subgroup argument. Cardinality
and index follow from the product and the presentation's prescribed group order;
they supply the independent maximality and uniqueness argument for the base.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private def baseEval :
    (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) →* P.U where
  toFun v := ⟨P.s ^ v.1.toAdd.val * P.t ^ v.2.toAdd.val,
    (P.mem_U_iff _).mpr ⟨v.1.toAdd.val, v.2.toAdd.val, by simp only [zpow_natCast]⟩⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' v w := by
    apply Subtype.ext
    change P.s ^ (v.1.toAdd + w.1.toAdd).val * P.t ^ (v.2.toAdd + w.2.toAdd).val = _
    rw [ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ P.s_pow,
      ← pow_eq_pow_mod _ P.t_pow, pow_add, pow_add]
    have hc : Commute P.s P.t := P.commute
    calc
      _ = P.s ^ v.1.toAdd.val * (P.s ^ w.1.toAdd.val * P.t ^ v.2.toAdd.val) *
          P.t ^ w.2.toAdd.val := by group
      _ = _ := by rw [(hc.pow_pow w.1.toAdd.val v.2.toAdd.val).eq]; simp [mul_assoc]

private theorem baseEval_zpow (i j : ℤ) :
    (P.baseEval (Multiplicative.ofAdd (i : ZMod (2 ^ n)),
      Multiplicative.ofAdd (j : ZMod (2 ^ n))) : S) = P.s ^ i * P.t ^ j := by
  change P.s ^ (i : ZMod (2 ^ n)).val * P.t ^ (j : ZMod (2 ^ n)).val = _
  rw [← zpow_natCast, ← zpow_natCast, ZMod.val_intCast, ZMod.val_intCast,
    ← zpow_eq_zpow_emod' i P.s_pow, ← zpow_eq_zpow_emod' j P.t_pow]

private theorem baseEval_bijective : Function.Bijective P.baseEval := by
  constructor
  · intro v w h
    have h' : P.normalForm
        (⟨v.1.toAdd.val, ZMod.val_lt _⟩, ⟨v.2.toAdd.val, ZMod.val_lt _⟩, 0) =
        P.normalForm
        (⟨w.1.toAdd.val, ZMod.val_lt _⟩, ⟨w.2.toAdd.val, ZMod.val_lt _⟩, 0) := by
      simpa [normalForm, baseEval] using congrArg Subtype.val h
    have he := P.normal_form_injective h'
    have h₁ : v.1.toAdd.val = w.1.toAdd.val := congrArg (fun x => x.1.val) he
    have h₂ : v.2.toAdd.val = w.2.toAdd.val := congrArg (fun x => x.2.1.val) he
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      exact ZMod.val_injective _ h₁
    · apply Multiplicative.toAdd.injective
      exact ZMod.val_injective _ h₂
  · intro g
    rcases (P.mem_U_iff g).mp g.property with ⟨i, j, h⟩
    exact ⟨(Multiplicative.ofAdd (i : ZMod (2 ^ n)),
      Multiplicative.ofAdd (j : ZMod (2 ^ n))), Subtype.ext ((P.baseEval_zpow i j).trans h)⟩

public noncomputable def baseEquiv : P.U ≃*
    (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) :=
  (MulEquiv.ofBijective P.baseEval P.baseEval_bijective).symm

public theorem baseEquiv_symm_apply
    (v : Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) :
    (P.baseEquiv.symm v : S) = P.s ^ v.1.toAdd.val * P.t ^ v.2.toAdd.val := by rfl

public theorem baseEquiv_apply_zpow (i j : ℤ) :
    P.baseEquiv ⟨P.s ^ i * P.t ^ j, (P.mem_U_iff _).mpr ⟨i, j, rfl⟩⟩ =
      (Multiplicative.ofAdd (i : ZMod (2 ^ n)), Multiplicative.ofAdd (j : ZMod (2 ^ n))) := by
  apply P.baseEquiv.symm.injective
  simpa only [MulEquiv.symm_apply_apply] using (Subtype.ext (P.baseEval_zpow i j)).symm

public theorem baseEquiv_apply_eq (g : P.U) (i j : ℤ)
    (h : P.s ^ i * P.t ^ j = (g : S)) :
    P.baseEquiv g =
      (Multiplicative.ofAdd (i : ZMod (2 ^ n)), Multiplicative.ofAdd (j : ZMod (2 ^ n))) := by
  have he : (⟨P.s ^ i * P.t ^ j, (P.mem_U_iff _).mpr ⟨i, j, rfl⟩⟩ : P.U) = g :=
    Subtype.ext h
  rw [← he]
  exact P.baseEquiv_apply_zpow i j

public theorem baseEquiv_fst_eq_one_iff (g : P.U) :
    (P.baseEquiv g).1 = 1 ↔ (g : S) ∈ Subgroup.zpowers P.t := by
  constructor
  · intro h
    have he := P.baseEquiv_symm_apply (P.baseEquiv g)
    rw [MulEquiv.symm_apply_apply, h] at he
    simp only [toAdd_one, ZMod.val_zero, pow_zero, one_mul] at he
    rw [he]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · intro h
    rcases Subgroup.mem_zpowers_iff.mp h with ⟨i, hi⟩
    have he := P.baseEquiv_apply_eq g 0 i (by simpa using hi)
    simp only [he, Int.cast_zero, ofAdd_zero]

public theorem baseEquiv_snd_eq_one_iff (g : P.U) :
    (P.baseEquiv g).2 = 1 ↔ (g : S) ∈ Subgroup.zpowers P.s := by
  constructor
  · intro h
    have he := P.baseEquiv_symm_apply (P.baseEquiv g)
    rw [MulEquiv.symm_apply_apply, h] at he
    simp only [toAdd_one, ZMod.val_zero, pow_zero, mul_one] at he
    rw [he]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · intro h
    rcases Subgroup.mem_zpowers_iff.mp h with ⟨i, hi⟩
    have he := P.baseEquiv_apply_eq g i 0 (by simpa using hi)
    simp only [he, Int.cast_zero, ofAdd_zero]

public theorem card_U : Nat.card P.U = 2 ^ (2 * n) := by
  rw [Nat.card_congr P.baseEquiv.toEquiv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_multiplicative, ZMod.card]
  rw [Nat.mul_comm 2 n, pow_mul]
  ring

public theorem index_U : P.U.index = 2 := by
  have h := P.U.card_mul_index
  rw [P.card_U, P.card, pow_add] at h
  have hp : 0 < 2 ^ (2 * n) := by positivity
  simp only [pow_one] at h
  exact Nat.eq_of_mul_eq_mul_left hp h

end ABG.Wreathed.Presentation
