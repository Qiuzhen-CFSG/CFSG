module
public import Theory.Representation.G2NaturalOffenders.Short
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Exclusion of pure long-root offenders

A nonzero long-root element has fixed codimension twice the binary field
degree. An offender in the long-root plane must therefore have the full
order of that plane. The plane itself fixes only the upper three-space,
whose codimension is larger than its binary rank. Hence no such offender
exists. Together with the common-conjugator fusion theorem, this excludes
the pure-long branch of Aschbacher–Smith B.4.6(13), printed pp.88–90.
-/

@[expose] public noncomputable section
namespace Atlas.G2.NaturalOffenders
open Representation Representation.BinaryOffender Subgroup
open Restricted.NaturalCoordinates
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

def upperFour : Submodule F (Fin 6 → F) where
  carrier := {v | v 4 = 0 ∧ v 5 = 0}
  zero_mem' := by simp
  add_mem' := by rintro v w ⟨h4,h5⟩ ⟨k4,k5⟩; simp_all
  smul_mem' := by rintro c v ⟨h4,h5⟩; simp_all

def upperFourEquiv : upperFour (F:=F) ≃ₗ[F] (Fin 4 → F) where
  toFun v := ![v.val 0,v.val 1,v.val 2,v.val 3]
  invFun v := ⟨![v 0,v 1,v 2,v 3,0,0], by simp [upperFour]⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [v.prop.1,v.prop.2]
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

omit [Algebra (ZMod 2) F] in
theorem fixed_rootA_iff (a : F) (ha : a ≠ 0) (v : Fin 6 → F) :
    action F (rootA a) v = v ↔ v ∈ upperFour := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [action_rootA, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨(mul_eq_zero.mp (add_eq_left.mp h0)).resolve_left ha,
      (mul_eq_zero.mp (add_eq_left.mp h1)).resolve_left ha⟩
  · rintro ⟨h4,h5⟩
    ext i
    fin_cases i <;> simp [h4,h5]

theorem fixedSpace_rootA (a : F) (ha : a ≠ 0) :
    fixedSpace (binaryAction (F:=F)) (zpowers (rootA a)) =
      (upperFour (F:=F)).restrictScalars (ZMod 2) := by
  ext v
  rw [mem_fixedSpace_zpowers_iff]
  exact fixed_rootA_iff a ha v

variable [Finite F]

omit [CharP F 2] in
theorem upperFour_binary_finrank {n : ℕ} (hc : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) ((upperFour (F:=F)).restrictScalars (ZMod 2)) = 4*n := by
  change Module.finrank (ZMod 2) (upperFour (F:=F)) = _
  rw [((upperFourEquiv (F:=F)).restrictScalars (ZMod 2)).finrank_eq]
  simp [Module.finrank_pi_fintype,finrank_binary_field hc]

theorem fixedCodim_rootA {n : ℕ} (hc : Nat.card F = 2^n) (a : F) (ha : a ≠ 0) :
    fixedCodim (binaryAction (F:=F)) (zpowers (rootA a)) = 2*n := by
  have h := fixedCodim_add_finrank (binaryAction (F:=F)) (zpowers (rootA a))
  rw [fixedSpace_rootA a ha,upperFour_binary_finrank hc,coordinates_binary_finrank hc] at h
  omega

theorem fixedCodim_longRoot {n : ℕ} (hc : Nat.card F = 2^n) {b : Model F}
    (hb : ShortRootProducts.IsLongRootElement b) :
    fixedCodim (binaryAction (F:=F)) (zpowers b) = 2*n := by
  obtain ⟨a,ha,g,rfl⟩ := hb
  change fixedCodim (binaryAction (F:=F)) (zpowers ((MulAut.conj g).toMonoidHom (rootA a))) = _
  rw [← MonoidHom.map_zpowers, fixedCodim_map_conj]
  exact fixedCodim_rootA hc a ha

private theorem codim_mono {A B : Subgroup (Model F)} (hAB : A ≤ B) :
    fixedCodim (binaryAction (F:=F)) A ≤ fixedCodim (binaryAction (F:=F)) B := by
  have hf : fixedSpace (binaryAction (F:=F)) B ≤ fixedSpace (binaryAction (F:=F)) A := by
    intro v hv a
    exact hv ⟨a,hAB a.prop⟩
  have hd := Submodule.finrank_mono hf
  have ha := fixedCodim_add_finrank (binaryAction (F:=F)) A
  have hb := fixedCodim_add_finrank (binaryAction (F:=F)) B
  omega

theorem not_offender_of_le_longRootLocal {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n)
    (B : Subgroup (Model F)) (hle : B ≤ longRootLocal) :
    ¬ IsOffender (binaryAction (F:=F)) B := by
  intro hB
  obtain ⟨b,hb,hne⟩ := B.bot_or_exists_ne_one.resolve_left hB.1.1
  have hlo := ShortRootProducts.longRootLocal_isLong (hle hb) hne
  have hd := codim_mono (zpowers_le.mpr hb)
  rw [fixedCodim_longRoot hc hlo] at hd
  have hcB := Subgroup.card_le_of_le hle
  rw [card_longRootLocal,hc,← pow_mul] at hcB
  have hr : rank B ≤ 2*n := by
    have hh := Nat.log_mono_right (b:=2) hcB
    simpa only [rank,Nat.log_pow (by decide : 1<2),Nat.mul_comm n 2] using hh
  have hcost := hB.2
  have heq : rank B = 2*n := by omega
  have hEq : B = longRootLocal := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_longRootLocal,hc,hB.1.card_eq_two_pow_rank,heq,← pow_mul,Nat.mul_comm n 2]
  rw [hEq,fixedCodim_longRootLocal hc] at hcost
  have hr' : rank (longRootLocal (F:=F)) = 2*n := hEq ▸ heq
  omega

end Atlas.G2.NaturalOffenders
