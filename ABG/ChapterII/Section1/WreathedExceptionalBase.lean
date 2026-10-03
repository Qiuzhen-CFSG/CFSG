module
public import ABG.ChapterII.Section1.WreathedCentralExtensionDefs
public import ABG.ChapterII.Section1.WreathedBaseFour
public import ABG.ChapterII.Section1.WreathedCenter

/-!
# The common base of the small wreathed central extensions

For the chosen wreathed presentation of height `n ≥ 2`, the subgroup generated
by the ambient center and `x₂` is normal, lies in the abelian base `U`, and
has type `(2^n, 2)`. These coordinates support the analysis of the two small
central extensions in ABG Chapter II §1 Lemma 3 (article p.10).

Adjoining the normal four subgroup `T` to the center gives the same subgroup,
since `x₃ = x₂⁻¹*x`; this proves normality. Evaluation as `u^i*x₂^e` defines
a homomorphism from the product of the two cyclic groups. Supremum membership
gives surjectivity. Unique wreathed normal form recovers `i` from the
`t`-coordinate, and the exact order of `x₂` then recovers `e`, proving
injectivity. The equivalence gives the cardinality and bounded normal form.
All statements concern the actual presentation subgroup `exceptionalBase`.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

public theorem u_mem_exceptionalBase : P.u ∈ P.exceptionalBase :=
  (show Subgroup.center S ≤ P.exceptionalBase from le_sup_left) P.u_mem_center

public theorem x₂_mem_exceptionalBase : P.x₂ ∈ P.exceptionalBase :=
  (show Subgroup.zpowers P.x₂ ≤ P.exceptionalBase from le_sup_right) (Subgroup.mem_zpowers _)

public theorem exceptionalBase_le_U : P.exceptionalBase ≤ P.U := by
  apply sup_le
  · rw [P.center_eq_zpowers]
    exact Subgroup.zpowers_le.mpr (P.U.mul_mem
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
  · exact Subgroup.zpowers_le.mpr (P.U.pow_mem (Subgroup.subset_closure (by simp)) _)

private theorem exceptionalBase_eq_center_sup_T :
    P.exceptionalBase = Subgroup.center S ⊔ P.T := by
  apply le_antisymm
  · apply sup_le le_sup_left
    exact Subgroup.zpowers_le.mpr ((show P.T ≤ _ from le_sup_right)
      (Subgroup.subset_closure (by simp)))
  · apply sup_le le_sup_left
    rw [P.T_eq_closure_pair]
    apply (Subgroup.closure_le _).mpr
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact P.x₂_mem_exceptionalBase
    · change P.x₃ ∈ P.exceptionalBase
      have hx : P.x ∈ P.exceptionalBase :=
        (show Subgroup.center S ≤ P.exceptionalBase from le_sup_left) P.x_mem_center
      have h := P.exceptionalBase.mul_mem
        (P.exceptionalBase.inv_mem P.x₂_mem_exceptionalBase) hx
      simpa only [P.x_eq_x₂_mul_x₃, inv_mul_cancel_left] using h

public theorem exceptionalBase_normal : P.exceptionalBase.Normal := by
  rw [P.exceptionalBase_eq_center_sup_T]
  let := P.T_normal
  infer_instance

public theorem mem_exceptionalBase_iff (g : S) :
    g ∈ P.exceptionalBase ↔ ∃ i e : ℤ, P.u ^ i * P.x₂ ^ e = g := by
  constructor
  · intro hg
    obtain ⟨a,ha,b,hb,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    rw [P.center_eq_zpowers] at ha
    obtain ⟨i,rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨e,rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ⟨i,e,rfl⟩
  · rintro ⟨i,e,rfl⟩
    exact P.exceptionalBase.mul_mem
      (P.exceptionalBase.zpow_mem P.u_mem_exceptionalBase _)
      (P.exceptionalBase.zpow_mem P.x₂_mem_exceptionalBase _)

private theorem u_period : P.u ^ (2 ^ n) = 1 := by
  rw [← P.orderOf_u, pow_orderOf_eq_one]

private def exceptionalBaseEval :
    (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2)) →* P.exceptionalBase where
  toFun v := ⟨P.u ^ v.1.toAdd.val * P.x₂ ^ v.2.toAdd.val,
    P.exceptionalBase.mul_mem (P.exceptionalBase.pow_mem P.u_mem_exceptionalBase _)
      (P.exceptionalBase.pow_mem P.x₂_mem_exceptionalBase _)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' v w := by
    apply Subtype.ext
    change P.u ^ (v.1.toAdd + w.1.toAdd).val * P.x₂ ^ (v.2.toAdd + w.2.toAdd).val = _
    rw [ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ P.u_period,
      ← pow_eq_pow_mod _ P.x₂_sq, pow_add, pow_add]
    have hc : Commute P.u P.x₂ := ((Subgroup.mem_center_iff.mp P.u_mem_center) _).symm
    calc
      _ = P.u ^ v.1.toAdd.val * (P.u ^ w.1.toAdd.val * P.x₂ ^ v.2.toAdd.val) *
          P.x₂ ^ w.2.toAdd.val := by group
      _ = _ := by rw [(hc.pow_pow w.1.toAdd.val v.2.toAdd.val).eq]; simp [mul_assoc]

private theorem exceptionalBaseEval_zpow (i e : ℤ) :
    (P.exceptionalBaseEval (Multiplicative.ofAdd (i : ZMod (2 ^ n)),
      Multiplicative.ofAdd (e : ZMod 2)) : S) = P.u ^ i * P.x₂ ^ e := by
  change P.u ^ (i : ZMod (2 ^ n)).val * P.x₂ ^ (e : ZMod 2).val = _
  rw [← zpow_natCast, ← zpow_natCast, ZMod.val_intCast, ZMod.val_intCast,
    ← zpow_eq_zpow_emod' i P.u_period, ← zpow_eq_zpow_emod' e P.x₂_sq]

private theorem exceptionalBaseEval_bijective : Function.Bijective P.exceptionalBaseEval := by
  constructor
  · intro v w h
    have he : P.u ^ v.1.toAdd.val * P.x₂ ^ v.2.toAdd.val =
        P.u ^ w.1.toAdd.val * P.x₂ ^ w.2.toAdd.val := congrArg Subtype.val h
    have hc : Commute P.s P.t := P.commute
    have form (i e : ℕ) : P.u ^ i * P.x₂ ^ e =
        P.s ^ (i + 2 ^ (n-1) * e) * P.t ^ i := by
      rw [u, x₂, hc.mul_pow, ← pow_mul, pow_add]
      rw [mul_assoc, (hc.pow_pow (2^(n-1)*e) i).symm.eq, ← mul_assoc]
    have hh := (P.normal_form_zpow_eq_iff
      ((v.1.toAdd.val + 2 ^ (n-1) * v.2.toAdd.val : ℕ) : ℤ) v.1.toAdd.val 0
      ((w.1.toAdd.val + 2 ^ (n-1) * w.2.toAdd.val : ℕ) : ℤ) w.1.toAdd.val 0).mp
      (by simpa only [zpow_natCast, zpow_zero, mul_one] using
        ((form _ _).symm.trans he).trans (form _ _))
    have hi : v.1.toAdd.val = w.1.toAdd.val := by
      have hv := ZMod.val_lt v.1.toAdd
      have hw := ZMod.val_lt w.1.toAdd
      have hvi : (v.1.toAdd.val : ℤ) < ((2^n : ℕ) : ℤ) := by exact_mod_cast hv
      have hwi : (w.1.toAdd.val : ℤ) < ((2^n : ℕ) : ℤ) := by exact_mod_cast hw
      have hh' := hh.2.1
      rw [Int.emod_eq_of_lt (by positivity) hvi,
        Int.emod_eq_of_lt (by positivity) hwi] at hh'
      exact_mod_cast hh'
    have he' : P.x₂ ^ v.2.toAdd.val = P.x₂ ^ w.2.toAdd.val := by
      rw [hi] at he
      exact mul_left_cancel he
    have heval : v.2.toAdd.val = w.2.toAdd.val :=
      pow_injOn_Iio_orderOf (by simpa [P.x₂_orderOf] using ZMod.val_lt v.2.toAdd)
        (by simpa [P.x₂_orderOf] using ZMod.val_lt w.2.toAdd) he'
    apply Prod.ext
    · exact Multiplicative.toAdd.injective (ZMod.val_injective _ hi)
    · exact Multiplicative.toAdd.injective (ZMod.val_injective _ heval)
  · intro g
    obtain ⟨i,e,h⟩ := (P.mem_exceptionalBase_iff g).mp g.property
    exact ⟨(Multiplicative.ofAdd (i : ZMod (2^n)), Multiplicative.ofAdd (e : ZMod 2)),
      Subtype.ext ((P.exceptionalBaseEval_zpow i e).trans h)⟩

public noncomputable def exceptionalBaseEquiv : P.exceptionalBase ≃*
    (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2)) :=
  (MulEquiv.ofBijective P.exceptionalBaseEval P.exceptionalBaseEval_bijective).symm

public theorem exceptionalBaseEquiv_symm_apply
    (v : Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2)) :
    (P.exceptionalBaseEquiv.symm v : S) = P.u ^ v.1.toAdd.val * P.x₂ ^ v.2.toAdd.val := by rfl

public theorem exists_exceptionalBase_form {g : S} (hg : g ∈ P.exceptionalBase) :
    ∃ i : Fin (2 ^ n), ∃ e : Fin 2, P.u ^ i.val * P.x₂ ^ e.val = g := by
  let v := P.exceptionalBaseEquiv ⟨g,hg⟩
  refine ⟨⟨v.1.toAdd.val,ZMod.val_lt _⟩,⟨v.2.toAdd.val,ZMod.val_lt _⟩,?_⟩
  exact (P.exceptionalBaseEquiv_symm_apply v).symm.trans
    (congrArg Subtype.val (P.exceptionalBaseEquiv.symm_apply_apply ⟨g,hg⟩))

public theorem card_exceptionalBase : Nat.card P.exceptionalBase = 2 ^ (n+1) := by
  rw [Nat.card_congr P.exceptionalBaseEquiv.toEquiv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_multiplicative, ZMod.card, pow_succ]

public theorem exceptional_base_structure :
    P.exceptionalBase.Normal ∧ P.exceptionalBase ≤ P.U ∧
      Nat.card P.exceptionalBase = 2 ^ (n+1) ∧
      Nonempty (P.exceptionalBase ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod 2))) :=
  ⟨P.exceptionalBase_normal, P.exceptionalBase_le_U, P.card_exceptionalBase,
    ⟨P.exceptionalBaseEquiv⟩⟩
end ABG.Wreathed.Presentation
