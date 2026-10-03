module

public import Stellmacher.Recognition.FongWreathedCentralizerQuotients

/-!
# Separation of Fong's six fusion representatives

For every actual height-two wreathed presentation in a finite simple group,
`F²` is not conjugate to its inverse. Indeed a putative conjugator centralizes
`J = F⁴`, while the image of `F²` in `C(J)/O(C(J))` is central of order four.
The real element `XF²` therefore belongs to neither of these classes. Squaring
separates `F` from `F³`; element orders give all remaining separations.
These conclusions do not require an oriented presentation or solvability.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)* (1967), pp. 69–70, the separations preceding equation (5). The
centralizer quotient argument uses the independent ABG Q-group calculation.
-/

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
  (S : Sylow 2 G) (P : Wreathed.Presentation S 2)

/-- The two central elements of order four are in distinct ambient classes. -/
public theorem not_isConj_F_sq_inv :
    ¬ IsConj ((F P ^ 2 : S) : G) (((F P ^ 2)⁻¹ : S) : G) := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hs : (F P ^ 2) ^ 2 = J P := by rw [← pow_mul, F_four]
  have hJ : (J P)⁻¹ = J P := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [← pow_two, J_orderOf] using pow_orderOf_eq_one (J P)
  have hgJ : g * ((J P : S) : G) * g⁻¹ = ((J P : S) : G) := by
    have hp := congrArg (fun a : G => a ^ 2) hg
    change ((MulAut.conj g) ((F P ^ 2 : S) : G)) ^ 2 = _ at hp
    rw [← map_pow] at hp
    simpa only [← Subgroup.coe_pow, inv_pow, hs, hJ, MulAut.conj_apply] using hp
  let C := Subgroup.centralizer ({((J P : S) : G)} : Set G)
  have hgC : g ∈ C := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (mul_inv_eq_iff_eq_mul).mp hgJ
  let a : C := squareInCentralizerJ S P
  have hc : IsConj a a⁻¹ := isConj_iff.mpr ⟨⟨g, hgC⟩, Subtype.ext hg⟩
  let q := QuotientGroup.mk' (pPrimeCore 2 C)
  have he : q a = (q a)⁻¹ := by
    apply IsConj.eq_of_left_mem_center (by simpa only [map_inv] using q.map_isConj hc)
    exact squareInCentralizerJ_quotient_mem_center S P
  have hpow : (q a) ^ 2 = 1 := by
    calc
      _ = q a * (q a)⁻¹ := by rw [pow_two]; exact congrArg (q a * ·) he
      _ = 1 := mul_inv_cancel _
  have hd := orderOf_dvd_of_pow_eq_one hpow
  rw [squareInCentralizerJ_quotient_orderOf S P] at hd
  norm_num at hd

omit [Finite G] [IsSimpleGroup G] in
/-- The third order-four representative is the inverse quaternion rotation. -/
public theorem XF_sq_eq_r_inv : X P * F P ^ 2 = P.r⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [F_sq, mul_assoc, P.u_mul_r]
  change P.s ^ 2 * P.s ^ 2 = 1
  rw [← pow_add]
  exact P.s_pow

private theorem isConj_inv {H : Type*} [Group H] {a b : H}
    (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨g, by simpa [mul_assoc] using congrArg Inv.inv hg⟩

omit [Finite G] [IsSimpleGroup G] in
/-- `XF²` is conjugate to its inverse already inside the Sylow subgroup. -/
public theorem isConj_XF_sq_inv :
    IsConj (X P * F P ^ 2) (X P * F P ^ 2)⁻¹ := by
  rw [XF_sq_eq_r_inv]
  exact isConj_inv (isConj_iff.mpr ⟨P.z, P.z_conj_r⟩)

public theorem not_isConj_F_sq_XF_sq :
    ¬ IsConj ((F P ^ 2 : S) : G) ((X P * F P ^ 2 : S) : G) := by
  intro h
  apply not_isConj_F_sq_inv S P
  exact (h.trans ((S : Subgroup G).subtype.map_isConj (isConj_XF_sq_inv S P))).trans
    (isConj_inv h).symm

public theorem not_isConj_F_sq_inv_XF_sq :
    ¬ IsConj (((F P ^ 2)⁻¹ : S) : G) ((X P * F P ^ 2 : S) : G) := by
  intro h
  apply not_isConj_F_sq_XF_sq S P
  have hi : IsConj ((F P ^ 2 : S) : G) (((X P * F P ^ 2 : S) : G)⁻¹) := by
    have hh := isConj_inv h
    change IsConj ((((F P ^ 2 : S) : G))⁻¹)⁻¹ _ at hh
    simpa only [Subgroup.coe_inv, inv_inv] using hh
  exact hi.trans ((S : Subgroup G).subtype.map_isConj (isConj_XF_sq_inv S P)).symm

omit [Finite G] [IsSimpleGroup G] in
public theorem F_cube_sq : (F P ^ 3) ^ 2 = (F P ^ 2)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_mul, ← pow_add]
  simpa only [F_orderOf] using pow_orderOf_eq_one (F P)

public theorem not_isConj_F_F_cube :
    ¬ IsConj ((F P : S) : G) ((F P ^ 3 : S) : G) := by
  intro h
  apply not_isConj_F_sq_inv S P
  have hp := h.pow 2
  change IsConj ((F P ^ 2 : S) : G) (((F P ^ 3) ^ 2 : S) : G) at hp
  rw [F_cube_sq S P] at hp
  exact hp

/-- The six representatives in the order used in Fong's equation (5). -/
@[expose] public def fusionRepresentative : Fin 6 → S :=
  ![F P, F P ^ 3, F P ^ 2, (F P ^ 2)⁻¹, X P * F P ^ 2, J P]

omit [Finite G] [IsSimpleGroup G] in
public theorem fusionRepresentative_orderOf (i : Fin 6) :
    orderOf (fusionRepresentative S P i) = ![8, 8, 4, 4, 4, 2] i := by
  fin_cases i <;> simp [fusionRepresentative, F_orderOf, F_cube_orderOf,
    F_sq_orderOf, XF_sq_orderOf, J_orderOf]

/-- Distinct indices always give distinct ambient conjugacy classes. -/
public theorem fusionRepresentative_separated (i j : Fin 6)
    (h : IsConj ((fusionRepresentative S P i : S) : G)
      ((fusionRepresentative S P j : S) : G)) : i = j := by
  have ho : orderOf (fusionRepresentative S P i) =
      orderOf (fusionRepresentative S P j) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    have he := (MulAut.conj g).orderOf_eq ((fusionRepresentative S P i : S) : G)
    change orderOf (g * _ * g⁻¹) = _ at he
    rw [hg] at he
    simpa only [Subgroup.orderOf_coe] using he.symm
  rw [fusionRepresentative_orderOf, fusionRepresentative_orderOf] at ho
  fin_cases i <;> fin_cases j
  all_goals norm_num at ho
  all_goals try rfl
  all_goals dsimp [fusionRepresentative] at h
  all_goals first
    | exact (not_isConj_F_F_cube S P h).elim
    | exact (not_isConj_F_F_cube S P h.symm).elim
    | exact (not_isConj_F_sq_inv S P h).elim
    | exact (not_isConj_F_sq_inv S P h.symm).elim
    | exact (not_isConj_F_sq_XF_sq S P h).elim
    | exact (not_isConj_F_sq_XF_sq S P h.symm).elim
    | exact (not_isConj_F_sq_inv_XF_sq S P h).elim
    | exact (not_isConj_F_sq_inv_XF_sq S P h.symm).elim

end Stellmacher.Recognition.FongWreathedIntrinsic
