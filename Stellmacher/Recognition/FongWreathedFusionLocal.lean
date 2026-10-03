module

public import Stellmacher.Recognition.FongWreathedFusionSeparation

/-!
# Presentation-independent positive fusion in Fong's order-32 case

Both canonical automizers have index six in a finite simple group. Thus every
ambient involution is conjugate to `J`, and the normalizer of the quaternion
central product fuses `XF²` to `EF`. These results use any supplied presentation;
the orientation of the two nonreal order-four classes is a separate choice.

The QD characterization gives both indices. The full normalizer action on the
quaternion core is transitive on its order-four elements, and the coordinates
identify `XF²` and `EF` with the inverse rotation and the other quaternion
generator. This proves the outer positive fusions of Fong (1967), p. 70,
equation (5), via ABG II.1's canonical normalizer action.
-/

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
  (S : Sylow 2 G) (P : Wreathed.Presentation S 2)

/-- The high-index fusion pattern holds for the frame of every presentation. -/
public theorem qdPattern :
    WreathedQDPattern (P.U.map (S : Subgroup G).subtype)
      (P.V.map (S : Subgroup G).subtype) := by
  have hf := P.fusionFrame S
  exact wreathed_qdPattern_of_no_normal_index_two S 2 _ _ hf
    (isQDGroup_of_simple_wreathed32 S hf.1).no_normal_index_two

public theorem isConj_involution_J (x : G) (hx : orderOf x = 2) :
    IsConj x ((J P : S) : G) := by
  obtain ⟨r, _, _, hcov⟩ := (qdPattern S P).2.1
  obtain ⟨i, hi⟩ := hcov x hx
  obtain ⟨j, hj⟩ := hcov (J P : S) ((Subgroup.orderOf_coe _).trans (J_orderOf P))
  exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)

omit [Finite G] [IsSimpleGroup G] in
public theorem EF_eq_d : E P * F P = P.d := by
  change P.s * (P.s * P.z) = P.s ^ 2 * P.z
  simp only [pow_two, mul_assoc]

omit [Finite G] [IsSimpleGroup G] in
public theorem EF_orderOf : orderOf (E P * F P) = 4 := by
  have hs : (E P * F P) ^ 2 = J P := by
    rw [EF_eq_d, P.d_sq, P.r_half]
    rfl
  apply @orderOf_eq_prime_pow S _ (E P * F P) 1 2 _
  · change (E P * F P) ^ 2 ≠ 1
    rw [hs]
    intro h
    have ho := J_orderOf P
    rw [h, orderOf_one] at ho
    omega
  · change (E P * F P) ^ 4 = 1
    rw [show 4 = 2 * 2 from rfl, pow_mul, hs]
    simpa only [J_orderOf] using pow_orderOf_eq_one (J P)

/-- The high quaternion automizer fuses the two order-four elements of its core. -/
public theorem isConj_XF_sq_EF :
    IsConj ((X P * F P ^ 2 : S) : G) ((E P * F P : S) : G) := by
  let Q := P.quaternionCore.map (S : Subgroup G).subtype
  have hr : P.r ∈ P.quaternionCore := by
    change P.r ∈ Subgroup.closure {P.r ^ (2 ^ (2 - 2)), P.d}
    apply Subgroup.subset_closure
    simp
  have ha : X P * F P ^ 2 ∈ P.quaternionCore := by
    rw [XF_sq_eq_r_inv]
    exact P.quaternionCore.inv_mem hr
  have hb : E P * F P ∈ P.quaternionCore := by
    rw [EF_eq_d]
    exact Subgroup.subset_closure (by simp)
  let a : Q := ⟨((X P * F P ^ 2 : S) : G), Subgroup.mem_map_of_mem _ ha⟩
  let b : Q := ⟨((E P * F P : S) : G), Subgroup.mem_map_of_mem _ hb⟩
  obtain ⟨e₀⟩ := P.quaternion_core_model.1
  let e : Q ≃* QuaternionGroup 2 :=
    (P.quaternionCore.equivMapOfInjective (S : Subgroup G).subtype
      (S : Subgroup G).subtype_injective).symm.trans e₀
  have ha4 : orderOf a = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe (X P * F P ^ 2)).trans (XF_sq_orderOf P)
  have hb4 : orderOf b = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe (E P * F P)).trans (EF_orderOf S P)
  obtain ⟨f, hf⟩ := QuaternionGroup.exists_mulAut_eq_of_orderOf_eq_four (e a) (e b)
    ((e.orderOf_eq a).trans ha4) ((e.orderOf_eq b).trans hb4)
  let alpha : MulAut Q := (MulAut.congr e.symm) f
  have hab : alpha a = b := by
    change e.symm (f (e a)) = b
    rw [hf, e.symm_apply_apply]
  obtain ⟨g, _, hg⟩ := Wreathed.canonical_v_restriction_surjective S P
    (qdPattern S P).2.2.2 alpha
  apply isConj_iff.mpr
  refine ⟨g, ?_⟩
  have hh := hg a
  rw [hab] at hh
  exact hh

omit [Finite G] [IsSimpleGroup G] in
public theorem EF_inv_eq_rz : E P * (F P)⁻¹ = P.r * P.z := by
  simp only [E, F, mul_inv_rev, P.z_inv, Wreathed.Presentation.r]
  have ht : P.z * P.s⁻¹ = P.t⁻¹ * P.z :=
    (show SemiconjBy P.z P.s P.t from P.z_mul_s).inv_right
  rw [mul_assoc, ht, ← mul_assoc]

omit [Finite G] [IsSimpleGroup G] in
public theorem EF_inv_orderOf : orderOf (E P * (F P)⁻¹) = 2 := by
  have hs : (E P * (F P)⁻¹) ^ 2 = 1 := by
    rw [EF_inv_eq_rz]
    calc
      _ = P.r * (P.z * P.r * P.z⁻¹) := by rw [P.z_inv, pow_two]; group
      _ = 1 := by rw [P.z_conj_r, mul_inv_cancel]
  apply orderOf_eq_prime_iff.mpr
  refine ⟨hs, ?_⟩
  intro he
  have hef : E P = F P := (mul_inv_eq_one.mp he)
  have ho := E_orderOf P
  rw [hef, F_orderOf] at ho
  omega

public theorem isConj_EF_inv_J :
    IsConj ((E P * (F P)⁻¹ : S) : G) ((J P : S) : G) :=
  isConj_involution_J S P _ ((Subgroup.orderOf_coe _).trans (EF_inv_orderOf S P))

public theorem isConj_X_EF_inv :
    IsConj ((X P : S) : G) ((E P * (F P)⁻¹ : S) : G) :=
  (isConj_X_J S P).trans (isConj_EF_inv_J S P).symm

end Stellmacher.Recognition.FongWreathedIntrinsic
