module
public import Theory.GroupAction.InvolutionDisplacementCard
public import Mathlib.GroupTheory.PGroup

/-!
# Fixed index eight on a sixteen-element invariant support

Let a two-group B act on a finite elementary abelian two-group W. Suppose
W is the direct sum of a B-invariant subgroup U of order sixteen and a
subgroup F fixed pointwise by B. If B contains a central automorphism t
of square one with displacement subgroup of order four, then a nonquadratic
B-action has common fixed subgroup of index eight. The canonical actions
of the supplied automorphisms and the invariant subgroup are used throughout.

Orbit counting makes the common fixed subgroup on U have positive even
order. Since F is fixed, restriction to U preserves the common fixed index,
which is at most eight. Involution rank-nullity gives t-fixed index four;
this divides the common fixed index. If the two indices were equal, the
fixed subgroups would coincide. The t-displacement would then be fixed by
B, and commutation with t would put every B-displacement in that same fixed
subgroup, contradicting the nonquadratic hypothesis.

This elementary counting and commutation argument supplies the fixed index
in the cost-four branch of Stellmacher (8.6), Journal of Algebra 190 (1997),
printed p.44. It is independent of the local graph and classification setup.
-/

open scoped IsMulCommutative

public theorem fixedPoints_index_eq_eight_of_sixteen_support
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (B : Subgroup (MulAut W)) (U F : Subgroup W) [IsInvariant B W U]
    (hU : Nat.card U = 16) (hcompl : IsCompl U F)
    (hF : F ≤ FixedPoints.subgroup B W) (hB : IsPGroup 2 B)
    (t : MulAut W) (ht : t ∈ B) (hsquare : t ^ 2 = 1)
    (hcentral : ∀ b ∈ B, Commute b t)
    (hdisp : Nat.card (commutatorAction (Subgroup.zpowers t) W) = 4)
    (hnonquad : commutatorAction₂ B W ≠ ⊥) :
    (FixedPoints.subgroup B W).index = 8 := by
  let C := FixedPoints.subgroup B W
  let CU := FixedPoints.subgroup B U
  let T := FixedPoints.subgroup (Subgroup.zpowers t) W
  have hCU : C.subgroupOf U = CU := by
    ext u
    constructor
    · intro hu b
      apply Subtype.ext
      exact hu b
    · intro hu b
      exact congrArg Subtype.val (hu b)
  have hspan : U ⊔ C = ⊤ := top_unique
    (hcompl.sup_eq_top ▸ sup_le_sup_left hF U)
  have hindexU : C.index = CU.index := by
    have hh := Subgroup.relIndex_sup_right U C
    rw [hspan, Subgroup.relIndex_top_right] at hh
    change C.index = (C.subgroupOf U).index at hh
    rwa [hCU] at hh
  have hparity := hB.card_modEq_card_fixedPoints U
  change Nat.ModEq 2 (Nat.card U) (Nat.card CU) at hparity
  have hpos : 0 < Nat.card CU := Nat.card_pos
  have htwo : 2 ≤ Nat.card CU := by
    norm_num [Nat.ModEq, hU] at hparity
    omega
  have hcountU := CU.index_mul_card
  rw [hU, ← hindexU] at hcountU
  have hupper : C.index ≤ 8 := by nlinarith
  obtain ⟨hcountT, hquadT⟩ := MulAut.involution_fixed_displacement_card_data t hsquare
  change Nat.card W = Nat.card T * _ at hcountT
  rw [hdisp] at hcountT
  have hindexT : T.index = 4 := by
    have hh := T.index_mul_card
    rw [hcountT, mul_comm (Nat.card T)] at hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hh
  have hCT : C ≤ T := by
    intro w hw a
    exact smul_eq_self_of_mem_zpowers a.property (hw ⟨t, ht⟩)
  have hdiv : 4 ∣ C.index := hindexT ▸ Subgroup.index_dvd_of_le hCT
  have hneFour : C.index ≠ 4 := by
    intro hfour
    have heq : C = T := Subgroup.eq_of_le_of_card_ge hCT (by
      have hc := C.index_mul_card
      have ht := T.index_mul_card
      rw [hfour] at hc
      rw [hindexT] at ht
      omega)
    have hdispl : commutatorAction B W ≤ C := by
      rw [heq, commutatorAction_eq_closure]
      apply (Subgroup.closure_le (K := T)).mpr
      rintro _ ⟨b, w, rfl⟩ a
      have hd : w⁻¹ * t w ∈ commutatorAction (Subgroup.zpowers t) W := by
        rw [commutatorAction_eq_closure]
        exact Subgroup.subset_closure ⟨⟨t, Subgroup.mem_zpowers t⟩, w, rfl⟩
      have hfixed : w⁻¹ * t w ∈ C := heq ▸ hquadT hd
      have hb : (b : MulAut W) (w⁻¹ * t w) = w⁻¹ * t w := hfixed b
      have hbt : (b : MulAut W) (t w) = t ((b : MulAut W) w) :=
        DFunLike.congr_fun (hcentral b b.property).eq w
      have hfixedDisp : t (w⁻¹ * (b : MulAut W) w) = w⁻¹ * (b : MulAut W) w := by
        rw [map_mul, map_inv]
        rw [map_mul, map_inv, hbt] at hb
        have hexpr : t ((b : MulAut W) w) = (b : MulAut W) w * (w⁻¹ * t w) :=
          inv_mul_eq_iff_eq_mul.mp hb
        rw [hexpr]
        calc
          (t w)⁻¹ * ((b : MulAut W) w * (w⁻¹ * t w)) =
              ((t w)⁻¹ * t w) * (w⁻¹ * (b : MulAut W) w) := by ac_rfl
          _ = w⁻¹ * (b : MulAut W) w := by simp
      exact smul_eq_self_of_mem_zpowers a.property hfixedDisp
    apply hnonquad
    apply bot_unique
    rw [commutatorAction₂, commutatorSubgroup, Subgroup.closure_le]
    rintro _ ⟨b, w, hw, rfl⟩
    rw [(hdispl hw) b, inv_mul_cancel]
    exact Subgroup.one_mem _
  have hindexPos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨k, hk⟩ := hdiv
  change C.index = 8
  omega
