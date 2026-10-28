module
public import Theory.Representation.G2BinaryNaturalOffenders
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.PureLong

/-!
# Both natural-module ratios for the actual binary derived G₂ group

Every involution in G₂(2)′ is a long root: the other root class has nontrivial
image in the index-two quotient. Simultaneous long-root fusion bounds every
elementary actor by the root plane. The full-group offender classification
excludes derived-group offenders, so rank at most two gives ratio at least
3/2 for every elementary actor. The actual quadratic long-root plane has
rank two and fixed codimension three, attaining both infima.

Source: Aschbacher–Smith B.4.5 and B.4.6, printed pp.87–90.
-/

public noncomputable section
namespace Atlas.G2.Natural.BinaryNormalizer
open Representation Representation.BinaryOffender Subgroup NaturalOffenders
open scoped ENNReal
local notation "τ" => (Natural.action (ZMod 2))
local notation "δ" => (MonoidHom.comp (Natural.action (ZMod 2)) Derived.subtype)

theorem derived_involution_long (x : Derived) (hx2 : x ^ 2 = 1) (hne : x ≠ 1) :
    ShortRootProducts.IsLongRootElement (x : Full) := by
  have hx2' : (x : Full) ^ 2 = 1 := congrArg Subtype.val hx2
  have hne' : (x : Full) ≠ 1 := fun h => hne (Subtype.ext h)
  rcases EvenInvolutionGeometry.involution_isRoot hx2' hne' with hl | ⟨g,a,ha,hx⟩
  · obtain ⟨g,a,ha,hx⟩ := hl
    exact ⟨a,ha,g,hx⟩
  · exfalso
    have he : a = 1 := by
      have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      exact (hb a).resolve_left ha
    subst a
    have hm : g * rootC 1 * g⁻¹ ∈ Derived := by
      change MulAut.conj g (rootC 1) ∈ Derived
      rw [← hx]
      exact x.property
    have hc := (inferInstance : Derived.Normal).conj_mem' _ hm g
    apply rootC_not_mem_derived
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel, mul_one] using hc

theorem derived_rank_le_two (A : Subgroup Derived) (hA : IsElementaryTwo A) : rank A ≤ 2 := by
  let : IsElementaryAbelian 2 A := hA.2
  let B := A.map Derived.subtype
  have hp : ∀ b ∈ B, b ≠ 1 → ShortRootProducts.IsLongRootElement b := by
    rintro _ ⟨x,hx,rfl⟩ hn
    exact derived_involution_long x (elemPow_eq_one_of_isElementaryAbelian x hx)
      (fun h => hn (congrArg Subtype.val h))
  have hc := EvenInvolutionGeometry.PureLong.card_le_field_square B
    (IsElementaryAbelian.map Derived.subtype) hp
  rw [Subgroup.card_map_of_injective Derived.subtype_injective] at hc
  have hr := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.card_zmod, Nat.log_pow (by decide : 1 < 2)] using hr

theorem derived_not_ff : ¬ IsFFModule δ := by
  rintro ⟨A,hA⟩
  have hb := hA.map_equivariant δ τ Derived.subtype Derived.subtype_injective
    (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl)
  obtain ⟨g,_,hg⟩ := natural_offender_rootPair (n := 1) (by norm_num) (by decide) _ hb
  have hc := (inferInstance : Derived.Normal).conj_mem' _
    ((Subgroup.map_le_range _ _).trans (by simp) hg) g
  apply rootC_not_mem_derived
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
    inv_mul_cancel, mul_one] using hc

theorem derived_actionRatio_lower (A : Subgroup Derived) (hA : IsElementaryTwo A) :
    3 / 2 ≤ actionRatio δ A := by
  have hr := derived_rank_le_two A hA
  have hp := hA.rank_pos
  have hd : rank A < fixedCodim δ A := by
    by_contra! hh
    exact derived_not_ff ⟨A,hA,hh⟩
  have hr' : rank A = 1 ∨ rank A = 2 := by omega
  rcases hr' with hr' | hr'
  · have hd' : (2 : ℝ≥0∞) ≤ fixedCodim δ A := by exact_mod_cast (show 2 ≤ fixedCodim δ A by omega)
    simp only [actionRatio, hr', Nat.cast_one, div_one]
    exact (by
      rw [ENNReal.div_le_iff (by norm_num) (by simp)]
      norm_num : (3 : ℝ≥0∞) / 2 ≤ 2).trans hd'
  · have hd' : (3 : ℝ≥0∞) ≤ fixedCodim δ A := by exact_mod_cast (show 3 ≤ fixedCodim δ A by omega)
    simpa only [actionRatio, hr', Nat.cast_ofNat] using ENNReal.div_le_div_right hd' 2

theorem natural_elementary_quadratic : IsQuadratic τ (EvenTwoRank.elementary (ZMod 2)) := by
  have hA := natural_elementary_offender (F := ZMod 2) (n := 1) (by norm_num) (by decide)
  obtain ⟨B,hBA,hB,hq,_⟩ := hA.exists_quadratic_minimalBestOffender τ
  have hr := natural_offender_rank (n := 1) (by norm_num) (by decide) B (hB.1.isOffender τ)
  have he : B = EvenTwoRank.elementary (ZMod 2) := by
    apply Subgroup.eq_of_le_of_card_ge hBA
    rw [hB.1.1.card_eq_two_pow_rank,hr,EvenTwoRank.elementary_card]
    norm_num
  exact he ▸ hq

theorem longRootLocal_le_derived : (longRootLocal (F := ZMod 2)) ≤ Derived := by
  rw [Derived,BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Subgroup.le_normalClosure

theorem derived_quadratic_upper : quadraticRatio δ ≤ 3 / 2 := by
  let A := (longRootLocal (F := ZMod 2)).subgroupOf Derived
  have hmap : A.map Derived.subtype = longRootLocal := map_subgroupOf_eq_of_le longRootLocal_le_derived
  have hcard : Nat.card A = 4 := by
    rw [← Subgroup.card_map_of_injective Derived.subtype_injective,hmap,card_longRootLocal]
    norm_num
  have hA : IsElementaryTwo A := by
    refine ⟨?_,?_⟩
    · intro he
      rw [he,Subgroup.card_bot] at hcard
      omega
    · refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
      · apply IsMulCommutative.of_setLike_mul_comm
        intro a ha b hb
        apply Subtype.ext
        exact congrArg (fun x : longRootLocal (F := ZMod 2) => (x : Full))
          ((IsMulCommutative.is_comm (M := longRootLocal (F := ZMod 2))).comm ⟨a,ha⟩ ⟨b,hb⟩)
      · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        intro a
        apply Subtype.ext
        apply Subtype.ext
        obtain ⟨p,hp⟩ := a.property
        change (Derived.subtype (a : Derived)) ^ 2 = 1
        rw [← hp,← map_pow]
        have hp2 : p ^ 2 = 1 := by
          apply Multiplicative.toAdd.injective
          simp only [pow_two]
          change p.toAdd + p.toAdd = (0 : ZMod 2 × ZMod 2)
          ext <;> exact CharTwo.add_self_eq_zero _
        rw [hp2,map_one]
  have hr : rank A = 2 := by simp only [rank,hcard]; decide
  have hd : fixedCodim δ A = 3 := by
    change fixedCodim δ (longRootLocal.subgroupOf Derived) = 3
    rw [fixedCodim_subgroupOf τ longRootLocal_le_derived]
    change fixedCodim (binaryNatural (F := ZMod 2)) longRootLocal = 3
    rw [natural_fixedCodim_eq, fixedCodim_longRootLocal (n := 1) (by norm_num)]
  have hle : longRootLocal (F := ZMod 2) ≤ EvenTwoRank.elementary (ZMod 2) := by
    rintro _ ⟨p,rfl⟩
    exact (EvenTwoRank.elementary _).mul_mem (rootA_mem_elementary _) (rootB_mem_elementary _)
  have hquad : IsQuadratic δ A := by
    intro a ha b hb v
    exact natural_elementary_quadratic a (hle ha) b (hle hb) v
  have hu : quadraticRatio δ ≤ actionRatio δ A :=
    iInf_le_of_le A (iInf_le_of_le ⟨hA,hquad⟩ le_rfl)
  simpa only [actionRatio,hr,hd,Nat.cast_ofNat] using hu

theorem derived_ratios : quadraticRatio δ = 3 / 2 ∧ cubicRatio δ = 3 / 2 := by
  have hc : 3 / 2 ≤ cubicRatio δ := le_iInf fun A => le_iInf fun hA => derived_actionRatio_lower A hA.1
  have hcq := cubicRatio_le_quadraticRatio δ
  exact ⟨le_antisymm derived_quadratic_upper (hc.trans hcq),
    le_antisymm (hcq.trans derived_quadratic_upper) hc⟩
end Atlas.G2.Natural.BinaryNormalizer
