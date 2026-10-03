module
public import Theory.GroupAction.ElementaryEightTwoActionFixedLine
public import Theory.GroupTheory.ElementaryPairHyperbolicGenerators
public import Theory.GroupTheory.HyperbolicQuaternionFactors
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Quaternion factors from two generating elementary eights

Let C and D be elementary abelian two-subgroups of order8 generating a finite
group whose center has order2. If C normalizes D, the group is the central
product of two commuting quaternion eights. The theorem assumes only this
one normalization direction, and derives the reverse direction in the proof.

First D is normal, and the generated group is a two-group. The center meets
its nontrivial normal subgroup D, so its order2 forces the entire center into
D. Conjugation of C on D has exactly this common fixed line. The elementary
eight fixed-line action theorem gives image order4 and puts every displacement
in that fixed line. The action kernel is C intersected with the ambient center;
counting its order gives2, so the center also lies in C. Hence C∩D is precisely
the center. The central displacement assertion, using both factors' exponent2,
now shows D normalizes C.

The elementary-pair pairing theorem extracts four hyperbolic involutions from
these two normal factors. The explicit hyperbolic quaternion construction then
produces two commuting Q8 subgroups generating the group and intersecting in
order2. All model statements remain intrinsic; no campaign-owned predicate or
abstract extraspecial classification theorem is imported.

Source: the extraspecial-plus recognition after Stellmacher (9.1), relation(11),
Journal of Algebra190 (1997), p.48.
-/

namespace Subgroup
open scoped Pointwise

private theorem elementary_pair_central_structure
    {G : Type*} [Group G] [Finite G] (C D : Subgroup G)
    (hC : IsElementaryAbelian 2 C) (hD : IsElementaryAbelian 2 D)
    (hCcard : Nat.card C = 8) (hDcard : Nat.card D = 8)
    (hgen : C ⊔ D = ⊤) (hn : C ≤ normalizer (D : Set G))
    (hZcard : Nat.card (center G) = 2) :
    C.Normal ∧ D.Normal ∧ C ⊓ D = center G := by
  classical
  let := hC
  let := hD
  have hDn : D.Normal := normalizer_eq_top_iff.mp (by
    apply top_unique
    rw [← hgen]
    exact sup_le hn D.le_normalizer)
  let := hDn
  have hGp : IsPGroup 2 G := by
    have hh := (IsElementaryAbelian.isPGroup 2 C).to_sup_of_normal_right
      (IsElementaryAbelian.isPGroup 2 D)
    rw [hgen] at hh
    exact hh.of_equiv topEquiv
  let : Fact (IsPGroup 2 G) := ⟨hGp⟩
  let : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by rw [hDcard]; decide)
  obtain ⟨z, hzne, hzcenter⟩ := exists_nontrivial_center_mem_normal (N := D) (p := 2)
  have hZD : center G ≤ D := by
    obtain ⟨other, hother, hall⟩ := (Nat.card_eq_two_iff' (1 : center G)).mp hZcard
    have hzneq : (⟨(z : G), hzcenter⟩ : center G) ≠ 1 := fun hh => hzne (Subtype.ext (congrArg (fun q : center G => (q : G)) hh))
    intro x hx
    by_cases heq : (⟨x, hx⟩ : center G) = 1
    · have hxone : x = 1 := congrArg Subtype.val heq
      simp [hxone]
    · have hh : x = (z : G) := congrArg (fun q : center G => (q : G)) ((hall _ heq).trans (hall _ hzneq).symm)
      exact hh.symm ▸ z.property
  have hDC : D ⊓ centralizer (C : Set G) = center G := by
    apply le_antisymm
    · intro x hx
      apply mem_center_iff.mpr
      intro g
      have hh : C ⊔ D ≤ centralizer ({x} : Set G) := by
        apply sup_le
        · intro c hc
          exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx.2 c hc)
        · intro d hd
          exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm (s := D) hd hx.1)
      rw [hgen] at hh
      exact mem_centralizer_singleton_iff.mp (hh (mem_top g))
    · intro x hx
      exact ⟨hZD hx, center_le_centralizer _ hx⟩
  let action : C →* MulAut D := D.normalizerMonoidHom.comp (inclusion hn)
  let B := action.range
  have hBsq : ∀ b : B, b ^ 2 = 1 := by
    rintro ⟨b, c, rfl⟩
    apply Subtype.ext
    change action c ^ 2 = 1
    rw [← map_pow]
    have hc2 : c ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 C) c
    rw [hc2, map_one]
  let : IsElementaryAbelian 2 B := {
    toIsMulCommutative := ⟨⟨fun a b => by
      obtain ⟨x, hx⟩ := a.property
      obtain ⟨y, hy⟩ := b.property
      apply Subtype.ext
      change (a : MulAut D) * b = (b : MulAut D) * a
      rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm']⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hBsq }
  have hfixmap : (FixedPoints.subgroup B D).map D.subtype = center G := by
    rw [← hDC]
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      refine ⟨d.property, mem_centralizer_iff.mpr ?_⟩
      intro c hc
      have hh := congrArg Subtype.val (hd (⟨action ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : B))
      change c * (d : G) * c⁻¹ = (d : G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · rintro ⟨hxD, hxC⟩
      refine ⟨⟨x, hxD⟩, ?_, rfl⟩
      rintro ⟨b, c, rfl⟩
      apply Subtype.ext
      change (c : G) * x * (c : G)⁻¹ = x
      rw [mem_centralizer_iff.mp hxC c c.property, mul_inv_cancel_right]
  have hfixcard : Nat.card (FixedPoints.subgroup B D) = 2 := by
    rw [← card_map_of_injective D.subtype_injective, hfixmap, hZcard]
  obtain ⟨hBcard, hdelta⟩ := elementaryEight_two_action_fixed_line hDcard B hfixcard
  have hker : action.ker = (C ⊓ center G).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker]
    constructor
    · intro hc
      refine ⟨c.property, mem_center_iff.mpr ?_⟩
      intro g
      have hCD : C ⊔ D ≤ centralizer ({(c : G)} : Set G) := by
        apply sup_le
        · intro a ha
          exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm ha c.property)
        · intro d hd
          have hh := congrArg (fun a : MulAut D => (a ⟨d, hd⟩ : G)) hc
          change (c : G) * d * (c : G)⁻¹ = d at hh
          exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
      rw [hgen] at hCD
      exact mem_centralizer_singleton_iff.mp (hCD (mem_top g))
    · intro hc
      apply MulEquiv.ext
      intro d
      apply Subtype.ext
      change (c : G) * (d : G) * (c : G)⁻¹ = (d : G)
      have hcc : (c : G) ∈ center G := hc.2
      have hh : (d : G) * (c : G) = (c : G) * (d : G) := mem_center_iff.mp hcc d
      rw [← hh, mul_inv_cancel_right]
  have hCZcard : Nat.card (C ⊓ center G : Subgroup G) = 2 := by
    have hh := action.ker.card_mul_index
    rw [index_ker] at hh
    change Nat.card action.ker * Nat.card B = Nat.card C at hh
    rw [hBcard, hCcard, hker, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at hh
    omega
  have hZC : center G ≤ C := by
    have heq : C ⊓ center G = center G := eq_of_le_of_card_ge inf_le_right (by rw [hCZcard, hZcard])
    exact heq.symm.le.trans inf_le_left
  have hCDZ : C ⊓ D = center G := by
    apply le_antisymm
    · intro x hx
      apply hDC.le
      exact ⟨hx.2, fun c hc => setLike_mul_comm hc hx.1⟩
    · exact le_inf hZC hZD
  have hCn : C.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    refine sup_le C.le_normalizer ?_
    rw [le_normalizer_iff_commutator_le_right]
    apply commutator_le.mpr
    intro d hd c hc
    have hh := hdelta (⟨action ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : B) (⟨d, hd⟩ : D)
    have hz := mem_map_of_mem D.subtype hh
    rw [hfixmap] at hz
    change d⁻¹ * (c * d * c⁻¹) ∈ center G at hz
    have hd2 : d⁻¹ = d := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) d hd)
    have hc2 : c⁻¹ = c := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) c hc)
    apply hZC
    simpa only [commutatorElement_def, hd2, hc2, mul_assoc] using hz
  exact ⟨hCn, hDn, hCDZ⟩

end Subgroup

/-- Two generating elementary eights, one normalizing the other, and ambient
center of order2 have a decomposition into two commuting quaternion eights. -/
public theorem exists_quaternion_factors_of_elementary_eights
    {G : Type*} [Group G] [Finite G] (C D : Subgroup G)
    (hC : IsElementaryAbelian 2 C) (hD : IsElementaryAbelian 2 D)
    (hCcard : Nat.card C = 8) (hDcard : Nat.card D = 8)
    (hgen : C ⊔ D = ⊤) (hn : C ≤ Subgroup.normalizer (D : Set G))
    (hZcard : Nat.card (Subgroup.center G) = 2) :
    ∃ L R : Subgroup G,
      Nonempty (L ≃* QuaternionGroup 2) ∧ Nonempty (R ≃* QuaternionGroup 2) ∧
      L ⊔ R = ⊤ ∧ Nat.card (L ⊓ R : Subgroup G) = 2 ∧
      (∀ l ∈ L, ∀ r ∈ R, l * r = r * l) := by
  obtain ⟨hCn, hDn, hinter⟩ := Subgroup.elementary_pair_central_structure
    C D hC hD hCcard hDcard hgen hn hZcard
  let := hC
  let := hD
  let := hCn
  let := hDn
  obtain ⟨x1, y1, x2, y2, z, _, _, _, _, hx1, hy1, hx2, hy2,
    hz, hz2, hzc, hxy1, hxy2, hxx, hxy, hyx, hyy, hgens⟩ :=
    exists_hyperbolic_involutions_of_elementary_pair C D hCcard hDcard hgen hinter hZcard
  exact exists_quaternion_factors_of_hyperbolic_involutions x1 y1 x2 y2 z
    hx1 hy1 hx2 hy2 hz hz2 hzc hxy1 hxy2 hxx hxy hyx hyy hgens
