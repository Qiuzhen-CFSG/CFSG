module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic

/-!
# Fixed-index and faithful odd-core centralizer reductions

The index-two intersection bound compares offender ratios. Fitting and coprime-core calculations show that the Sylow subgroup meets the odd-core centralizer trivially under the exact faithful hypotheses.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- Fixed points of an image subgroup on a normal subgroup's fixed module
are exactly the ambient fixed points of its preimage, restricted to that
module.  We only need the cardinal form because the two sides use different
subtype towers. -/
public theorem natCard_fixedPoints_quotient_map_eq_inf
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (H : Subgroup G) (A X : Subgroup H) [A.Normal]
    (Q : Subgroup (H ⧸ A))
    (hQ : X.map (QuotientGroup.mk' A) = Q) :
    Nat.card (FixedPoints.subgroup Q (FixedPoints.subgroup A V)) =
      Nat.card (↥((FixedPoints.subgroup A V) ⊓
        FixedPoints.subgroup (X.map H.subtype) V)) := by
  let q : H →* H ⧸ A := QuotientGroup.mk' A
  let Cbar := FixedPoints.subgroup Q (FixedPoints.subgroup A V)
  let Camb : Subgroup V := FixedPoints.subgroup A V ⊓
    FixedPoints.subgroup (X.map H.subtype) V
  let f : Cbar → Camb := fun z => ⟨((z : FixedPoints.subgroup A V) : V),
    z.val.property, by
      refine (FixedPoints.mem_subgroup
        (M := X.map H.subtype) (a := (z : V))).2 ?_
      intro x
      obtain ⟨xh, hxhX, hxval⟩ := x.property
      have hqxQ : q xh ∈ Q := by
        rw [← hQ]
        exact ⟨xh, hxhX, rfl⟩
      have hzfix := (FixedPoints.mem_subgroup
        (M := Q) (a := (z : FixedPoints.subgroup A V))).1 z.property
        ⟨q xh, hqxQ⟩
      have hzfixA : (q xh) • (z : FixedPoints.subgroup A V) =
          (z : FixedPoints.subgroup A V) := by
        simpa only [Subgroup.smul_def] using hzfix
      have hzfixV := congrArg
        (fun w : FixedPoints.subgroup A V => (w : V)) hzfixA
      change (xh : G) • (z : V) = (z : V) at hzfixV
      change ((x : X.map H.subtype) : G) • (z : V) = (z : V)
      rw [← hxval]
      exact hzfixV⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : Camb => (z : V)) hxy))
  have hfsurj : Function.Surjective f := by
    intro z
    let za : FixedPoints.subgroup A V := ⟨(z : V), z.property.1⟩
    have hzbar : za ∈ Cbar := by
      rw [FixedPoints.mem_subgroup]
      intro qx
      have hqxMap : (qx : H ⧸ A) ∈ X.map q := by
        rw [hQ]
        exact qx.property
      obtain ⟨xh, hxhX, hxq⟩ := hqxMap
      have hxhMap : (xh : G) ∈ X.map H.subtype :=
        ⟨xh, hxhX, rfl⟩
      have hzfix := (FixedPoints.mem_subgroup
        (M := X.map H.subtype) (a := (z : V))).1 z.property.2
        ⟨xh, hxhMap⟩
      change (qx : H ⧸ A) • za = za
      rw [← hxq]
      apply Subtype.ext
      change (xh : G) • (z : V) = (z : V)
      simpa only [Subgroup.smul_def] using hzfix
    refine ⟨⟨za, hzbar⟩, ?_⟩
    apply Subtype.ext
    rfl
  exact Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)

/-- If an involution fixes points outside `C_V(A)` while its fixed points
inside `C_V(A)` have index two, then its total fixed subgroup is at least as
large as `C_V(A)`.  For two order-two actors this is exactly the required
comparison of `m`-values. -/
public theorem m_le_of_fixed_intersection_index_two_of_not_le
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (A B : Subgroup G) (hAcard : Nat.card A = 2)
    (hBcard : Nat.card B = 2)
    (hratio : (Nat.card (FixedPoints.subgroup A V) : ℚ) /
      Nat.card (↥(FixedPoints.subgroup A V ⊓
        FixedPoints.subgroup B V)) = 2)
    (hnotle : ¬ FixedPoints.subgroup B V ≤ FixedPoints.subgroup A V) :
    m (G := G) (V := V) B ≤ m (G := G) (V := V) A := by
  let CA : Subgroup V := FixedPoints.subgroup A V
  let CB : Subgroup V := FixedPoints.subgroup B V
  let C : Subgroup V := CA ⊓ CB
  have hCneTop : C.subgroupOf CB ≠ ⊤ := by
    intro htop
    have hCBleC : CB ≤ C := Subgroup.subgroupOf_eq_top.mp htop
    apply hnotle
    exact hCBleC.trans inf_le_left
  have hindex : 2 ≤ (C.subgroupOf CB).index := by
    have := Subgroup.one_lt_index_of_ne_top hCneTop
    omega
  have hcardSub : Nat.card (C.subgroupOf CB) = Nat.card C :=
    natCard_subgroupOf_eq C CB inf_le_right
  have hindexCard : Nat.card C * (C.subgroupOf CB).index = Nat.card CB := by
    have hmul := Subgroup.index_mul_card (H := C.subgroupOf CB)
    simpa [hcardSub, mul_comm] using hmul
  have hcardTwice : 2 * Nat.card C ≤ Nat.card CB := by
    nlinarith [hindexCard]
  have hcardCA : Nat.card CA = 2 * Nat.card C := by
    have hden : (Nat.card C : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := C)).ne'
    have hq : (Nat.card CA : ℚ) = 2 * Nat.card C := by
      exact (div_eq_iff hden).1 (by simpa only [CA, C] using hratio)
    exact_mod_cast hq
  have hcardLe : Nat.card CA ≤ Nat.card CB := by
    rw [hcardCA]
    exact hcardTwice
  unfold m
  have hdenB : (0 : ℚ) <
      (Nat.card (FixedPoints.subgroup B V) : ℚ) * Nat.card B :=
    mul_pos (by exact_mod_cast (Nat.card_pos
      (α := FixedPoints.subgroup B V)))
      (by exact_mod_cast (Nat.card_pos (α := B)))
  have hdenA : (0 : ℚ) <
      (Nat.card (FixedPoints.subgroup A V) : ℚ) * Nat.card A :=
    mul_pos (by exact_mod_cast (Nat.card_pos
      (α := FixedPoints.subgroup A V)))
      (by exact_mod_cast (Nat.card_pos (α := A)))
  apply (div_le_div_iff₀ hdenB hdenA).2
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [hAcard, hBcard]
  exact_mod_cast (Nat.mul_le_mul_right 2
    (by simpa only [CA, CB] using hcardLe))

/-- In the present solvable characteristic-two-free situation, a nilpotent
odd core is the whole Fitting subgroup.  This is the standard reason that its
ambient centralizer has no nontrivial two-elements. -/
private theorem oddCore_eq_fitting_of_solvable_twoCore_eq_bot_of_isPGroup_three
    {G : Type u} [Group G] [Finite G]
    (_hsolv : Group.IsSolvable G) (hO2 : pCore 2 G = ⊥)
    (hWthree : IsPGroup 3 (oddCore G)) :
    oddCore G = fittingSubgroup G := by
  apply le_antisymm
  · apply le_sSup
    exact ⟨pPrimeCore_normal, hWthree.isNilpotent⟩
  · refine sSup_le ?_
    intro N hN
    have hcop : Nat.Coprime 2 (Nat.card N) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro htwo
      let Q : Sylow 2 N := Classical.choice Sylow.nonempty
      have hQne : (Q : Subgroup N) ≠ ⊥ :=
        Sylow.ne_bot_of_dvd_card Q htwo
      let hQnormal : (Q : Subgroup N).Normal := by
        let _ : Group.IsNilpotent N := hN.2
        exact Sylow.normal_of_normalizerCondition
          Group.normalizerCondition_of_isNilpotent Q
      let hQchar : (Q : Subgroup N).Characteristic :=
        Sylow.characteristic_of_normal Q hQnormal
      let _ : N.Normal := hN.1
      let _ : (Q : Subgroup N).Characteristic := hQchar
      have hQmapNormal : ((Q : Subgroup N).map N.subtype).Normal := by
        infer_instance
      have hQmapTwo : IsPGroup 2 ((Q : Subgroup N).map N.subtype) :=
        Q.isPGroup'.map N.subtype
      have hQmapLe : (Q : Subgroup N).map N.subtype ≤ pCore 2 G :=
        le_sSup ⟨hQmapNormal, hQmapTwo⟩
      have hQmapBot : (Q : Subgroup N).map N.subtype = ⊥ :=
        le_bot_iff.mp (hQmapLe.trans hO2.le)
      have hQbot : (Q : Subgroup N) = ⊥ := by
        apply Subgroup.map_injective N.subtype_injective
        rw [hQmapBot, Subgroup.map_bot]
      exact hQne hQbot
    exact le_sSup ⟨hN.1, hcop⟩

public theorem sylow_inf_centralizer_oddCore_eq_bot
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Subgroup G)
    (hS : IsElementaryAbelian 2 S)
    (hWthree : IsPGroup 3 (oddCore G)) :
    S ⊓ Subgroup.centralizer (oddCore G : Set G) = ⊥ := by
  have hfit : oddCore G = fittingSubgroup G :=
    oddCore_eq_fitting_of_solvable_twoCore_eq_bot_of_isPGroup_three
      h.G_solvable h.twoCore_eq_bot hWthree
  have hcentLeW : Subgroup.centralizer (oddCore G : Set G) ≤ oddCore G := by
    rw [hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
      h.G_solvable
  have hSp : IsPGroup 2 S := hS.isPGroup 2 S
  have hdisj : Disjoint S (oddCore G) :=
    IsPGroup.disjoint_of_ne 2 3 (by decide) S (oddCore G) hSp hWthree
  apply le_antisymm
  · exact (le_inf inf_le_left (inf_le_right.trans hcentLeW)).trans
      hdisj.le_bot
  · exact bot_le

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
