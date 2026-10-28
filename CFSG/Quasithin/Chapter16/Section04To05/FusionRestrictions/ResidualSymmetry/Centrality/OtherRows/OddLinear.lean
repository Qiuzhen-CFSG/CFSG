module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.Marking
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.SplitModels
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.OddTwo
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.OddThree

/-!
# Separating the odd-linear residual rows

The complete (E2)(ii) alternative specifies the full component as PSL₃(3)
or PSL₂(p), with p a Fermat or Mersenne prime. Both families have trivial
center and a single class of inner involutions. Thus an inner action has
the same two-central mark as the given central action, and the noncentral
action must be outer.

For PSL₂, the central fixed group is Sylow and has trivial two-residual;
the outer dihedral fixed group has nontrivial two-residual. This includes
the order-six rows at p = 5 and p = 7. For PSL₃(3), the fixed groups are
GL₂(3) and S₄. Their two-residuals cannot be isomorphic: the former has
at most one involution and the latter is A₄, with distinct involutions.
All residuals are transported from full fixed groups through actual
multiplicative equivalences.

The exceptional three-residual modification is excluded from actual model
orders. The odd PSL₂ comparison uses the incompatible two-part and total
order of binary PSL₃; PSL₃(3) is smaller than every even-exponent PSL₃
model. In particular the outer order-three residuals at the small PSL₂
parameters are retained.

Only the universal outer fixed-group tables remain explicit earlier inputs.
The final comparison applies under weaker assumptions than the source:
perfection suffices, and no additional source model exclusions are needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, (E2)(ii)
and 16.1.5 on printed pp.1170–1172, and Notation 16.5.5 and 16.5.6(4)
on p.1197. The GL₂ residual obstruction follows the argument in
`SylowSymmetry/ReverseDelta/Comparison/OtherFamilies/OddThree.lean`.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.OddLinear
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] {L : Subgroup G}

/-- The two-part and order of an odd PSL₂ exclude all exceptional PSL₃ models. -/
theorem pslTwo_not_evenLinearThree [Group.IsPerfect L] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hL : ClassicalGroup.IsPSL L 2 p) :
    ¬ HasEvenLinearThreeType L := by
  rintro ⟨n, hn, he, hmodel⟩
  have hp5 := OtherPreliminaries.OddLinear.pslTwo_parameter_ge_five hp hL
  have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
  exact Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.not_linear_three
    (hp.1.odd_of_ne_two (by omega)) hp.1.two_le hn2 hL hmodel

/-- PSL₃(3) has order 5616, below every positive even-exponent PSL₃ model. -/
theorem pslThree_not_evenLinearThree (hL : ClassicalGroup.IsPSL L 3 3) :
    ¬ HasEvenLinearThreeType L := by
  obtain ⟨e⟩ := OtherPreliminaries.equiv_pslThree_of_isPSL hL
  have hc : Nat.card L = 5616 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Three.card_PSL
  rintro ⟨n, hn, he, F, _, _, hF, ⟨f⟩⟩
  have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
  have hq : 4 ≤ 2^n := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn2
  have ho := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
  rw [← Nat.card_congr f.toEquiv, hc, hF] at ho
  have hd : Nat.gcd 3 (2^n-1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hl := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
  norm_num at hl
  omega

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.OddLinear

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.OddLinear
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

private theorem noncentral_outer_of_fusion (hZ : center L = ⊥)
    (hfus : ∀ k l : L, orderOf k = 2 → orderOf l = 2 → IsConj k l)
    (u v : normalizer (L : Set G))
    (hv2 : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ ∃ k : L, L.normalizerMonoidHom v = MulAut.conj k := by
  rintro ⟨l, hl⟩
  obtain ⟨hu2, k, hk, hkc⟩ := (action_twoCentral_iff u).mp hu
  have hord (w : normalizer (L : Set G)) (x : L)
      (hx : L.normalizerMonoidHom w = MulAut.conj x)
      (hw : orderOf (actionMap (L := L) le_rfl w) = 2) : orderOf x = 2 := by
    rw [← action_order w, hx] at hw
    exact (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot hZ) x).symm.trans hw
  obtain ⟨g, hg⟩ := isConj_iff.mp (hfus k l (hord u k hk hu2) (hord v l hl hv2))
  apply hv
  apply (action_twoCentral_iff v).mpr
  refine ⟨hv2, l, hl, ?_⟩
  let q := QuotientGroup.mk' (center L)
  have h := hkc.map (MulAut.conj (q g))
  have he : MulAut.conj (q g) (q k) = q l := by
    change q g * q k * (q g)⁻¹ = q l
    rw [← map_inv, ← map_mul, ← map_mul, hg]
  exact he ▸ h

omit [Finite G] in
private theorem pslTwo_fusion {p : ℕ} (hp : IsFermatOrMersennePrime p)
    (hp5 : 5 ≤ p) (hL : ClassicalGroup.IsPSL L 2 p)
    (k l : L) (hk : orderOf k = 2) (hl : orderOf l = 2) : IsConj k l := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp.1, hp.1.odd_of_ne_two (by omega), by omega, by simpa using hF⟩
  have hk2 : orderOf (e k) = 2 := (e.orderOf_eq k).trans hk
  have hl2 : orderOf (e l) = 2 := (e.orderOf_eq l).trans hl
  obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power F hodd
    (e k) (e l) ⟨by intro h; simp [h] at hk2, by simpa [hk2] using pow_orderOf_eq_one (e k)⟩
    ⟨by intro h; simp [h] at hl2, by simpa [hl2] using pow_orderOf_eq_one (e l)⟩
  apply isConj_iff.mpr
  refine ⟨e.symm g, e.injective ?_⟩
  simpa only [map_mul, map_inv, e.apply_symm_apply] using hg

omit [Finite G] in
private theorem pslThree_fusion (hL : ClassicalGroup.IsPSL L 3 3)
    (k l : L) (hk : orderOf k = 2) (hl : orderOf l = 2) : IsConj k l := by
  obtain ⟨e⟩ := OtherPreliminaries.equiv_pslThree_of_isPSL hL
  let f := e.trans Matrix.PSL3Three.equiv.symm
  obtain ⟨g, hg⟩ := isConj_iff.mp (Matrix.SL3.involutions_isConj (ZMod 3) (f k) (f l)
    ((f.orderOf_eq k).trans hk) ((f.orderOf_eq l).trans hl) (by decide))
  apply isConj_iff.mpr
  refine ⟨f.symm g, f.injective ?_⟩
  simpa only [map_mul, map_inv, f.apply_symm_apply] using hg

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.OddLinear

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.OddLinear
open Subgroup Theory.GroupTheory
private abbrev GLThree := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

private theorem glThree_residual_involution_unique (x y : pResidual 2 GLThree)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  have hu : IsPGroup 2 (ZMod 3)ˣ := IsPGroup.of_card (n := 1) (by
    norm_num [Nat.card_eq_fintype_card, ZMod.card_units, Nat.totient_prime Nat.prime_three])
  have hb : pResidual 2 (ZMod 3)ˣ = ⊥ :=
    le_bot_iff.mp (sInf_le ⟨inferInstance, hu.to_quotient ⊥⟩)
  have scalar (a : pResidual 2 GLThree) (ha : orderOf a = 2) : (a : GLThree) = -1 := by
    have hd : Matrix.GeneralLinearGroup.det (a : GLThree) = 1 := by
      have hm := map_pResidual_le 2 Matrix.GeneralLinearGroup.det
        (mem_map.mpr ⟨(a : GLThree), a.property, rfl⟩)
      rwa [hb, mem_bot] at hm
    apply (Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
      (by decide : (2 : ZMod 3) ≠ 0) (a : GLThree) ?_ hd).resolve_left
    · intro h
      have he : a = 1 := Subtype.ext h
      simp [he] at ha
    · exact congrArg Subtype.val (ha ▸ pow_orderOf_eq_one a)
  exact Subtype.ext ((scalar x hx).trans (scalar y hy).symm)

private theorem no_equiv_glThree_residual_aFour :
    ¬ Nonempty (pResidual 2 GLThree ≃* alternatingGroup (Fin 4)) := by
  rintro ⟨e⟩
  let x : alternatingGroup (Fin 4) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  let y : alternatingGroup (Fin 4) :=
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  have hx : orderOf x = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hy : orderOf y = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hxy : x ≠ y := by decide +kernel
  exact hxy (e.symm.injective (glThree_residual_involution_unique (e.symm x) (e.symm y)
    ((e.symm.orderOf_eq x).trans hx) ((e.symm.orderOf_eq y).trans hy)))

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.OddLinear

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.OddLinear
open Subgroup Theory.GroupTheory
open SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

private noncomputable def ordinaryResidualEquiv (hn : ¬ HasEvenLinearThreeType L) (w : G) :
    modifiedCentralizerResidual L w ≃* involutionTwoResidual L w :=
  MulEquiv.subgroupCongr (by rw [modifiedCentralizerResidual, if_neg hn])

private theorem outerRow_of_tables (tables : OddTwoTables)
    {F : Type} [Field F] [Finite F] {p : ℕ} (hF : Nat.card F = p)
    (hp : IsFermatOrMersennePrime p) (hp5 : 5 ≤ p)
    (a : MulAut PSL(2,F)) (ha : orderOf a = 2)
    (hoa : ¬ ∃ x, a = MulAut.conj x) : PSLTwoOuterRow p a := by
  by_cases hlarge : 7 < p
  · exact tables.large F p hF hp hlarge a ha hoa
  · have hpodd := hp.1.odd_of_ne_two (by omega)
    have hpmod := Nat.odd_iff.mp hpodd
    have hsmall : p = 5 ∨ p = 7 := by omega
    refine ⟨3, ?_, tables.small F (hF ▸ hsmall) a ha hoa⟩
    rcases hsmall with rfl | rfl <;> norm_num

/-- For the PSL₂ alternative, a noncentral actor is outer: all inner
involutions are conjugate to the given central one. -/
theorem pslTwo_noncentral_outer [Group.IsPerfect L] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hL : ClassicalGroup.IsPSL L 2 p)
    (u v : normalizer (L : Set G))
    (hv2 : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ ∃ k : L, L.normalizerMonoidHom v = MulAut.conj k :=
  noncentral_outer_of_fusion (OtherPreliminaries.OddLinear.pslTwo_center_eq_bot hL)
    (pslTwo_fusion hp (OtherPreliminaries.OddLinear.pslTwo_parameter_ge_five hp hL) hL)
    u v hv2 hu hv

/-- The same marking argument applies to the single inner involution class
of PSL₃(3). The statement concerns the action, not membership of v in L. -/
theorem pslThree_noncentral_outer (hL : ClassicalGroup.IsPSL L 3 3)
    (u v : normalizer (L : Set G))
    (hv2 : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ ∃ k : L, L.normalizerMonoidHom v = MulAut.conj k :=
  noncentral_outer_of_fusion (OtherPreliminaries.pslThree_center_eq_bot hL)
    (pslThree_fusion hL) u v hv2 hu hv

/-- The complete Fermat–Mersenne branch, including parameters five and seven.
The central residual is trivial, while the outer fixed group is not a two-group.
The order comparison excludes the exceptional modification. -/
theorem pslTwo_separation [Group.IsPerfect L] (tables : OddTwoTables) {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hL : ClassicalGroup.IsPSL L 2 p)
    (u v : normalizer (L : Set G))
    (hv2 : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  have hp5 := OtherPreliminaries.OddLinear.pslTwo_parameter_ge_five hp hL
  have hvo := pslTwo_noncentral_outer hp hL u v hv2 hu hv
  have hn := pslTwo_not_evenLinearThree hp hL
  obtain ⟨hu2, k, hk, _⟩ := (action_twoCentral_iff u).mp hu
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  let a := MulAut.congr e (L.normalizerMonoidHom u)
  let b := MulAut.congr e (L.normalizerMonoidHom v)
  have ha : orderOf a = 2 := ((MulAut.congr e).orderOf_eq _).trans
    ((action_order u).trans hu2)
  have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq _).trans
    ((action_order v).trans hv2)
  have hai : ∃ x, a = MulAut.conj x :=
    (MulAut.congr_inner_iff e _).mpr ⟨k, hk⟩
  have hbo : ¬ ∃ x, b = MulAut.conj x :=
    fun h => hvo ((MulAut.congr_inner_iff e _).mp h)
  obtain ⟨S, hS⟩ := OtherPreliminaries.OddLinear.pslTwo_inner_involution hF hp hp5 a ha hai
  have htwo : IsPGroup 2 a.fixedSubgroup := hS ▸ S.isPGroup'
  have hr : pResidual 2 a.fixedSubgroup = ⊥ :=
    le_bot_iff.mp (sInf_le ⟨inferInstance, htwo.to_quotient ⊥⟩)
  let ei := fullFixedResidualEquiv u (MulAut.fixedSubgroupCongr e _)
  let eo := fullFixedResidualEquiv v (MulAut.fixedSubgroupCongr e _)
  rintro ⟨f⟩
  let f' := (ordinaryResidualEquiv hn u.val).symm.trans
    (f.trans (ordinaryResidualEquiv hn v.val))
  have eab : pResidual 2 a.fixedSubgroup ≃* pResidual 2 b.fixedSubgroup :=
    ei.symm.trans (f'.trans eo)
  have hrb : pResidual 2 b.fixedSubgroup = ⊥ := by
    apply (eq_bot_iff_card _).mpr
    rw [← Nat.card_congr eab.toEquiv]
    exact (eq_bot_iff_card _).mp hr
  have hi : Function.Injective (QuotientGroup.mk' (pResidual 2 b.fixedSubgroup)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rwa [QuotientGroup.ker_mk']
  exact (outerRow_of_tables tables hF hp hp5 b hb hbo).not_twoGroup
    (hp.1.odd_of_ne_two (by omega)) hp5
    ((isPGroup_quotient_pResidual 2).of_injective _ hi)

/-- PSL₃(3): the central residual embeds in determinant-one GL₂(3), which
has a unique involution. The outer residual is A₄, with distinct involutions. -/
theorem pslThree_separation (hL : ClassicalGroup.IsPSL L 3 3)
    (table : ∀ a : MulAut Matrix.PSL3Three.PSL, orderOf a = 2 →
      (¬ ∃ x, a = MulAut.conj x) → Nonempty (a.fixedSubgroup ≃* Equiv.Perm (Fin 4)))
    (u v : normalizer (L : Set G))
    (hv2 : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  have hvo := pslThree_noncentral_outer hL u v hv2 hu hv
  have hn := pslThree_not_evenLinearThree hL
  obtain ⟨hu2, k, hk, _⟩ := (action_twoCentral_iff u).mp hu
  obtain ⟨ei⟩ := OtherPreliminaries.pslThree_inner_involution hL _
    ((action_order u).trans hu2) ⟨k, hk⟩
  obtain ⟨e⟩ := OtherPreliminaries.equiv_pslThree_of_isPSL hL
  let b := MulAut.congr e (L.normalizerMonoidHom v)
  have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq _).trans
    ((action_order v).trans hv2)
  have hbo : ¬ ∃ x, b = MulAut.conj x :=
    fun h => hvo ((MulAut.congr_inner_iff e _).mp h)
  obtain ⟨eo⟩ := table b hb hbo
  let eri := fullFixedResidualEquiv u ei
  let ero := (fullFixedResidualEquiv v ((MulAut.fixedSubgroupCongr e _).trans eo)).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.twoResidual_eq_alternating (Fin 4)))
  rintro ⟨f⟩
  let f' := (ordinaryResidualEquiv hn u.val).symm.trans
    (f.trans (ordinaryResidualEquiv hn v.val))
  exact no_equiv_glThree_residual_aFour ⟨eri.symm.trans (f'.trans ero)⟩

/-- Residual separation for the full (E2)(ii) alternative. Only the exact
universal outer fixed-group tables remain inputs. Source ambient involution,
odd-core and model-exclusion hypotheses may be supplied by the consumer;
this stronger comparison needs none of them. -/
theorem separation [Group.IsPerfect L] (twoTables : OddTwoTables)
    (threeTable : ∀ a : MulAut Matrix.PSL3Three.PSL, orderOf a = 2 →
      (¬ ∃ x, a = MulAut.conj x) → Nonempty (a.fixedSubgroup ≃* Equiv.Perm (Fin 4)))
    (hfamily : ClassicalGroup.IsPSL L 3 3 ∨
      ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p)
    (u v : normalizer (L : Set G))
    (hv2 : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  rcases hfamily with hL | ⟨p, hp, hL⟩
  · exact pslThree_separation hL threeTable u v hv2 hu hv
  · exact pslTwo_separation twoTables hp hL u v hv2 hu hv

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.OddLinear
