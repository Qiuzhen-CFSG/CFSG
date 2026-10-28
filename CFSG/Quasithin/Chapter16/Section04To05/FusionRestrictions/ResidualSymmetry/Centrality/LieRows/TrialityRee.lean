module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional.Rows
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.Roots
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Separating the triality, Ree, and Tits centrality rows

For genuine binary triality and positive Ree parameters, the long-root fixed
centralizer is two-perfect. A central actor therefore has a fixed two-residual
containing the full Sylow two-part. Equality of residual two-parts forces the
other fixed group to contain a Sylow subgroup. The earlier Sylow-fixer theorem
then makes its actor inner, and the fixed-group index proves two-centrality.
For Ree, the supplied inner--field coverage and odd field degree already imply
innerness of every involutory actor.

The triality table is the earlier `TrialityInvolutionTable`: it retains both
actual root curves, the cubic coefficient action, f = 1, and the smaller
*derived* fixed groups. The comparison needs no orders or simplicity proofs
for those smaller groups. The extra root inputs below are individual markings,
an exact long-root residual identity, and the triality part of 16.1.6; none is
a comparison or centrality-transfer premise. The centerless input is precisely
the covering restriction of 16.1.2 for these three families.

The separate Tits case retains the full binary Ree action on its derived group.
Its root fixed groups have orders 2^11 * 5 and 2^9 * 3. Taking either O² or O³
preserves their five-parts, which separates their modified residuals. The
O³ modification is used literally throughout, with no family-disjointness
assumption. Universal earlier tables and their model calculations remain inputs
to these conditional comparisons; this module does not prove those tables or
complete source 16.5.6.

Sources: Aschbacher--Smith, combined manuscript (1 March 2004), 16.1.2--4,6,
printed pp.1170--1172, and 16.5.5--6(4), p.1197 (`refs/quasithin.pdf`).
The Tits fixed orders are Parrott (1972), theorem on p.672 and §4 on p.682,
`refs/original/n-group-global/parrott-tits-characterization-1972.pdf`.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter16.Intersections
open ResidualSymmetry ResidualSymmetry.Centrality ResidualSymmetry.Centrality.LieRows

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.TrialityRee

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem fixed_index (hZ : center H = ⊥) (a : MulAut H) :
    a.fixedSubgroup.index = (relativeCentralizer (MulAut.innerSubgroup H) a).index := by
  let e := MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hZ)
  have he : (relativeCentralizer (MulAut.innerSubgroup H) a).comap e.toMonoidHom =
      a.fixedSubgroup := by
    ext x
    rw [MulAut.mem_fixedSubgroup]
    change MulAut.conj x ∈ centralizer ({a} : Set (MulAut H)) ↔ a x = x
    rw [mem_centralizer_singleton_iff]
    have hc : MulAut.conj (a x) * a = a * MulAut.conj x := by
      ext y
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    constructor
    · intro hx
      apply MulAut.conj_injective_of_center_eq_bot hZ
      exact mul_right_cancel (hc.trans hx.symm)
    · intro hx
      rw [hx] at hc
      exact hc
  rw [← he]
  exact index_comap_of_surjective _ e.surjective

private theorem valuation_card_index (K : Subgroup H) :
    padicValNat 2 (Nat.card K) + padicValNat 2 K.index = padicValNat 2 (Nat.card H) := by
  rw [← padicValNat.mul Nat.card_pos.ne' K.index_ne_zero_of_finite, K.card_mul_index]

private theorem fixed_odd_index_of_residual_eq (hZ : center H = ⊥)
    (a b : MulAut H) (ha : IsTwoCentralIn (MulAut.innerSubgroup H) a)
    (hp : pResidual 2 a.fixedSubgroup = ⊤)
    (he : padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) =
      padicValNat 2 (Nat.card (pResidual 2 b.fixedSubgroup))) : Odd b.fixedSubgroup.index := by
  have haodd : Odd a.fixedSubgroup.index := by
    rw [fixed_index hZ a]
    exact (twoCentral_iff_odd_index.mp ha).2.2
  have hai : padicValNat 2 a.fixedSubgroup.index = 0 :=
    padicValNat.eq_zero_of_not_dvd (by simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using haodd)
  have hac := valuation_card_index a.fixedSubgroup
  have hbc := valuation_card_index b.fixedSubgroup
  have hbr := valuation_card_index (pResidual 2 b.fixedSubgroup)
  rw [hp, card_top] at he
  have hbi : padicValNat 2 b.fixedSubgroup.index = 0 := by omega
  apply Nat.not_even_iff_odd.mp
  intro hb
  have := one_le_padicValNat_of_dvd b.fixedSubgroup.index_ne_zero_of_finite (even_iff_two_dvd.mp hb)
  omega

private theorem exists_fixed_sylow (a : MulAut H) (hi : Odd a.fixedSubgroup.index) :
    ∃ P : Sylow 2 H, ∀ x ∈ P, a x = x := by
  let P : Sylow 2 a.fixedSubgroup := Classical.choice inferInstance
  let Q : Subgroup H := (P : Subgroup a.fixedSubgroup).map a.fixedSubgroup.subtype
  have hQ : ¬ 2 ∣ Q.index := by
    rw [show Q.index = (P : Subgroup a.fixedSubgroup).index * a.fixedSubgroup.index from
      index_map_subtype _]
    intro h
    rcases Nat.prime_two.dvd_mul.mp h with h | h
    · exact P.not_dvd_index h
    · exact (Nat.not_even_iff_odd.mpr hi) (even_iff_two_dvd.mpr h)
  let S := (P.isPGroup'.map a.fixedSubgroup.subtype).toSylow hQ
  refine ⟨S, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  exact (MulAut.mem_fixedSubgroup a y).mp y.property

private theorem central_of_residual_eq (hZ : center H = ⊥)
    (a b : MulAut H) (ha : IsTwoCentralIn (MulAut.innerSubgroup H) a)
    (hb : orderOf b = 2)
    (hp : pResidual 2 a.fixedSubgroup = ⊤)
    (fixers : ∀ (P : Sylow 2 H), (∀ x ∈ P, b x = x) → ∃ x, b = MulAut.conj x)
    (he : padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) =
      padicValNat 2 (Nat.card (pResidual 2 b.fixedSubgroup))) :
    IsTwoCentralIn (MulAut.innerSubgroup H) b := by
  have hi := fixed_odd_index_of_residual_eq hZ a b ha hp he
  obtain ⟨P, hP⟩ := exists_fixed_sylow b hi
  obtain ⟨x, hx⟩ := fixers P hP
  apply twoCentral_iff_odd_index.mpr
  refine ⟨hb, ⟨x, hx.symm⟩, ?_⟩
  rwa [← fixed_index hZ b]

open SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional

/-- The precise additional long/short-root and Sylow-fixer clauses consumed
from 16.1.4 and 16.1.6, on the genuine graph-field carrier. -/
structure TrialityRootInputs (f : ℕ) (hf : 0 < f) : Prop where
  long_residual : ∀ x : Triality.Standard.BinaryCarrier f hf,
    Triality.Standard.EvenInvolutionGeometry.IsLongRootInvolution f hf x →
      pResidual 2 (MulAut.conj x).fixedSubgroup = ⊤
  short_noncentral : ∀ x : Triality.Standard.BinaryCarrier f hf,
    Triality.Standard.EvenInvolutionGeometry.IsShortRootInvolution f hf x →
      ¬ IsTwoCentralIn (MulAut.innerSubgroup _) (MulAut.conj x)
  sylow_fixers : ∀ (a : MulAut (Triality.Standard.BinaryCarrier f hf)), orderOf a = 2 →
    ∀ P : Sylow 2 (Triality.Standard.BinaryCarrier f hf),
      (∀ x ∈ P, a x = x) → ∃ x, a = MulAut.conj x

/-- Root coverage, the long-root residual identity, and the individual short
marking. The comparison requests this only for positive Ree parameters. -/
structure ReeRootInputs (m : ℕ) : Prop where
  roots : ∀ x : ReeF4.Model m, orderOf x = 2 →
    ReeF4.EvenInvolutionGeometry.IsLongRootInvolution x ∨
      ReeF4.EvenInvolutionGeometry.IsShortRootInvolution x
  long_residual : ∀ x : ReeF4.Model m,
    ReeF4.EvenInvolutionGeometry.IsLongRootInvolution x →
      pResidual 2 (MulAut.conj x).fixedSubgroup = ⊤
  short_noncentral : ∀ x : ReeF4.Model m,
    ReeF4.EvenInvolutionGeometry.IsShortRootInvolution x →
      ¬ IsTwoCentralIn (MulAut.innerSubgroup _) (MulAut.conj x)

/-- Individual root markings and full fixed-group orders on the actual Tits
carrier; the full binary Ree actor coverage is supplied separately. -/
structure TitsRootInputs : Prop where
  long_central : ∀ x : Tits.ParrottGroup, Tits.InvolutionRootGeometry.IsLongRoot x →
    IsTwoCentralIn (MulAut.innerSubgroup _) (MulAut.conj x)
  short_noncentral : ∀ x : Tits.ParrottGroup, Tits.InvolutionRootGeometry.IsShortRoot x →
    ¬ IsTwoCentralIn (MulAut.innerSubgroup _) (MulAut.conj x)
  long_fixed_card : ∀ x : Tits.ParrottGroup, Tits.InvolutionRootGeometry.IsLongRoot x →
    Nat.card (MulAut.conj x).fixedSubgroup = 2 ^ 11 * 5
  short_fixed_card : ∀ x : Tits.ParrottGroup, Tits.InvolutionRootGeometry.IsShortRoot x →
    Nat.card (MulAut.conj x).fixedSubgroup = 2 ^ 9 * 3

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

private noncomputable def centerlessModelEquiv (hZ : center L = ⊥) {S : Type*} [Group S]
    (e : (L ⧸ center L) ≃* S) : L ≃* S :=
  (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e

omit [Finite G] in
private theorem model_center {S : Type*} [Group S] (hZ : center L = ⊥)
    (e : L ≃* S) : center S = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [← Nat.card_congr (centerCongr e).toEquiv, hZ, card_bot]

private theorem central_inner {S : Type*} [Group S] [Finite S] {a : MulAut S}
    (h : IsTwoCentralIn (MulAut.innerSubgroup S) a) : ∃ x, a = MulAut.conj x := by
  obtain ⟨x, hx⟩ := (twoCentral_iff_odd_index.mp h).2.1
  exact ⟨x, hx.symm⟩

private theorem separation_of_root_fixed {S : Type*} [Group S] [Finite S]
    (hZ : center L = ⊥) (e : L ≃* S)
    (u v : normalizer (L : Set G))
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v))
    (hp : pResidual 2 (fullModelAction e (actionMap le_rfl u)).fixedSubgroup = ⊤)
    (fixers : ∀ P : Sylow 2 S,
      (∀ x ∈ P, fullModelAction e (actionMap le_rfl v) x = x) →
        ∃ x, fullModelAction e (actionMap le_rfl v) = MulAut.conj x) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  rintro ⟨d⟩
  apply hv
  apply (fullModelAction_twoCentral_iff e _).mp
  exact central_of_residual_eq (model_center hZ e) _ _
    ((fullModelAction_twoCentral_iff e _).mpr hu)
    ((orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hv2)
    hp fixers (fixedResidual_twoValuation_eq e u v d)

/-- Genuine triality separation, including f = 1 and every field row of the
earlier table. The Sylow argument avoids computing smaller-model orders. -/
theorem triality_separation (table : TrialityInvolutionTable)
    (root : ∀ (f : ℕ) (hf : 0 < f), TrialityRootInputs f hf)
    (hZ : center L = ⊥) {f : ℕ} (hf : 1 ≤ f)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ f) (L ⧸ center L))
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  obtain ⟨eq⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f hf).mp hmodel
  let e := centerlessModelEquiv hZ eq
  let a := fullModelAction e (actionMap le_rfl u)
  let b := fullModelAction e (actionMap le_rfl v)
  have ha2 : orderOf a = 2 :=
    (orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hu2
  have hb2 : orderOf b = 2 :=
    (orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hv2
  have ha : IsTwoCentralIn (MulAut.innerSubgroup _) a :=
    (fullModelAction_twoCentral_iff e _).mpr hu
  obtain ⟨x, hx, he, _⟩ := (table f hf).inner_root a ha2 (central_inner ha)
  have hp : pResidual 2 a.fixedSubgroup = ⊤ := by
    rcases hx with hx | hx
    · rw [he]
      exact (root f hf).long_residual x hx
    · exact ((root f hf).short_noncentral x hx (he ▸ ha)).elim
  exact separation_of_root_fixed hZ e u v hv2 hu hv hp
    (fun P hP => (root f hf).sylow_fixers b hb2 P hP)

/-- Positive Ree separation. Odd field degree removes the field part of the
actual involutory actor; no Tits endpoint is folded into this family. -/
theorem ree_separation (table : ReeInvolutionTable)
    (root : ∀ m : ℕ, 1 ≤ m → ReeRootInputs m)
    (hZ : center L = ⊥) {m : ℕ} (hm : 1 ≤ m)
    (eq : (L ⧸ center L) ≃* ReeF4.Model m)
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  let e := centerlessModelEquiv hZ eq
  let a := fullModelAction e (actionMap le_rfl u)
  let b := fullModelAction e (actionMap le_rfl v)
  have ha2 : orderOf a = 2 :=
    (orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hu2
  have hb2 : orderOf b = 2 :=
    (orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hv2
  have ha : IsTwoCentralIn (MulAut.innerSubgroup _) a :=
    (fullModelAction_twoCentral_iff e _).mpr hu
  obtain ⟨x, he⟩ := central_inner ha
  have hx2 : orderOf x = 2 := by
    rw [he, MulAut.conj_orderOf_of_center_eq_bot (model_center hZ e)] at ha2
    exact ha2
  have hp : pResidual 2 a.fixedSubgroup = ⊤ := by
    rcases (root m hm).roots x hx2 with hx | hx
    · rw [he]
      exact (root m hm).long_residual x hx
    · exact ((root m hm).short_noncentral x hx (he ▸ ha)).elim
  obtain ⟨y, k, hk⟩ := table m hm b hb2
  obtain ⟨z, hz⟩ := ReeF4.Parabolics.OuterLocal.inner_of_twoPower_of_inner_field
    m b y k 1 hk (by simpa only [pow_one, hb2] using pow_orderOf_eq_one b)
  exact separation_of_root_fixed hZ e u v hv2 hu hv hp (fun _ _ => ⟨z, hz.symm⟩)

private theorem modified_fiveValuation (u : G) :
    padicValNat 5 (Nat.card (modifiedCentralizerResidual L u)) =
      padicValNat 5 (Nat.card (involutionTwoResidual L u)) := by
  classical
  unfold modifiedCentralizerResidual
  split_ifs
  · rw [card_map_of_injective (subtype_injective _)]
    exact pResidual_card_padicValNat 5 3 (by decide)
  · rfl

/-- Tits separation through the actual full binary Ree derived action. The
fixed-group five-parts survive both residual operations in Notation 16.5.5. -/
theorem tits_separation (table : TitsInvolutionInputs)
    (root : TitsRootInputs) (hZ : center L = ⊥)
    (eq : (L ⧸ center L) ≃* Tits.ParrottGroup)
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) := by
  let e := centerlessModelEquiv hZ eq
  let a := fullModelAction e (actionMap le_rfl u)
  let b := fullModelAction e (actionMap le_rfl v)
  have ha2 : orderOf a = 2 :=
    (orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hu2
  have hb2 : orderOf b = 2 :=
    (orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hv2
  have ha : IsTwoCentralIn (MulAut.innerSubgroup _) a :=
    (fullModelAction_twoCentral_iff e _).mpr hu
  have hb : ¬ IsTwoCentralIn (MulAut.innerSubgroup _) b :=
    fun h => hv ((fullModelAction_twoCentral_iff e _).mp h)
  have classify := Tits.InvolutionRootGeometry.involution_inner_root_of_binary_coverage
    table.derived_action table.involutions
  obtain ⟨x, he, hx⟩ := classify a (ha2 ▸ pow_orderOf_eq_one a)
    (fun h => by simp [h] at ha2)
  obtain ⟨y, hf, hy⟩ := classify b (hb2 ▸ pow_orderOf_eq_one b)
    (fun h => by simp [h] at hb2)
  have hxlong : Tits.InvolutionRootGeometry.IsLongRoot x :=
    hx.resolve_right (fun h => root.short_noncentral x h (he ▸ ha))
  have hyshort : Tits.InvolutionRootGeometry.IsShortRoot y :=
    hy.resolve_left (fun h => hb (hf.symm ▸ root.long_central y h))
  rintro ⟨d⟩
  have hcard : padicValNat 5 (Nat.card (pResidual 2 a.fixedSubgroup)) =
      padicValNat 5 (Nat.card (pResidual 2 b.fixedSubgroup)) := by
    change padicValNat 5 (Nat.card (pResidual 2
      (fullModelAction e (actionMap le_rfl u)).fixedSubgroup)) =
      padicValNat 5 (Nat.card (pResidual 2
      (fullModelAction e (actionMap le_rfl v)).fixedSubgroup))
    rw [← Nat.card_congr (fullResidualEquiv e u).toEquiv,
      ← Nat.card_congr (fullResidualEquiv e v).toEquiv,
      ← modified_fiveValuation, ← modified_fiveValuation, Nat.card_congr d.toEquiv]
  rw [pResidual_card_padicValNat 5 2 (by decide),
    pResidual_card_padicValNat 5 2 (by decide), he, hf,
    root.long_fixed_card x hxlong, root.short_fixed_card y hyshort] at hcard
  have hl : padicValNat 5 (2 ^ 11 * 5) = 1 := by
    rw [padicValNat.mul (by decide) (by decide),
      padicValNat_prime_prime_pow 11 (by decide), padicValNat_self, zero_add]
  have hr : padicValNat 5 (2 ^ 9 * 3) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by decide)
  omega

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.TrialityRee
