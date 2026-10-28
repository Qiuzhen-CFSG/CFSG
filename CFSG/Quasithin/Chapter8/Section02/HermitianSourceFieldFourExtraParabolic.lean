module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourExtraCenter
public import Theory.GroupTheory.PerfectNormalizerCoreQuotient
public import Theory.GroupTheory.CyclicNormalCentralizer

/-!
# The intrinsic extraspecial parabolic at the Hermitian four-space

A proper subgroup between T and XT has radical image contained in the
Frattini subgroup of X/O₂(X). For an extraspecial radical this is its cyclic
center. A perfect residual R fixes that center, so its commutator with the
full center preimage lies in O₂(X). The actual normalization of R by O₂(X)
then recovers normalization of R from the quotient, using the solvable
residual of R O₂(X).

Consequently every proper overgroup of T in XT normalizes R. When X does
not normalize R, XT is intrinsically a minimal parabolic, with unique
maximal overgroup XT intersect N_G(R). The companion Chapter 12 module
proves the nonnormalization premise for the original residual and radical,
and applies the result on the literal tensor. This does not identify that
maximal subgroup with XT intersect M: that comparison, actual H-star
placement, whole odd-normalizer control and the final source exclusion
remain to be established.

Source: Aschbacher--Smith 1.3.1--3, B.6.1 and the radical paragraph of
8.2.7, printed pp.508--509,112,717--718, refs/quasithin.pdf
(1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- The full preimage in X of Z(X/O₂(X)), embedded in the original group. -/
@[expose] def radicalCenterPreimage (X : Subgroup G) : Subgroup G :=
  ((center (XiQuotient X)).comap (QuotientGroup.mk' (pCore 2 X))).map X.subtype

omit [Finite G] in
private theorem center_preimage_commutator
    (X R : Subgroup G) [Group.IsPerfect R]
    (hRX : R ≤ normalizer (X : Set G)) [IsCyclic (center (XiQuotient X))] :
    ⁅R,radicalCenterPreimage X⁆ ≤ X.pCoreIn 2 := by
  let _ := conjMulDistribMulActionOfLeNormalizer R X hRX
  let a := (quotientAut (pCore 2 X)).comp (MulDistribMulAction.toMulAut R X)
  let f := (MulAut.characteristic (center (XiQuotient X))).comp a
  let _ := (IsCyclic.mulAutMulEquiv (center (XiQuotient X))).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv (center (XiQuotient X))).injective
  have hf : ∀ r : R, f r = 1 := by
    intro r
    exact Abelianization.commutator_subset_ker f (Group.IsPerfect.mem_commutator (g := r))
  apply commutator_le.mpr
  rintro r hr z ⟨x,hx,rfl⟩
  let r' : R := ⟨r,hr⟩
  let y : X := (r' • x) * x⁻¹
  refine ⟨y,?_,rfl⟩
  apply (QuotientGroup.eq_one_iff y).mp
  have hh := congrArg (fun b : MulAut (center (XiQuotient X)) =>
    (b ⟨QuotientGroup.mk' (pCore 2 X) x,hx⟩).val) (hf r')
  change a r' (QuotientGroup.mk' (pCore 2 X) x) = QuotientGroup.mk' (pCore 2 X) x at hh
  simp only [a,MonoidHom.comp_apply,quotientAut_apply_mk] at hh
  change QuotientGroup.mk' (pCore 2 X) (r' • x) = QuotientGroup.mk' (pCore 2 X) x at hh
  change QuotientGroup.mk' (pCore 2 X) ((r' • x) * x⁻¹) = 1
  rw [map_mul,map_inv,hh,mul_inv_cancel]

private theorem perfect_normalized_of_core_commutator
    (X R Z : Subgroup G) [Group.IsPerfect R]
    (hRX : R ≤ normalizer (X : Set G)) (hZX : Z ≤ X)
    (hQR : X.pCoreIn 2 ≤ normalizer (R : Set G))
    (hc : ⁅R,Z⁆ ≤ X.pCoreIn 2) : Z ≤ normalizer (R : Set G) := by
  let H := normalizer (X : Set G)
  let Q := (X.pCoreIn 2).subgroupOf H
  let A := R.subgroupOf H
  let B := Z.subgroupOf H
  have hQH : X.pCoreIn 2 ≤ H := (pCoreIn_le 2 X).trans X.le_normalizer
  have hZH : Z ≤ H := hZX.trans X.le_normalizer
  let : Q.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRX).symm.toMonoidHom)
    (subgroupOfEquivOfLe hRX).symm.surjective
  have hQA : Q ≤ normalizer (A : Set H) := by
    apply le_normalizer_iff.mpr
    intro q hq a ha
    exact (mem_normalizer_iff.mp (hQR hq) (a : G)).mp ha
  have hAB : ⁅A,B⁆ ≤ Q := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hZH,
      map_subgroupOf_eq_of_le hQH]
    exact hc
  have hn := normalizes_perfect_of_commutator_le A Q B
    (isPGroup_pCoreIn 2 X).comap_subtype hQA hAB
  apply le_normalizer_iff.mpr
  intro z hz r hr
  exact (mem_normalizer_iff.mp (hn (show (⟨z,hZH hz⟩ : H) ∈ B from hz))
    (⟨r,hRX hr⟩ : H)).mp hr

/-- The full preimage of the cyclic extraspecial center normalizes the
perfect residual when the original radical two-core does. -/
theorem radicalCenterPreimage_normalizes
    (X R : Subgroup G) [Group.IsPerfect R]
    (hRX : R ≤ normalizer (X : Set G)) (hQR : X.pCoreIn 2 ≤ normalizer (R : Set G))
    [IsCyclic (center (XiQuotient X))] :
    radicalCenterPreimage X ≤ normalizer (R : Set G) :=
  perfect_normalized_of_core_commutator X R _ hRX (map_subtype_le _) hQR
    (center_preimage_commutator X R hRX)

private theorem xi_intermediate_center_or_full
    {T X Y : Subgroup G} (hX : XiMember T X)
    {p : ℕ} [Fact p.Prime] [IsExtraspecial p (XiQuotient X)]
    (hcore : X.pCoreIn 2 ≤ T) (hTY : T ≤ Y) (hY : Y ≤ X ⊔ T) :
    Y ≤ radicalCenterPreimage X ⊔ T ∨ X ≤ Y := by
  let I := Y.subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := QuotientGroup.mk' (frattini (XiQuotient X))
  let A := (I.map q).map r
  have hstable : ∀ t : T, ∀ a ∈ A, xiFrattiniAction T X hX.invariant t a ∈ A := by
    rintro t a ⟨b,⟨x,hx,rfl⟩,rfl⟩
    let z : X := ⟨(t : G)*x*(t : G)⁻¹,
      (mem_normalizer_iff.mp (hX.invariant t.property) x).mp x.property⟩
    have hz : z ∈ I := Y.mul_mem (Y.mul_mem (hTY t.property) hx)
      (Y.inv_mem (hTY t.property))
    refine ⟨q z,⟨z,hz,rfl⟩,?_⟩
    simp only [r,q,xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    rfl
  rcases hX.irreducible A hstable with hb | ht
  · left
    have hi : I ≤ (center (XiQuotient X)).comap q := by
      intro x hx
      have hz : r (q x) = 1 := mem_bot.mp (hb ▸ mem_map_of_mem r (mem_map_of_mem q hx))
      have hq := (QuotientGroup.eq_one_iff _).mp hz
      rwa [IsExtraspecial.frattini_eq_center (p := p)] at hq
    intro y hy
    have hyt := hY hy
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hX.invariant] at hyt
    obtain ⟨x,hx,t,ht,hxt⟩ := hyt
    have hxY : x ∈ Y := by
      have hh : x = y*t⁻¹ := by rw [←hxt,mul_inv_cancel_right]
      rw [hh]
      exact Y.mul_mem hy (Y.inv_mem (hTY ht))
    have hxZ : x ∈ radicalCenterPreimage X := ⟨⟨x,hx⟩,hi hxY,rfl⟩
    rw [←hxt]
    exact (radicalCenterPreimage X ⊔ T).mul_mem (mem_sup_left hxZ) (mem_sup_right ht)
  · right
    have hI : I.map q = ⊤ := by
      apply frattini_nongenerating
      have hh := congrArg (comap r) ht
      simpa only [A,comap_map_eq,r,QuotientGroup.ker_mk',comap_top] using hh
    have hsup : I ⊔ pCore 2 X = ⊤ := by
      have hh := congrArg (comap q) hI
      simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
    have hc : pCore 2 X ≤ I := fun x hx => hTY (hcore ⟨x,hx,rfl⟩)
    rw [sup_eq_left.mpr hc] at hsup
    exact subgroupOf_eq_top.mp hsup

/-- Every proper overgroup of the original Sylow in an extraspecial radical
join normalizes R; the two-core is retained in the center preimage. -/
theorem extraspecial_radical_proper_overgroup_normalizes
    (T : Sylow 2 G) {X R : Subgroup G} (hX : XiMember (T : Subgroup G) X)
    [Group.IsPerfect R] (hRX : R ≤ normalizer (X : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {p : ℕ} [Fact p.Prime] [IsExtraspecial p (XiQuotient X)]
    (Y : Subgroup G) (hTY : (T : Subgroup G) ≤ Y) (hY : Y < X ⊔ (T : Subgroup G)) :
    Y ≤ normalizer (R : Set G) := by
  have hc := hX.pCoreIn_le_of_isSylowIn
    (show IsSylowIn 2 (T : Subgroup G) (X ⊔ (T : Subgroup G)) from
      ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩)
  rcases xi_intermediate_center_or_full (p := p) hX hc hTY hY.le with hz | hx
  · let : IsCyclic (center (XiQuotient X)) :=
      isCyclic_of_prime_card (IsExtraspecial.center_order_p p (XiQuotient X))
    exact hz.trans (sup_le (radicalCenterPreimage_normalizes X R hRX (hc.trans hTR)) hTR)
  · exact (hY.not_ge (sup_le hx hTY)).elim

private theorem xi_join_not_normalizes_sylow
    (T : Sylow 2 G) {X : Subgroup G} (hX : XiMember (T : Subgroup G) X) :
    ¬ X ⊔ (T : Subgroup G) ≤ normalizer (T : Set G) := by
  intro hn
  obtain ⟨p,hp,ho,hq⟩ := hX.odd_quotient
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p X := Classical.arbitrary _
  let Y := (P : Subgroup X).map X.subtype
  let S := (T : Subgroup G) ⊓ normalizer (Y : Set G)
  have hTY : Disjoint (T : Subgroup G) Y := T.isPGroup'.disjoint_of_coprime
    (P.isPGroup'.map X.subtype) (Nat.coprime_two_left.mpr ho)
  have hYN : Y ≤ normalizer (T : Set G) :=
    (map_subtype_le (P : Subgroup X)).trans (le_sup_left.trans hn)
  have hYT : ⁅Y,(T : Subgroup G)⁆ ≤ (T : Subgroup G) :=
    le_normalizer_iff_commutator_le_right.mp hYN
  have hYS : ⁅Y,S⁆ ≤ Y := le_normalizer_iff_commutator_le_left.mp
    (show S ≤ normalizer (Y : Set G) from inf_le_right)
  have hc : ⁅Y,S⁆ = ⊥ := bot_unique ((le_inf
    ((commutator_mono le_rfl (show S ≤ (T : Subgroup G) from inf_le_left)).trans hYT)
    hYS).trans hTY.le_bot)
  have he : Y = ⊥ := by
    have hg := lemma_1_3_2_4 hX
      (show IsSylowIn 2 (T : Subgroup G) (X ⊔ (T : Subgroup G)) from
        ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩) ho hq P
    exact hg.trans (bot_unique ((commutator_mono le_rfl (map_subtype_le _)).trans hc.le))
  apply hX.sylow_not_isCyclic ho hq P
  change IsCyclic Y
  rw [he]
  infer_instance

/-- The extraspecial radical join is intrinsically a minimal parabolic.
Its unique maximal overgroup of T is its intersection with N_G(R).
No identification of this maximal subgroup with the original M is assumed. -/
theorem extraspecial_radical_parabolic_at_residual
    (T : Sylow 2 G) {X R : Subgroup G} (hX : XiMember (T : Subgroup G) X)
    [Group.IsPerfect R] (hRX : R ≤ normalizer (X : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {p : ℕ} [Fact p.Prime] [IsExtraspecial p (XiQuotient X)]
    (hout : ¬ X ≤ normalizer (R : Set G)) :
    let H := X ⊔ (T : Subgroup G)
    ChapterB.IsMinimalParabolicOver T H ∧
      (T : Subgroup G) ≤ H ⊓ normalizer (R : Set G) ∧
      H ⊓ normalizer (R : Set G) ⋖ H ∧
      ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Y < H →
        Y ≤ H ⊓ normalizer (R : Set G) := by
  let H := X ⊔ (T : Subgroup G)
  let B := H ⊓ normalizer (R : Set G)
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hTR
  have hBH : B < H := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hout (le_sup_left.trans (he ▸ (show B ≤ normalizer (R : Set G) from inf_le_right))))
  have hm (Y : Subgroup G) (hTY : (T : Subgroup G) ≤ Y) (hY : Y < H) : Y ≤ B :=
    le_inf hY.le (extraspecial_radical_proper_overgroup_normalizes (p := p) T hX hRX hTR Y hTY hY)
  have hcov : B ⋖ H := ⟨hBH,fun Y hBY hYH => hBY.not_ge (hm Y (hTB.trans hBY.le) hYH)⟩
  refine ⟨⟨⟨hTB.trans_lt hBH,B,⟨hTB,hcov⟩,?_⟩,xi_join_not_normalizes_sylow T hX⟩,hTB,hcov,hm⟩
  intro Y hY
  exact ((hY.2.eq_or_eq (hm Y hY.1 hY.2.lt) hBH.le).resolve_right hBH.ne).symm

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
