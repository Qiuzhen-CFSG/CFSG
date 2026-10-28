module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The literal even-component quotient and its centralizer numerics

The index-at-most-two quaternion extension has order 1152 or 2304. The
component's intrinsic two-core is exactly the kernel of its map into
C_G(d)/<d>, so its two-core quotient embeds in that original quotient.
The order-960 block forces 480 to divide the component quotient's order.
The same z maps to an involution there and fixes a full Sylow two-subgroup.
Both even alternatives of 1.1.5 give a simple Lie model on this quotient.

These are reductions for the final model inspection, not that inspection.
In particular, a faithful action of the ambient quotient centralizer is
still required before using an automorphism-centralizer order bound.
Source: Aschbacher--Smith, 14.3.20, printed p.998, and 1.1.5(3)(a--b),
printed pp.501--503, `refs/quasithin.pdf`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section08
open CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
variable {F : InvariantFlag T V 2} {L A : Subgroup G}
namespace MarkedPoint
variable (P : MarkedPoint F L A)

/-- The source extension determines both possible orders of the full quotient centralizer. -/
theorem quotientCentralizer_card_cases (z : P.globalCentralizer)
    (h : P.QuotientCentralizerStructure z) :
    Nat.card (centralizer ({P.pointQuotientMap z} : Set P.PointQuotient)) = 1152 ∨
      Nat.card (centralizer ({P.pointQuotientMap z} : Set P.PointQuotient)) = 2304 := by
  obtain ⟨W, hi, Q, hn, ⟨d⟩, ⟨e⟩⟩ := h
  let := hn
  have hq : Nat.card (W ⧸ Q) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hw : Nat.card W = 1152 := by
    rw [card_eq_card_quotient_mul_card_subgroup Q, hq, d.card]
  have hc := W.card_mul_index
  rw [hw] at hc
  have hp : 0 < W.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hi' : W.index = 1 ∨ W.index = 2 := by omega
  rcases hi' with hi' | hi'
  · left; rw [hi'] at hc; omega
  · right; rw [hi'] at hc; omega

/-- The whole quotient centralizer has order dividing 2304. -/
theorem quotientCentralizer_card_dvd (z : P.globalCentralizer)
    (h : P.QuotientCentralizerStructure z) :
    Nat.card (centralizer ({P.pointQuotientMap z} : Set P.PointQuotient)) ∣ 2304 := by
  rcases P.quotientCentralizer_card_cases z h with h | h
  · rw [h]; decide
  · rw [h]

/-- The actual S₃ × S₃ quotient forces a factor of nine in the centralizer order. -/
theorem nine_dvd_quotientCentralizer (z : P.globalCentralizer)
    (h : P.QuotientCentralizerStructure z) :
    9 ∣ Nat.card (centralizer ({P.pointQuotientMap z} : Set P.PointQuotient)) := by
  rcases P.quotientCentralizer_card_cases z h with h | h
  · rw [h]; decide
  · rw [h]; decide

/-- The marked z remains an involution modulo the distinct marked d. -/
theorem markedGenerator_quotient_order (hA : ElementaryFactor F L A)
    (z : G) (hz : F.Vi 1 = zpowers z) :
    orderOf (P.pointQuotientMap (P.markedGenerator hA.seed_le z hz)) = 2 := by
  have hzA : z ∈ A := hA.seed_le (F.le_seed 1 (hz.symm ▸ mem_zpowers z))
  let x : A.subgroupOf P.globalCentralizer := ⟨P.markedGenerator hA.seed_le z hz, hzA⟩
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← hz]
    simpa using F.card 1 (by decide)
  exact (orderOf_injective _ P.factor_quotient_injective x).trans
    ((orderOf_injective ((P.globalCentralizer.subtype).comp
      (A.subgroupOf P.globalCentralizer).subtype)
      (P.globalCentralizer.subtype_injective.comp Subtype.val_injective) x).symm.trans hz2)

/-- Subnormality identifies the kernel with the component’s intrinsic two-core. -/
theorem component_quotient_kernel (B : Subgroup G)
    (hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer))
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element) :
    (P.pointQuotientMap.comp (B.subgroupOf P.globalCentralizer).subtype).ker =
      pCore 2 (B.subgroupOf P.globalCentralizer) := by
  rw [← MonoidHom.comap_ker, P.pointQuotientMap_ker, P.pointKernel_eq_core hcore]
  exact (pCore_subnormal_eq_comap 2 hB.1).symm

/-- The embedding is induced by the original point quotient map. -/
noncomputable def componentQuotientMap (B : Subgroup G)
    (hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer))
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element) :
    ((B.subgroupOf P.globalCentralizer) ⧸ pCore 2 (B.subgroupOf P.globalCentralizer)) →*
      P.PointQuotient :=
  QuotientGroup.lift _ (P.pointQuotientMap.comp (B.subgroupOf P.globalCentralizer).subtype)
    (P.component_quotient_kernel B hB hcore).symm.le

/-- The actual component two-core quotient embeds in the point quotient. -/
theorem componentQuotientMap_injective (B : Subgroup G)
    (hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer))
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element) :
    Function.Injective (P.componentQuotientMap B hB hcore) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  exact (P.component_quotient_kernel B hB hcore).symm

/-- The order-960 block and the at-most-two kernel force this quotient divisor. -/
theorem componentQuotient_card_dvd (B : Subgroup G) (hBC : B ≤ P.globalCentralizer)
    (hKB : P.blockCentralizer ≤ B)
    (hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer))
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element) :
    480 ∣ Nat.card ((B.subgroupOf P.globalCentralizer) ⧸
      pCore 2 (B.subgroupOf P.globalCentralizer)) := by
  let K := B.subgroupOf P.globalCentralizer
  have hcK : 960 ∣ Nat.card K := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv]
    simpa only [P.blockCentralizer_card] using
      Subgroup.card_dvd_of_injective (inclusion hKB) (inclusion_injective hKB)
  have hp : K.pCoreIn 2 ≤ P.pointKernel := by
    rw [P.pointKernel_eq_core hcore]
    exact pCoreIn_le_of_subnormal 2 hB.1
  have hd : Nat.card (pCore 2 K) ∣ 2 := by
    have hd := Subgroup.card_dvd_of_injective (inclusion hp) (inclusion_injective hp)
    simpa only [pCoreIn, card_map_of_injective K.subtype_injective, P.pointKernel_card] using hd
  have hh := (pCore 2 K).card_mul_index
  rw [index_eq_card] at hh
  have hmul : Nat.card K ∣ 2 * Nat.card (K ⧸ pCore 2 K) := by
    rw [← hh]
    exact Nat.mul_dvd_mul hd (dvd_refl _)
  have hh' : 2 * 480 ∣ 2 * Nat.card (K ⧸ pCore 2 K) := hcK.trans hmul
  exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hh'

abbrev componentGenerator (hA : ElementaryFactor F L A) (z : G)
    (hz : F.Vi 1 = zpowers z) (B : Subgroup G) (hKB : P.blockCentralizer ≤ B) :
    B.subgroupOf P.globalCentralizer :=
  ⟨P.markedGenerator hA.seed_le z hz, hKB (P.generator_mem hA.seed_le z hz)⟩

abbrev componentQuotientGenerator (hA : ElementaryFactor F L A) (z : G)
    (hz : F.Vi 1 = zpowers z) (B : Subgroup G) (hKB : P.blockCentralizer ≤ B) :
    (B.subgroupOf P.globalCentralizer) ⧸ pCore 2 (B.subgroupOf P.globalCentralizer) :=
  QuotientGroup.mk' _ (P.componentGenerator hA z hz B hKB)

/-- The component quotient retains the same nontrivial involution. -/
theorem componentQuotientGenerator_order (hA : ElementaryFactor F L A) (z : G)
    (hz : F.Vi 1 = zpowers z) (B : Subgroup G) (hKB : P.blockCentralizer ≤ B)
    (hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer))
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element) :
    orderOf (P.componentQuotientGenerator hA z hz B hKB) = 2 := by
  exact (orderOf_injective _ (P.componentQuotientMap_injective B hB hcore) _).symm.trans
    (P.markedGenerator_quotient_order hA z hz)

theorem componentQuotientGenerator_fixes_sylow
    (hA : ElementaryFactor F L A) (z : G) (hz : F.Vi 1 = zpowers z)
    (B : Subgroup G) (hKB : P.blockCentralizer ≤ B)
    (hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer))
    (hSylow : CFSG.Quasithin.Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer) :
    ∃ S : Sylow 2 ((B.subgroupOf P.globalCentralizer) ⧸
        pCore 2 (B.subgroupOf P.globalCentralizer)),
      ∀ y : S, MulAut.conj (P.componentQuotientGenerator hA z hz B hKB) y = y := by
  let K := B.subgroupOf P.globalCentralizer
  let q := QuotientGroup.mk' (pCore 2 K)
  obtain ⟨S, hS⟩ := hSylow
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_subnormal K hB.1
  refine ⟨R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _), ?_⟩
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := hy
  have hxS : (x : P.globalCentralizer) ∈ (S : Subgroup P.globalCentralizer) := by
    change x ∈ (S : Subgroup P.globalCentralizer).subgroupOf K
    rwa [← hR]
  have hxT : (x : G) ∈ (T : Subgroup G) :=
    ((hS ▸ mem_map_of_mem P.globalCentralizer.subtype hxS) :
      (x : G) ∈ P.sylowCentralizer).1
  have hcz : (x : G) * z = z * (x : G) :=
    (normalizer_le_centralizer_of_card_two (F.Vi 1)
      (by simpa using F.card 1 (by decide)) (F.invariant 1 hxT)
      z (hz.symm ▸ mem_zpowers z)).symm
  have hc : P.componentGenerator hA z hz B hKB * x =
      x * P.componentGenerator hA z hz B hKB :=
    Subtype.ext (Subtype.ext hcz.symm)
  change q (P.componentGenerator hA z hz B hKB) * q x *
    (q (P.componentGenerator hA z hz B hKB))⁻¹ = q x
  rw [← map_inv, ← map_mul, ← map_mul, hc, mul_inv_cancel_right]

end MarkedPoint

private theorem lie_transport {X Y : Type*} [Group X] [Group Y]
    (h : LieTypeTwoModel X) (e : Y ≃* X) : LieTypeTwoModel Y := by
  rcases h with h | h | ⟨n, hn, hm⟩
  · exact Or.inl (h.of_mulEquiv e)
  · apply Or.inr ∘ Or.inl
    cases h with
    | linear f hf hm => exact .linear f hf (hm.of_mulEquiv e)
    | symplectic f hf hm => exact .symplectic f hf (hm.of_mulEquiv e)
    | g2 f hf hm => exact .g2 f hf (hm.of_mulEquiv e)
    | triality f hf hm => exact .triality f hf (hm.of_mulEquiv e)
    | ree m hm hi =>
        obtain ⟨d, ⟨a⟩⟩ := hi
        exact .ree m hm ⟨d, ⟨e.trans a⟩⟩
    | symplectic_derived hi => exact .symplectic_derived ⟨e.trans hi.some⟩
    | g2_derived hi => exact .g2_derived ⟨e.trans hi.some⟩
    | tits hi => exact .tits ⟨e.trans hi.some⟩
  · exact Or.inr (Or.inr ⟨n, hn, hm.of_mulEquiv e⟩)

/-- Both even rows give a simple Lie model on the actual two-core quotient. -/
theorem EvenModelAction.quotient_model {X : Type*} [Group X] [Finite X]
    [IsQuasisimple X] {α : MulAut X} (h : EvenModelAction X α) :
    center X = pCore 2 X ∧ IsSimpleGroup (X ⧸ pCore 2 X) ∧
      LieTypeTwoModel (X ⧸ pCore 2 X) := by
  rcases h with ⟨hs, hm, _⟩ | ⟨_, hz, hm, _⟩
  · let := hs
    have hz : center X = ⊥ := center_eq_bot_of_simple_perfect
    have hp : pCore 2 X = ⊥ := bot_unique (hz ▸ IsQuasisimple.pCore_le_center 2)
    let e : (X ⧸ pCore 2 X) ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hp).trans QuotientGroup.quotientBot
    exact ⟨hz.trans hp.symm, e.isSimpleGroup, lie_transport hm e⟩
  · refine ⟨hz, ?_, ?_⟩
    · let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
      exact (QuotientGroup.quotientMulEquivOfEq hz.symm).isSimpleGroup
    · apply Or.inr ∘ Or.inl
      rcases hm with hm | hm
      · exact .linear 2 (by decide) hm
      · exact .g2 2 (by decide) hm

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
