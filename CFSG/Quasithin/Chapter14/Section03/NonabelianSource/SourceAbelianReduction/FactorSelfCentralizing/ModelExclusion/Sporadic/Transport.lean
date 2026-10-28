module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# Literal quotient transport for the sporadic rows of 14.3.20

Subnormality identifies the intrinsic component two-core with the restriction
of the global core. The component quotient therefore embeds in C_G(d)/<d>
by the original quotient map. The elementary factor remains injective, and
the original z becomes a two-central involution of the marked model.
The index-at-most-two quaternion extension bounds the full marked centralizer.
No central cover is split and no fixed-point lifting is assumed.

Source: Aschbacher--Smith, 14.3.20, printed p.998, and 1.1.5(3)(f), p.502.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
variable {F : InvariantFlag T V 2} {L A : Subgroup G}
namespace MarkedPoint
variable (P : MarkedPoint F L A)

/-- The actual local extension has order 1152 or 2304. -/
theorem quotientCentralizer_card_dvd (z : P.globalCentralizer)
    (h : P.QuotientCentralizerStructure z) :
    Nat.card (centralizer ({P.pointQuotientMap z} : Set P.PointQuotient)) ∣ 2304 := by
  obtain ⟨W, hi, Q, hQ, ⟨d⟩, ⟨e⟩⟩ := h
  let := hQ
  have hq : Nat.card (W ⧸ Q) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hw : Nat.card W = 1152 := by
    have hc := Q.card_mul_index
    rw [d.card, index_eq_card, hq] at hc
    omega
  have hc := W.card_mul_index
  have hp : W.index ≠ 0 := index_ne_zero_of_finite
  have hid : W.index = 1 ∨ W.index = 2 := by omega
  rcases hid with hid | hid
  · rw [hw, hid] at hc
    exact hc ▸ (by decide : 1152 * 1 ∣ 2304)
  · rw [hw, hid] at hc
    exact hc ▸ (by decide : 1152 * 2 ∣ 2304)

/-- The intrinsic component quotient embeds by the original cyclic quotient map. -/
theorem exists_component_quotient_embedding (B : Subgroup P.globalCentralizer)
    (hB : B.IsSubnormal)
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element) :
    ∃ j : (B ⧸ pCore 2 B) →* P.PointQuotient, Function.Injective j ∧
      (∀ x : B, j (QuotientGroup.mk' (pCore 2 B) x) = P.pointQuotientMap x) ∧
      j.range.IsSubnormal := by
  let f := P.pointQuotientMap.comp B.subtype
  have hk : pCore 2 B = f.ker := by
    rw [pCore_subnormal_eq_comap 2 hB]
    change (pCore 2 P.globalCentralizer).comap B.subtype =
      P.pointQuotientMap.ker.comap B.subtype
    rw [P.pointQuotientMap_ker, P.pointKernel_eq_core hcore]
  let e := (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivRange f)
  let j := f.range.subtype.comp e.toMonoidHom
  have hj (x : B) : j (QuotientGroup.mk' (pCore 2 B) x) = P.pointQuotientMap x := rfl
  refine ⟨j, f.range.subtype_injective.comp e.injective, hj, ?_⟩
  have hr : j.range = B.map P.pointQuotientMap := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) y
      exact ⟨y, y.property, hj y⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 B) ⟨y, hy⟩, hj ⟨y, hy⟩⟩
  rw [hr]
  exact hB.map (QuotientGroup.mk'_surjective P.pointKernel)

/-- The model contains the same elementary sixteen and embeds as the actual
subnormal component image, with the original two-central marked element. -/
theorem exists_marked_model_embedding (hA : ElementaryFactor F L A)
    (name : ClassificationModels.SporadicName)
    (z : G) (hz : F.Vi 1 = zpowers z)
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element)
    (h : P.ComponentWithAction z (fun B α =>
      Nonempty (((B.subgroupOf P.globalCentralizer) ⧸
        pCore 2 (B.subgroupOf P.globalCentralizer)) ≃* name.Carrier) ∧ TwoCentralInner α)) :
    ∃ (t : name.Carrier) (j : name.Carrier →* P.PointQuotient),
      Function.Injective j ∧ j.range.IsSubnormal ∧
      j t = P.pointQuotientMap (P.markedGenerator hA.seed_le z hz) ∧
      orderOf t = 2 ∧ TwoCentral t ∧ 4 ≤ primeRank 2 name.Carrier := by
  obtain ⟨B, hBC, hKB, hcomp, hcomm, α, hα, ⟨e⟩, ha⟩ := h
  let K := B.subgroupOf P.globalCentralizer
  obtain ⟨j₀, hj₀, hj₀mk, hj₀sub⟩ :=
    P.exists_component_quotient_embedding K hcomp.1 hcore
  let : Finite name.Carrier := Finite.of_surjective e e.surjective
  let q := QuotientGroup.mk' (pCore 2 K)
  let f := e.toMonoidHom.comp q
  let j := j₀.comp e.symm.toMonoidHom
  have hj : Function.Injective j := hj₀.comp e.symm.injective
  have hjf (x : K) : j (f x) = P.pointQuotientMap x := by
    change j₀ (e.symm (e (q x))) = _
    rw [e.symm_apply_apply]
    exact hj₀mk x
  have hAC : A ≤ P.globalCentralizer := P.factor_le_blockCentralizer.trans inf_le_right
  have hAK : A.subgroupOf P.globalCentralizer ≤ K :=
    fun _ hx => hKB (P.factor_le_blockCentralizer hx)
  let i := f.comp (inclusion hAK)
  have hi : Function.Injective i := by
    intro x y hxy
    apply P.factor_quotient_injective
    exact (hjf (inclusion hAK x)).symm.trans
      ((congrArg j hxy).trans (hjf (inclusion hAK y)))
  have hzA : z ∈ A := hA.seed_le (F.le_seed 1 (hz.symm ▸ mem_zpowers z))
  let zK : K := ⟨P.markedGenerator hA.seed_le z hz, hKB (P.factor_le_blockCentralizer hzA)⟩
  let t := f zK
  have hz2 : orderOf zK = 2 := by
    rw [← orderOf_injective K.subtype K.subtype_injective,
      ← orderOf_injective P.globalCentralizer.subtype P.globalCentralizer.subtype_injective]
    change orderOf z = 2
    rw [← Nat.card_zpowers, ← hz]
    simpa using F.card 1 (by decide)
  have ht2 : orderOf t = 2 := by
    have hzi : i ⟨P.markedGenerator hA.seed_le z hz, hzA⟩ = t := rfl
    rw [← hzi, orderOf_injective i hi]
    rw [← orderOf_injective (A.subgroupOf P.globalCentralizer).subtype Subtype.val_injective,
      ← orderOf_injective P.globalCentralizer.subtype P.globalCentralizer.subtype_injective]
    change orderOf z = 2
    rw [← Nat.card_zpowers, ← hz]
    simpa using F.card 1 (by decide)
  have htcentral : TwoCentral t := by
    obtain ⟨S, hS⟩ := ha.2.2
    have hzc : (S : Subgroup K) ≤ centralizer ({zK} : Set K) := by
      intro x hx
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun y : K => ((y : P.globalCentralizer) : G)) (hS ⟨x, hx⟩)
      rw [hα] at he
      apply Subtype.ext
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hp : IsPGroup 2 (zpowers zK) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hz2]; rfl)
    have hn : zpowers zK ≤ normalizer (S : Set K) := by
      apply (zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hzc hx)
    have hzS : zK ∈ S :=
      (sup_eq_left.mp (S.is_maximal' (S.isPGroup'.to_sup_of_normal_left' hp hn)
        le_sup_left)) (mem_zpowers zK)
    let Sf := S.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    refine ⟨Sf, ⟨zK, hzS, rfl⟩, ?_⟩
    apply mem_center_iff.mpr
    rintro ⟨x, y, hy, rfl⟩
    apply Subtype.ext
    exact (map_mul f _ _).symm.trans
      ((congrArg f (mem_centralizer_singleton_iff.mp (hzc hy))).trans (map_mul f _ _))
  refine ⟨t, j, hj, ?_, hjf zK, ht2, htcentral, ?_⟩
  · have hr : j.range = j₀.range := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨e.symm y, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨e y, by change j₀ (e.symm (e y)) = j₀ y; rw [e.symm_apply_apply]⟩
    exact hr ▸ hj₀sub
  · let := hA.elementary
    let : IsElementaryAbelian 2 (A.subgroupOf P.globalCentralizer) :=
      IsElementaryAbelian.subgroupOf hAC
    have hc : Nat.card (A.subgroupOf P.globalCentralizer) = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv).trans hA.card
    have hr : primeRank 2 (A.subgroupOf P.globalCentralizer) = 4 := by
      rw [← IsElementaryAbelian.log_card_eq_primeRank, hc]
      decide
    exact hr ▸ _root_.primeRank_le_of_injective 2 i hi
end MarkedPoint
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
