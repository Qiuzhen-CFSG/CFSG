module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.InnerSplitting.RankOneImage
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.InnerSplitting.SectionAction

/-!
# The inner-action splitting in 15.3.12

The genuine inner action embeds the image of `Y₊` in an image of the
rank-one component `L`. Cyclic Sylow three-subgroups bound its rank.
Transfer excludes central three-torsion in `L/O₂(L)`, so the kernel on
`Y_L` is a two-group. The rank-one image comparison then shows that
`Y_L` supplies the entire action of `Y₊`.

Taking the residual of the action kernel gives the literal product
`Y₊ = Y_L Y_C`. The same kernel argument shows that the intersection of
these two residual factors is a two-group. The order-three quotient and
nontriviality of `Y_L` are the explicit inputs from the independent
odd-rank argument; the quotient properties and theta equality are the
local conclusions of 15.3.11. No exponent assumption on `Y₊` is made.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.12(2), printed p.1125 (PDF p.1142).
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.InnerSplitting
variable {G : Type*} [Group G] [Finite G]

/-- Every element of `Y` induces the same quotient automorphism as some
member of the actual intersection residual. -/
theorem action_comparison_of_local_facts
    {Y M I L : Subgroup G}
    (htheta : theta (M ⊓ I) = Y)
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (hr : primeRank 3 L = 1)
    (hi : InducesInnerOnTwoCoreQuotient Y L)
    (hne : intersectionResidual Y L ≠ ⊥)
    (ha : Nat.card (TwoCoreQuotient (intersectionResidual Y L)) = 3)
    (hq : IsPGroup 3 (TwoCoreQuotient Y))
    (he : Monoid.exponent (TwoCoreQuotient Y) ∣ 3) :
    ∀ y ∈ Y, ∃ a ∈ intersectionResidual Y L,
      a⁻¹ * y ∈ Chapter4.sectionCentralizer L := by
  let N := normalizer (L : Set G)
  let ψ : Y →* MulAut (TwoCoreQuotient L) :=
    (sectionAction L).comp (inclusion hi.normalizes)
  let φ : L →* MulAut (TwoCoreQuotient L) :=
    (sectionAction L).comp (inclusion L.le_normalizer)
  have hinner : ψ.range ≤ φ.range := by
    rintro x ⟨y, rfl⟩
    obtain ⟨l, hl, hc⟩ := hi y y.property
    refine ⟨⟨l, hl⟩, ?_⟩
    have hh := (sectionAction_eq_one_iff L
      ((inclusion L.le_normalizer ⟨l, hl⟩)⁻¹ * inclusion hi.normalizes y)).mpr hc
    rw [map_mul, map_inv, inv_mul_eq_one] at hh
    exact hh
  let P : Sylow 3 L := Sylow.nonempty.some
  have hP : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr.le
  have hφr : primeRank 3 φ.range ≤ 1 :=
    P.primeRank_le_one_of_surjective hP φ.rangeRestrict φ.rangeRestrict_surjective
  have hψr : primeRank 3 ψ.range ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hinner)
      (inclusion_injective hinner)).trans hφr
  let A := intersectionResidual Y L
  have hAY : A ≤ Y := (intersectionResidual_le Y L).trans inf_le_left
  have hAL : A ≤ L := (intersectionResidual_le Y L).trans inf_le_right
  let A₀ := A.subgroupOf Y
  let e : A₀ ≃* A := subgroupOfEquivOfLe hAY
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer
    (normalizes_intersectionResidual hi.normalizes)
  have hAp : IsPPerfect 2 A₀ := (intersectionResidual_isPPerfect Y L).of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hAne : A₀ ≠ ⊥ := by
    intro hb
    apply hne
    have hm := congrArg (Subgroup.map Y.subtype) hb
    simpa only [A₀, map_subgroupOf_eq_of_le hAY, Subgroup.map_bot] using hm
  have hAc : Nat.card (A₀ ⧸ pCore 2 A₀) = 3 := by
    let eqQ := QuotientGroup.congr (pCore 2 A₀) (pCore 2 A) e (pCore_map_iso 2 e)
    exact (Nat.card_congr eqQ.toEquiv).trans ha
  let j : A₀ →* L := (inclusion hAL).comp e.toMonoidHom
  let f : A₀ →* TwoCoreQuotient L := (QuotientGroup.mk' (pCore 2 L)).comp j
  have hj : Function.Injective j := (inclusion_injective hAL).comp e.injective
  have hfk : IsPGroup 2 f.ker := by
    have hk : f.ker = (pCore 2 L).comap j := by
      ext a
      exact QuotientGroup.eq_one_iff _
    rw [hk]
    exact pCore_isPGroup.comap_of_injective j hj
  let : Group.IsPerfect (L.subgroupOf I) := hL.perfect
  let eL := subgroupOfEquivOfLe hLI
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective
  have hLq : primeRank 3 (TwoCoreQuotient L) ≤ 1 := P.primeRank_quotient_le_one hP _
  have hcenter := three_not_dvd_center_of_perfect_rankOne hLq
  have haction (a : A₀) : ψ (a : Y) = MulAut.conj (f a) :=
    sectionAction_on_component L (j a)
  have hk : IsPGroup 2 (ψ.rangeRestrict.comp A₀.subtype).ker := by
    have hh : (ψ.rangeRestrict.comp A₀.subtype).ker =
        ((MulAut.conj : TwoCoreQuotient L →* MulAut (TwoCoreQuotient L)).comp f).ker := by
      ext a
      change (⟨ψ (a : Y), _⟩ : ψ.range) = 1 ↔ MulAut.conj (f a) = 1
      rw [Subtype.ext_iff]
      change ψ (a : Y) = 1 ↔ MulAut.conj (f a) = 1
      rw [haction]
    rw [hh]
    exact inner_kernel_isTwoGroup f hfk hAc hcenter
  have hs := rankOne_image_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    (htheta ▸ theta_isPPerfect (M ⊓ I)) hψr hq he A₀ hAp hAne hk
  intro y hy
  obtain ⟨a, hae⟩ := hs (ψ.rangeRestrict ⟨y, hy⟩)
  refine ⟨(e a : G), (e a).property, ?_⟩
  have hψeq : ψ (a : Y) = ψ ⟨y, hy⟩ := congrArg Subtype.val hae
  apply (sectionAction_eq_one_iff L
    ((inclusion hi.normalizes (a : Y))⁻¹ * inclusion hi.normalizes ⟨y, hy⟩)).mp
  rw [map_mul, map_inv]
  exact inv_mul_eq_one.mpr hψeq


/-- The section-centralizing part of a subgroup with two-core quotient of
order three is a two-group in a perfect rank-one component. -/
theorem intersection_sectionCentralizer_isTwoGroup
    {A L : Subgroup G} [Group.IsPerfect L]
    (hAL : A ≤ L) (hr : primeRank 3 L ≤ 1)
    (ha : Nat.card (TwoCoreQuotient A) = 3) :
    IsPGroup 2 (A ⊓ Chapter4.sectionCentralizer L : Subgroup G) := by
  let j := inclusion hAL
  let f : A →* TwoCoreQuotient L := (QuotientGroup.mk' (pCore 2 L)).comp j
  have hk : IsPGroup 2 f.ker := by
    have hh : f.ker = (pCore 2 L).comap j := by
      ext a
      exact QuotientGroup.eq_one_iff _
    rw [hh]
    exact pCore_isPGroup.comap_of_injective j (inclusion_injective hAL)
  let P : Sylow 3 L := Sylow.nonempty.some
  have hrq := P.primeRank_quotient_le_one
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) (pCore 2 L)
  let k := ((MulAut.conj : TwoCoreQuotient L →* MulAut (TwoCoreQuotient L)).comp f).ker
  have htwo : IsPGroup 2 k := inner_kernel_isTwoGroup f hk ha
    (three_not_dvd_center_of_perfect_rankOne hrq)
  have hm : k.map A.subtype = A ⊓ Chapter4.sectionCentralizer L := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.property, ?_⟩
      apply (sectionAction_eq_one_iff L (inclusion (hAL.trans L.le_normalizer) a)).mp
      rw [show sectionAction L (inclusion (hAL.trans L.le_normalizer) a) =
        MulAut.conj (f a) from sectionAction_on_component L (j a)]
      exact ha
    · rintro ⟨hxA, hxK⟩
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      have he := (sectionAction_eq_one_iff L
        (inclusion (hAL.trans L.le_normalizer) ⟨x, hxA⟩)).mpr hxK
      rwa [show sectionAction L (inclusion (hAL.trans L.le_normalizer) ⟨x, hxA⟩) =
        MulAut.conj (f ⟨x, hxA⟩) from sectionAction_on_component L (j ⟨x, hxA⟩)] at he
  rw [← hm]
  exact htwo.map A.subtype

/-- The two actual residual factors have two-group intersection. -/
theorem residual_intersection_isTwoGroup
    {Y I L : Subgroup G} (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (hr : primeRank 3 L = 1)
    (ha : Nat.card (TwoCoreQuotient (intersectionResidual Y L)) = 3) :
    IsPGroup 2 (intersectionResidual Y L ⊓ centralizerResidual Y L : Subgroup G) := by
  let : Group.IsPerfect (L.subgroupOf I) := hL.perfect
  let eL := subgroupOfEquivOfLe hLI
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective
  exact (intersection_sectionCentralizer_isTwoGroup
    ((intersectionResidual_le Y L).trans inf_le_right) hr.le ha).to_le
    (inf_le_inf le_rfl ((centralizerResidual_le Y L).trans inf_le_right))

/-- Literal set-product splitting into the residual of the intersection and
the residual of the genuine section-action kernel. -/
theorem residual_factorization_of_local_facts
    {Y M I L : Subgroup G}
    (htheta : theta (M ⊓ I) = Y)
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (hr : primeRank 3 L = 1)
    (hi : InducesInnerOnTwoCoreQuotient Y L)
    (hne : intersectionResidual Y L ≠ ⊥)
    (ha : Nat.card (TwoCoreQuotient (intersectionResidual Y L)) = 3)
    (hq : IsPGroup 3 (TwoCoreQuotient Y))
    (he : Monoid.exponent (TwoCoreQuotient Y) ∣ 3) :
    (Y : Set G) = (intersectionResidual Y L : Set G) * (centralizerResidual Y L : Set G) := by
  let A := intersectionResidual Y L
  have hAY : A ≤ Y := (intersectionResidual_le Y L).trans inf_le_left
  let N := A.subgroupOf Y
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (normalizes_intersectionResidual hi.normalizes)
  have hcover : (Y : Set G) ⊆ (Chapter4.sectionCentralizer L : Set G) *
      (N.map Y.subtype : Set G) := by
    intro y hy
    obtain ⟨a, ha, hd⟩ := action_comparison_of_local_facts htheta hLI hL hr hi hne ha hq he y hy
    have hAYa := hAY ha
    have hdiff : a⁻¹ * y ∈ Chapter4.sectionCentralizerIn Y L :=
      ⟨Y.mul_mem (Y.inv_mem hAYa) hy, hd⟩
    have hconj := (Chapter4.sectionCentralizerIn_normalized hi.normalizes hAYa (a⁻¹ * y)).mp hdiff
    have hk : y * a⁻¹ ∈ Chapter4.sectionCentralizer L := by
      have hh := hconj.2
      change a * (a⁻¹ * y) * a⁻¹ ∈ Chapter4.sectionCentralizer L at hh
      rwa [mul_inv_cancel_left] at hh
    refine ⟨y * a⁻¹, hk, a, ?_, by group⟩
    exact mem_map.mpr ⟨⟨a, hAYa⟩, ha, rfl⟩
  have hprod := eq_mul_embedded_pResidual_of_cover 2 Y (Chapter4.sectionCentralizer L) N
    (htheta ▸ theta_isPPerfect (M ⊓ I)) hcover
  have hN : N.map Y.subtype = A := map_subgroupOf_eq_of_le hAY
  rw [hN, ← twoResidualAmbient_eq_map_pResidual] at hprod
  change (Y : Set G) = (centralizerResidual Y L : Set G) * (A : Set G) at hprod
  rw [set_mul_normalizer_comm _ A
    (((centralizerResidual_le Y L).trans inf_le_left).trans
      (normalizes_intersectionResidual hi.normalizes))] at hprod
  exact hprod

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.InnerSplitting

end
