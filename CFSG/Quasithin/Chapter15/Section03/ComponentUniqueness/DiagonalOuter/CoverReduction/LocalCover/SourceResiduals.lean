module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Contracts
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Residual
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.ActorData
public import Theory.GroupTheory.PResidual.NormalSubgroup.SimpleQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup.TwoGroupKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData


/-!
# Identifying the two plane residuals in the local cover

The input actor pair supplies the full residuals of the two original plane
centralizers, their three-parts, and their generation of Y. Either orientation
chosen by the Borel argument is allowed. The component residual is nontrivial,
two-perfect, normal in Y, and contained in the first plane residual. That plane
residual has an order-three image in the actual quotient Y/O₂(Y). The normal
simple-quotient argument removes the two-group kernel and identifies the two
residuals.

The two plane images generate the order-nine quotient and intersect trivially.
Cauchy's theorem supplies an order-three element in the second residual. If it
lay in L, its odd order would put it in O²(Y ∩ L), hence its quotient image would
be trivial. This contradicts the two-group kernel.

These are conditional constructors of `ResidualPlaneData`, not a proof of
15.3.38 on their own. The source wrapper uses the genuine natural orthogonal
local data and relative normality of L in its eligible outside overgroup.
The parent supplies Y₊ = Y, the order-nine two-core quotient, and the actor pair
with its full right residual, then constructs the diagonal action separately.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.7 and 15.3.10--12, printed pp.1122--1125; proof of 15.3.38,
printed p.1136, with Mᵢ = C_M(V₍₃₋ᵢ₎) on printed p.1122.
-/

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceResiduals
variable {G : Type*} [Group G] [Finite G]

private theorem image_card_three {Y X : Subgroup G} (hXY : X ≤ Y)
    (hX : 3 ^ (Nat.card X).factorization 3 = 3)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 9) :
    Nat.card ((X.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) = 3 := by
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hthree := threePart_map_of_twoGroup_kernel q hk (X.subgroupOf Y)
  rw [Nat.card_congr (subgroupOfEquivOfLe hXY).toEquiv, hX] at hthree
  have hd := ((X.subgroupOf Y).map q).card_subgroup_dvd_card
  rw [hY] at hd
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show
    Nat.card ((X.subgroupOf Y).map q) ∣ 3 ^ 2 from hd)
  rw [hk, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_three] at hthree
  exact hk.trans (by simpa using hthree)

private theorem perfect_le_residual {A C : Subgroup G} (hAC : A ≤ C)
    (hA : IsPPerfect 2 A) : A ≤ Stellmacher.twoResidualAmbient C := by
  have hp : IsPPerfect 2 (A.subgroupOf C) := hA.of_surjective
    (subgroupOfEquivOfLe hAC).symm.toMonoidHom (subgroupOfEquivOfLe hAC).symm.surjective
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  have h := map_mono (f := C.subtype) (le_pResidual_of_isPPerfect _ hp)
  rwa [map_subgroupOf_eq_of_le hAC] at h

private theorem eq_of_perfect_le {Y A R : Subgroup G}
    (hAR : A ≤ R) (hRY : R ≤ Y) (hYA : Y ≤ normalizer (A : Set G))
    (hA : IsPPerfect 2 A) (hR : IsPPerfect 2 R) (hne : A ≠ ⊥)
    (hRthree : 3 ^ (Nat.card R).factorization 3 = 3)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 9) : A = R := by
  let f : R →* Y ⧸ pCore 2 Y :=
    (QuotientGroup.mk' (pCore 2 Y)).comp (inclusion hRY)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 Y)).comp (inclusion hRY)).ker)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (pCore_isPGroup (p := 2) (G := Y)).comap_of_injective
      (inclusion hRY) (inclusion_injective hRY)
  have hrange : f.range = (R.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) := by
    rw [MonoidHom.range_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      exact r.property
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hq : Nat.card (R ⧸ f.ker) = 3 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange]
    exact image_card_three hRY hRthree hY
  let : IsSimpleGroup (R ⧸ f.ker) := isSimpleGroup_of_prime_card hq
  let : (A.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer (hRY.trans hYA)
  have hp : IsPPerfect 2 (A.subgroupOf R) := hA.of_surjective
    (subgroupOfEquivOfLe hAR).symm.toMonoidHom (subgroupOfEquivOfLe hAR).symm.surjective
  have hn : A.subgroupOf R ≠ ⊥ := by
    intro he
    apply hne
    have hh := congrArg (Subgroup.map R.subtype) he
    simpa only [map_subgroupOf_eq_of_le hAR, Subgroup.map_bot] using hh
  have he := eq_top_of_normal_isPPerfect_of_simple_quotient f.ker hk hR
    (A.subgroupOf R) hp hn
  have hh := congrArg (Subgroup.map R.subtype) he
  simpa only [map_subgroupOf_eq_of_le hAR, ← MonoidHom.range_eq_map, range_subtype] using hh

omit [Finite G] in
private theorem planeResidual_eq_factor {M Y : Subgroup G} (hYM : Y ≤ M)
    (W : Subgroup G) : planeResidual M Y W = RankTwo.centralizingFactor Y W := by
  unfold planeResidual RankTwo.centralizingFactor
  congr 1
  exact le_antisymm (inf_le_inf_left _ inf_le_right)
    (le_inf inf_le_left (le_inf (inf_le_left.trans hYM) inf_le_right))

private theorem images_disjoint {Y A D : Subgroup G}
    (hAY : A ≤ Y) (hDY : D ≤ Y) (hYA : Y ≤ normalizer (A : Set G))
    (hAthree : 3 ^ (Nat.card A).factorization 3 = 3)
    (hDthree : 3 ^ (Nat.card D).factorization 3 = 3)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 9) (hgen : Y = A ⊔ D) :
    Disjoint ((A.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)))
      ((D.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) := by
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Aq := (A.subgroupOf Y).map q
  let Dq := (D.subgroupOf Y).map q
  let : (A.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hYA
  let : Aq.Normal := (inferInstance : (A.subgroupOf Y).Normal).map q
    (QuotientGroup.mk'_surjective _)
  have hsup : Aq ⊔ Dq = ⊤ := by
    dsimp [Aq, Dq]
    rw [← Subgroup.map_sup, ← subgroupOf_sup hAY hDY, ← hgen, subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes Aq Dq
    (by rw [Aq.normalizer_eq_top]; exact le_top)
  rw [image_card_three hAY hAthree hY, image_card_three hDY hDthree hY,
    hsup, card_top, hY] at hcard
  rw [disjoint_iff, ← card_eq_one]
  change Nat.card (Aq ⊓ Dq : Subgroup _) = 1
  omega

private theorem order_three_mem_component {Y L : Subgroup G} {z : G}
    (hzY : z ∈ Y) (hzL : z ∈ L) (hz : orderOf z = 3) :
    z ∈ componentPart Y L := by
  rw [componentPart, ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  refine ⟨⟨z, hzY, hzL⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  have ho : orderOf (⟨z, hzY, hzL⟩ : ↥(Y ⊓ L : Subgroup G)) = 3 :=
    (orderOf_injective (Y ⊓ L).subtype (Y ⊓ L).subtype_injective _).symm.trans hz
  change Nat.Coprime 2 (orderOf (⟨z, hzY, hzL⟩ : ↥(Y ⊓ L : Subgroup G)))
  rw [ho]
  decide

private theorem exists_outside_actor {Y L D : Subgroup G}
    (hDY : D ≤ Y) (hYA : Y ≤ normalizer (componentPart Y L : Set G))
    (hAthree : 3 ^ (Nat.card (componentPart Y L)).factorization 3 = 3)
    (hDthree : 3 ^ (Nat.card D).factorization 3 = 3)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 9) (hgen : Y = componentPart Y L ⊔ D) :
    ∃ z ∈ D, orderOf z = 3 ∧ z ∉ L := by
  have hdiv : 3 ∣ Nat.card D := by
    rw [← hDthree]
    exact Nat.ordProj_dvd (Nat.card D) 3
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdiv
  have hzG : orderOf (z : G) = 3 :=
    (orderOf_injective D.subtype D.subtype_injective z).trans hz
  refine ⟨z, z.property, hzG, ?_⟩
  intro hzL
  have hzA := order_three_mem_component (hDY z.property) hzL hzG
  have hd := images_disjoint (RankTwo.componentFactor_le_left Y L) hDY hYA
    hAthree hDthree hY hgen
  let zy : Y := ⟨z, hDY z.property⟩
  have hq : QuotientGroup.mk' (pCore 2 Y) zy = 1 := hd.le_bot
    ⟨mem_map_of_mem _ (show zy ∈ (componentPart Y L).subgroupOf Y from hzA),
      mem_map_of_mem _ (show zy ∈ D.subgroupOf Y from z.property)⟩
  have hzQ : zy ∈ pCore 2 Y := by
    simpa only [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] using hq
  let zq : pCore 2 Y := ⟨zy, hzQ⟩
  have ho : orderOf zq = 3 :=
    ((orderOf_injective (pCore 2 Y).subtype (pCore 2 Y).subtype_injective zq).symm.trans
      (orderOf_injective Y.subtype Y.subtype_injective zy).symm).trans hzG
  have hc := (pCore_isPGroup (p := 2) (G := Y)).orderOf_coprime
    (by decide : Nat.Coprime 2 3) zq
  rw [ho] at hc
  norm_num at hc

/-- Identification for either orientation of the two full plane actors. -/
public theorem of_actorPair {M Y Yplus S L V V₁ V₂ : Subgroup G}
    {n : ℕ} {c : ProjectiveMarking L (2 ^ n)}
    (b : OrientedBorelData M Yplus S L V₁ V₂ c)
    (hplus : Yplus = Y) (hYM : Y ≤ M) (hYL : Y ≤ normalizer (L : Set G))
    (hquot : Nat.card (Y ⧸ pCore 2 Y) = 9)
    (a : RankTwo.PlaneActorPair M Y Y S V V₁ V₂)
    (hright : a.right = RankTwo.centralizingFactor Y V₁) :
    ResidualPlaneData M Y Yplus L b.W₁ b.W₂ := by
  subst Yplus
  have hplanes :
      3 ^ (Nat.card (planeResidual M Y b.W₁)).factorization 3 = 3 ∧
      3 ^ (Nat.card (planeResidual M Y b.W₂)).factorization 3 = 3 ∧
      Y = planeResidual M Y b.W₁ ⊔ planeResidual M Y b.W₂ := by
    have hg := a.generate
    rw [hright] at hg
    have hr := a.right_three_part
    rw [hright] at hr
    rcases b.planes with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂, planeResidual_eq_factor hYM, planeResidual_eq_factor hYM]
      exact ⟨hr, a.left_three_part, by rwa [sup_comm]⟩
    · rw [h₁, h₂, planeResidual_eq_factor hYM, planeResidual_eq_factor hYM]
      exact ⟨a.left_three_part, hr, hg⟩
  have hAY : componentPart Y L ≤ Y := RankTwo.componentFactor_le_left Y L
  have hAn : Y ≤ normalizer (componentPart Y L : Set G) :=
    ComponentIntersection.normalizes_intersectionResidual hYL
  have hAp : IsPPerfect 2 (componentPart Y L) :=
    ComponentIntersection.intersectionResidual_isPPerfect Y L
  have hAR : componentPart Y L ≤ planeResidual M Y b.W₁ :=
    perfect_le_residual (le_inf hAY (le_inf (hAY.trans hYM) b.component_centralizes)) hAp
  have hAne : componentPart Y L ≠ ⊥ := by
    intro he
    have hm := b.component_moves
    rw [he, commutator_bot_right] at hm
    have hc := b.second_card
    rw [← hm] at hc
    norm_num at hc
  have he : componentPart Y L = planeResidual M Y b.W₁ :=
    eq_of_perfect_le hAR ((planeResidual_le M Y b.W₁).trans inf_le_left) hAn hAp
      (by rw [planeResidual_eq_factor hYM]; exact RankTwo.centralizingFactor_isPPerfect _ _)
      hAne hplanes.1 hquot
  have hgen : Y = componentPart Y L ⊔ planeResidual M Y b.W₂ := by
    rw [he]
    exact hplanes.2.2
  exact ⟨he, hgen, exists_outside_actor
    ((planeResidual_le M Y b.W₂).trans inf_le_left) hAn
    (he.symm ▸ hplanes.1) hplanes.2.1 hquot hgen⟩

/-- The bridge for the source local data, with relative normality in the
eligible outside overgroup. The natural action and both original planes are
those of `d`; the supplied actor pair is the separate action calculation. -/
public theorem of_localData (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    {n : ℕ} {c : ProjectiveMarking L (2 ^ n)}
    (b : OrientedBorelData d.M d.Yplus d.S L d.V₁ d.V₂ c)
    (hplus : d.Yplus = d.Y) (hI : I ∈ d.Hplus)
    (hLI : L ≤ I) (hL : (L.subgroupOf I).Normal)
    (hquot : Nat.card (d.Y ⧸ pCore 2 d.Y) = 9)
    (a : RankTwo.PlaneActorPair d.M d.Y d.Y d.S d.V d.V₁ d.V₂)
    (hright : a.right = RankTwo.centralizingFactor d.Y d.V₁) :
    ResidualPlaneData d.M d.Y d.Yplus L b.W₁ b.W₂ := by
  have hYI : d.Y ≤ I := hplus ▸ (le_sup_left.trans hI.1.2)
  exact of_actorPair b hplus (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
    (hYI.trans ((normal_subgroupOf_iff_le_normalizer hLI).mp hL)) hquot a hright

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceResiduals
