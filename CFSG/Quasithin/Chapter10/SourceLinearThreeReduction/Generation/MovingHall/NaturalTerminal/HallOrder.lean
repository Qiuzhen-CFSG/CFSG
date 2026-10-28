module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.Quotient
public import Theory.SpecificGroups.SL2.PairBorelOddOrder

/-!
# The original odd Hall order in the general-field orbit Borel

The literal orbit quotient maps its Sylow normalizer into the paired SL₂
Borel. The two-core kernel misses the odd Hall, so the paired Borel order
forces the original Hall order to divide (q−1)². No scalar marking or
identification with a separately selected Hall subgroup is assumed.
Source: Aschbacher–Smith 10.2.3(4), printed pp.745–746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D in
private theorem orbit_sylow_intersection :
    ∃ S : Sylow 2 (localOrbit T L),
      (S : Subgroup (localOrbit T L)) = (T : Subgroup G).subgroupOf (localOrbit T L) := by
  let R := localOrbit T L
  let M := D.maximalLocal
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype (le_normalizer_componentOrbit L T)).exists_subgroupOf_eq_of_normal
    (R.subgroupOf M)
  let a := subgroupOfEquivOfLe R.le_normalizer
  refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
  change (P : Subgroup (R.subgroupOf M)).map a.toMonoidHom = _
  rw [hP]
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hr
    exact ⟨⟨⟨r,R.le_normalizer r.property⟩,r.property⟩,hr,rfl⟩

/-- The original Hall order divides the full paired Cartan order. -/
theorem Context.hall_card_dvd_torus_square
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    Nat.card B ∣ (Nat.card F - 1)^2 := by
  let R := localOrbit T L
  let C := B.map H.subtype
  have hCN : C ≤ sourceOrbitSylowNormalizer T L := hBB.trans (map_subtype_le _)
  have hCR : C ≤ R := hCN.trans inf_le_left
  have hodd : Odd (Nat.card C) := ctx.odd_card_of_le_hall_image C le_rfl
  obtain ⟨t,ht,htn,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 ctx.nonnormal
  obtain ⟨a,_,_⟩ := source_original_natural_pair_quotient D n hn hF e ctx.nonnormal ht htn
  let q : R →* (SL(2,F) × SL(2,F)) := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 R := by
    ext x
    change a (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [a.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let f : C →* (SL(2,F) × SL(2,F)) := q.comp (inclusion hCR)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_of_card_eq
    have hp : IsPGroup 2 f.ker := by
      change IsPGroup 2 (q.ker.comap (inclusion hCR))
      rw [hk]
      exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hCR)
    exact hp.card_eq_or_dvd.resolve_right
      (hodd.of_dvd_nat (card_subgroup_dvd_card f.ker)).not_two_dvd_nat
  obtain ⟨S,hS⟩ := orbit_sylow_intersection D
  have hN : (sourceOrbitSylowNormalizer T L).subgroupOf R =
      normalizer ((S : Subgroup R) : Set R) := by
    have he : (sourceOrbitSylowNormalizer T L).subgroupOf R =
        (normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G)).subgroupOf R := by
      ext x
      exact and_iff_right x.property
    rw [he,subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ R ≤ R from inf_le_right)]
    congr 2
    rw [hS]
    ext x
    exact and_iff_left x.property
  let P := S.mapSurjective hq
  have hBN : f.range ≤ normalizer ((P : Subgroup (SL(2,F) × SL(2,F))) : Set _) := by
    rintro _ ⟨b,rfl⟩
    apply (S : Subgroup R).le_normalizer_map q
    apply mem_map.mpr
    refine ⟨inclusion hCR b,?_,rfl⟩
    rw [←hN]
    exact hCN b.property
  have hodd' : Odd (Nat.card f.range) := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    exact hodd
  have hd := Matrix.SpecialLinearGroup.odd_card_dvd_pair_torus_order hF P f.range hBN hodd'
  rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv] at hd
  simpa only [C,card_map_of_injective H.subtype_injective] using hd

end CFSG.Quasithin.Chapter10.MovingHall
