module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.PairGeometry
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.FiveSylow
public import Theory.SpecificGroups.SL2.SolvableSylowCore
public import Theory.SpecificGroups.SL2.SolvableSylowTorus

/-!
# The actual component intersections before the factor-join index

Each PSL₂(16) component meets the solvable original J in an overgroup of
its Sylow intersection. Its two-core is that intersection, and its core
quotient embeds in the Borel torus of order fifteen. The original starred
residual has order twenty-five and two-group quotient, so J has no cubic
divisor; the torus quotient therefore has order dividing five. The proved
prime-to-five index of J in Mc makes that quotient have order exactly five.

This retains the two actual components and both original Sylow intersections.
Their images and supports must still be aligned with the D10 factors; neither
that identification nor the outer contradiction is asserted here.
Source: Aschbacher--Smith 14.6.15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer
open OddNormalizer.Quintic.ModuleGeometry (ExchangedFactorData)
namespace Singleton.QuinticNoIndex
open SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]
private theorem sixteen_sl_not_solvable : ¬ Group.IsSolvable SL(2,GaloisField 2 4) := by
  let := Theory.PSL2.SixteenWreathComponents.perfect
  let := Theory.PSL2.SixteenWreathComponents.simple
  intro hs
  let := hs
  apply Group.IsPerfect.not_isSolvable Theory.PSL2.SixteenWreathComponents.L
  exact Group.isSolvable_of_surjective
    (f := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 4)).toMonoidHom)
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 4)).surjective

/-- The prescribed component Sylow intersection is the entire two-core of K ∩ H. -/
private theorem component_intersection_core
    (T : Sylow 2 G) {H Mc : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHM : H ≤ Mc) (hsolv : Group.IsSolvable H) {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    (K ⊓ H).pCoreIn 2 = K ⊓ (T : Subgroup G) := by
  let HM := H.subgroupOf Mc
  let KM := K.subgroupOf Mc
  let hTM := hTH.trans hHM
  let eK := subgroupOfEquivOfLe hKM
  let e := em.some.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL
    (F := GaloisField 2 4)).symm
  let q : KM →* SL(2,GaloisField 2 4) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 K)).comp eK.toMonoidHom)
  have hq : Function.Surjective q :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eK.surjective)
  have hk : q.ker = (pCore 2 K).comap eK.toMonoidHom := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,
      ←MonoidHom.comap_ker,QuotientGroup.ker_mk']
  have hkp : IsPGroup 2 q.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective _ eK.injective
  let : Group.IsSolvable H := hsolv
  let eH := subgroupOfEquivOfLe hHM
  let : Group.IsSolvable HM := Group.isSolvable_of_isSolvable_injective
    (f := eH.toMonoidHom) eH.injective
  have hc := Matrix.SpecialLinearGroup.solvable_intersection_core
    (T.subtype hTM) KM HM hK.subnormal q hq hkp sixteen_sl_not_solvable
    (fun x hx => hTH hx)
  have hh := congrArg (Subgroup.map Mc.subtype) hc
  rw [map_pCoreIn_of_injective 2 _ _ Mc.subtype_injective,
    Subgroup.map_inf _ _ _ Mc.subtype_injective,
    Subgroup.map_inf _ _ _ Mc.subtype_injective,
    map_subgroupOf_eq_of_le hKM,map_subgroupOf_eq_of_le hHM,
    show ((T.subtype hTM : Sylow 2 Mc) : Subgroup Mc) =
      (T : Subgroup G).subgroupOf Mc from rfl,
    map_subgroupOf_eq_of_le hTM] at hh
  exact hh

private theorem intersection_torus_embedding
    (T : Sylow 2 G) {H Mc : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHM : H ≤ Mc) (hsolv : Group.IsSolvable H) {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    ∃ f : ((K ⊓ H : Subgroup G) ⧸ pCore 2 (K ⊓ H : Subgroup G)) →*
      (GaloisField 2 4)ˣ, Function.Injective f := by
  have hTM : (T : Subgroup G) ≤ Mc := hTH.trans hHM
  let eK := subgroupOfEquivOfLe hKM
  obtain ⟨R,hR⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_subnormal
    (K.subgroupOf Mc) hK.subnormal
  let P : Sylow 2 K := R.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      rw [hR] at hy
      exact hy
    · intro hx
      refine ⟨eK.symm x,?_,eK.apply_symm_apply x⟩
      rw [hR]
      exact hx
  let e := em.some.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL
    (F := GaloisField 2 4)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hns : ¬ Group.IsSolvable SL(2,GaloisField 2 4) := by
    let := Theory.PSL2.SixteenWreathComponents.perfect
    let := Theory.PSL2.SixteenWreathComponents.simple
    intro hs
    let := hs
    exact Group.IsPerfect.not_isSolvable Theory.PSL2.SixteenWreathComponents.L
      (Group.isSolvable_of_surjective
        (f := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 4)).toMonoidHom)
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 4)).surjective)
  let B := H.subgroupOf K
  let : Group.IsSolvable H := hsolv
  let i : B →* H := (K.subtype.comp B.subtype).codRestrict H (fun x => x.property)
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (f := i) (by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => (z : G)) he)
  have hPB : (P : Subgroup K) ≤ B := by
    rw [hP]
    exact fun x hx => hTH hx
  obtain ⟨f,hf⟩ := Matrix.SpecialLinearGroup.solvable_sylow_overgroup_torus_embedding
    q hq hk hns P B hPB
  have hm : B.map K.subtype = K ⊓ H := by
    rw [subgroupOf_map_subtype,inf_comm]
  let eB : B ≃* (K ⊓ H : Subgroup G) :=
    (B.equivMapOfInjective K.subtype K.subtype_injective).trans (MulEquiv.subgroupCongr hm)
  let eQ := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  exact ⟨f.comp eQ.symm.toMonoidHom,hf.comp eQ.symm.injective⟩

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)


include hG hempty hM hu hmany hcard e hab hJ hs w

omit hs w [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)] in
private theorem original_partner_contains : J ≤ Mc :=
  (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
    (InitialSource.centralizer_le_partner T hu)

private theorem strict_intersection_quotient_card
    (hne : residualClosure J Mc ≠ residual J)
    {K : Subgroup G} (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    Nat.card ((K ⊓ J : Subgroup G) ⧸ pCore 2 (K ⊓ J : Subgroup G)) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hJM := original_partner_contains hG T hempty hM hu hmany hcard e hab J hJ
  let B := K ⊓ J
  let c := Nat.card (B ⧸ pCore 2 B)
  obtain ⟨f0,hf⟩ := intersection_torus_embedding T hJ.1.1.2 hJM hs hKM hK em
  have hd15 : c ∣ 15 := by
    have hd := card_dvd_of_injective f0 hf
    rwa [Nat.card_units,GaloisField.card 2 4 (by decide)] at hd
  have hdJ : c ∣ Nat.card J :=
    (card_quotient_dvd_card (pCore 2 B)).trans
      (card_dvd_of_le (show B ≤ J from inf_le_right))
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_card_eq
  obtain ⟨m,hm⟩ := (isPGroup_quotient_pResidual (G := J ⧸ pCore 2 J) 2).exists_card_eq
  have h25 := source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  have hcJ : Nat.card J = 2 ^ n * (25 * 2 ^ m) := by
    rw [←(pCore 2 J).card_mul_index,index_eq_card,hn,
      ←(pResidual 2 (J ⧸ pCore 2 J)).card_mul_index,index_eq_card,h25,hm]
  have hcop : Nat.Coprime c 2 := (by decide : Nat.Coprime 15 2).of_dvd_left hd15
  have hd25 : c ∣ 25 := by
    rw [hcJ] at hdJ
    exact (hcop.pow_right m).dvd_of_dvd_mul_right
      ((hcop.pow_right n).dvd_of_dvd_mul_left hdJ)
  have hc5 : c ∣ 5 := Nat.dvd_gcd hd15 hd25
  have hdK : 5 ∣ Nat.card (K.subgroupOf Mc) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv]
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 K))
    rw [Nat.card_congr em.some.toEquiv]
    exact Theory.PSL2.SixteenWreathComponents.five_dvd_card
  have hd := prime_dvd_intersection_of_subnormal_of_primeTo_index
    (J.subgroupOf Mc) (K.subgroupOf Mc)
    (source_quintic_strict_outside_index_primeTo_five hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w hne) hK.subnormal hdK
  have he : ((K.subgroupOf Mc) ⊓ (J.subgroupOf Mc)).map Mc.subtype = B := by
    rw [Subgroup.map_inf _ _ _ Mc.subtype_injective,
      map_subgroupOf_eq_of_le hKM,map_subgroupOf_eq_of_le hJM]
  have hdB : 5 ∣ Nat.card B := by
    rwa [←he,card_map_of_injective Mc.subtype_injective]
  obtain ⟨l,hl⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
  rw [←(pCore 2 B).card_mul_index,index_eq_card,hl] at hdB
  exact Nat.dvd_antisymm hc5
    (((by decide : Nat.Coprime 5 2).pow_right l).dvd_of_dvd_mul_left hdB)

/-- In the original no-index strict branch, both actual component
intersections have the prescribed two-core and quotient of order five.
The selected exchanged components are constructed, not additional premises. -/
theorem source_quintic_strict_component_intersections
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T),
      (b.K1 ⊓ J).pCoreIn 2 = b.K1 ⊓ (T : Subgroup G) ∧
      (b.K2 ⊓ J).pCoreIn 2 = b.K2 ⊓ (T : Subgroup G) ∧
      Nat.card ((b.K1 ⊓ J : Subgroup G) ⧸ pCore 2 (b.K1 ⊓ J : Subgroup G)) = 5 ∧
      Nat.card ((b.K2 ⊓ J : Subgroup G) ⧸ pCore 2 (b.K2 ⊓ J : Subgroup G)) = 5 := by
  obtain ⟨b⟩ := source_quintic_strict_factor_data hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w hne
  have hJM := original_partner_contains hG T hempty hM hu hmany hcard e hab J hJ
  exact ⟨b,component_intersection_core T hJ.1.1.2 hJM hs b.first_le b.first_component b.first_model,
    component_intersection_core T hJ.1.1.2 hJM hs b.second_le b.second_component b.second_model,
    strict_intersection_quotient_card hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w
      hne b.first_le b.first_component b.first_model,
    strict_intersection_quotient_card hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w
      hne b.second_le b.second_component b.second_model⟩

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
