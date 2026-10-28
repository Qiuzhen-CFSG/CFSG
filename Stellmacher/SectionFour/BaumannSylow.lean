module
public import Stellmacher.SectionFour.TwoThreeHypotheses
public import Stellmacher.SectionTwo.NormalSupplementBaumannSetup
public import Stellmacher.BaumannMap

/-!
# Sylow control of the actual Baumann normal closure

In the critical-partner configuration of Stellmacher (4.6), the Baumann
subgroup B₀ of O₂(C) is a Sylow two-subgroup of its normal closure in Pstar.
The theorem retains the original finite ambient group and the prescribed
residual-core product E, without assuming Pstar normal in that ambient group.

Apply (2.3) inside the native group E.subgroupOf Pstar using the exact Sylow
and core equality supplied by TwoThreeHypotheses. The injective Baumann-map
theorem identifies its subgroup with B₀. NormalSupplement supplies E normal
in Pstar, ES=Pstar, and normalization of O₂(C) by the native image of S;
this image therefore also normalizes B₀. The normal-supplement closure
identity identifies the native closure with the closure inside Pstar.
Mapping its Sylow witness through the two subtype maps gives the ambient
conclusion. The Sylow witnesses from the two prerequisite APIs are compared
by their injective images, so no equality of arbitrary choices is assumed.

Source: Stellmacher, Journal of Algebra 190 (1997), (4.6), journal p26,
the sentence applying (2.3) to obtain B₀ ∈ Syl₂(L).
-/

open scoped Pointwise
namespace Stellmacher.SectionFour

private theorem sylow_map_range
    {H G : Type*} [Group H] [Group G] [Finite H]
    (f : H →* G) (T : Sylow 2 H) :
    IsSylowSubgroupIn ((T : Subgroup H).map f) f.range := by
  let U := T.mapSurjective f.rangeRestrict_surjective
  refine ⟨U, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  congr 1


/-- The literal Baumann subgroup of O₂(C) is Sylow in its Pstar-normal closure. -/
public theorem baumann_isSylow_normalClosure
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
    IsSylowSubgroupIn B
      ((Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)).map Pstar.subtype) := by
  obtain ⟨Q, hQhyp, hQmap, hcore⟩ :=
    baumann_two_three_hypotheses S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  obtain ⟨hEN, _, _, _, SP, Q', hSP, hQ'map, hgen, _, _, hSN⟩ :=
    baumann_normal_supplement_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  let N := E.subgroupOf Pstar
  let _ : N.Normal := hEN
  let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
  let b := (Q : Subgroup N) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (Q : Subgroup N)) : Set N)
  have hQinner : (Q : Subgroup N).map N.subtype = (Q' : Subgroup N).map N.subtype := by
    apply Subgroup.map_injective Pstar.subtype_injective
    exact hQmap.trans hQ'map.symm
  have hbmap : (b.map N.subtype).map Pstar.subtype = B := by
    rw [Subgroup.map_map]
    change ((Q : Subgroup N) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (Q : Subgroup N)) : Set N)).map
        (Pstar.subtype.comp N.subtype) = B
    rw [baumann_map_injective (Pstar.subtype.comp N.subtype)
      (fun x y hxy => N.subtype_injective (Pstar.subtype_injective hxy)),
      ← Subgroup.map_map, hQmap]
  have hBP : B ≤ Pstar := by
    rw [← hbmap]
    exact Subgroup.map_subtype_le _
  have hBsub : B.subgroupOf Pstar = b.map N.subtype := by
    apply Subgroup.map_injective Pstar.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hBP, hbmap]
  have hSBN : (SP : Subgroup Pstar) ≤
      Subgroup.normalizer (B.subgroupOf Pstar : Set Pstar) := by
    rw [hBsub, baumann_map_injective N.subtype N.subtype_injective,
      hQinner]
    exact hSN.trans (normalizer_le_normalizer_baumann _)
  have hnative := SectionTwo.baumann_sylow_of_native_two_three N (SP : Subgroup Pstar)
    (B.subgroupOf Pstar) hQhyp Q hcore hgen hBsub hSBN
  let L := Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)
  obtain ⟨T, hT⟩ := hnative
  let f : L →* G := Pstar.subtype.comp L.subtype
  have hf : f.range = L.map Pstar.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h := sylow_map_range f T
  rw [hf] at h
  have hTm : (T : Subgroup L).map f = B := by
    change (T : Subgroup L).map (Pstar.subtype.comp L.subtype) = B
    rw [← Subgroup.map_map, hT, Subgroup.map_subgroupOf_eq_of_le hBP]
  rwa [hTm] at h

end Stellmacher.SectionFour
