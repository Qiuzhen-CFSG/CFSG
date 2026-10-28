module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.NonnormalProjection
public import Theory.GroupTheory.ComponentOrbitInner

/-!
# The original module lies in the actual overlap component orbit

The overlap Y=M intersect N_G(B) normalizes the fixed perfect residual.
Its inner action on a nonnormal component therefore transports across the
whole Y-orbit and combines into an inner action on that orbit. The binary
projection of V onto the orbit centralizer is Y-invariant. Covering uniqueness
for F join N_T(B) kills it, since otherwise the escaping component lies in M.

All subgroups remain on the actual odd-normalizer carrier and are embedded
through its literal subtype. Source: Aschbacher--Smith 4.4.10(2), printed p.621,
applied to the original nonnormal A5 pair in 10.2.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The unchanged fixed residual acts innerly on the full overlap orbit. -/
theorem source_oddNormalizer_residual_componentOrbit_inner
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    let N := normalizer (B : Set G)
    let K0 := componentOrbit K (D.maximalLocal.subgroupOf N)
    ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N ≤
      K0 ⊔ centralizer (K0 : Set N) := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let Y := D.maximalLocal.subgroupOf N
  have hYF : Y ≤ normalizer (F.subgroupOf N : Set N) := by
    have hnorm : D.maximalLocal ⊓ N ≤ normalizer (F : Set G) :=
      ((le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer B))).trans
        inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
    intro y hy f
    exact hnorm ⟨hy,y.property⟩ (f : G)
  exact hK.le_orbit_sup_centralizer_of_normalized_inner Y (F.subgroupOf N) hYF
    (source_oddNormalizer_nonnormal_component_inner D B hne K hK hnK hFK)

/-- The actual original module lies in the overlap orbit of the selected
nonnormal component; uniqueness retains the full F join N_T(B). -/
theorem source_a5_oddNormalizer_fullModule_le_componentOrbit
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    D.fullModule ≤
      (componentOrbit K (D.maximalLocal.subgroupOf (normalizer (B : Set G)))).map
        (normalizer (B : Set G)).subtype := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let Y := D.maximalLocal.subgroupOf N
  let K0 := componentOrbit K Y
  let J := K0.map N.subtype
  let A := Y.map N.subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ N)
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hinner : F ≤ J ⊔ centralizer (J : Set G) := by
    have hh := map_mono (f := N.subtype)
      (source_oddNormalizer_residual_componentOrbit_inner D B hne K hK hnK hFK)
    change (F.subgroupOf N).map N.subtype ≤
      (K0 ⊔ centralizer (K0 : Set N)).map N.subtype at hh
    rw [map_subgroupOf_eq_of_le hFN,Subgroup.map_sup] at hh
    exact hh.trans (sup_le_sup le_rfl (map_centralizer_le_centralizer_image _ _))
  obtain ⟨_,_,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hV : IsPGroup 2 D.fullModule := (isPGroup_pCoreIn 2 F).to_le hVF
  have hAJ : A ≤ normalizer (J : Set G) :=
    (map_mono (le_normalizer_componentOrbit K Y)).trans (K0.le_normalizer_map N.subtype)
  have hAV : A ≤ normalizer (D.fullModule : Set G) := by
    rw [source_fullModule_normalizer D]
    rintro x ⟨y,hy,rfl⟩
    exact hy
  obtain ⟨hIM,hIN,_,_⟩ := source_oddActor_normalizerJoin_input D B hBC hodd hBV
  have hIA : I ≤ A := by
    intro x hx
    exact ⟨⟨x,hIN hx⟩,hIM hx,rfl⟩
  have houtJ : ¬ J ≤ D.maximalLocal :=
    fun hh => houtK ((map_mono (le_componentOrbit K Y)).trans hh)
  exact binary_subgroup_le_of_normalized_inner_product_uniqueness J D.fullModule A I
    D.maximalLocal hV (hVF.trans ((pCoreIn_le 2 F).trans hinner)) hAJ hAV hIA
    (source_a5_oddPrimeNormalizer_covering_uniqueness D e hn hp B hB hBC hBV hperm).2.2 houtJ

/-- The same placement on the literal odd-normalizer carrier. -/
theorem source_a5_oddNormalizer_fullModule_subgroupOf_le_componentOrbit
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    D.fullModule.subgroupOf (normalizer (B : Set G)) ≤
      componentOrbit K (D.maximalLocal.subgroupOf (normalizer (B : Set G))) := by
  have hh := source_a5_oddNormalizer_fullModule_le_componentOrbit D e hn hp B hne
    hB hBC hBV hperm K hK hnK houtK hFK
  intro v hv
  obtain ⟨w,hw,he⟩ := hh hv
  have he' : w = v := Subtype.ext he
  exact he' ▸ hw

end CFSG.Quasithin.Chapter10
