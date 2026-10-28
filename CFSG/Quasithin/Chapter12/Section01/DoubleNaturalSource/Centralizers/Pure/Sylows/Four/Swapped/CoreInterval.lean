module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.CoreAction
public import Theory.SpecificGroups.PSL2.SmallCubicCore

/-!
# Exact core indices in the original swapped-component quotient

Write K₀ = ⟨Kᵀ⟩ and R = O₂(X(T ∩ K₀)). In the remaining odd-prime
case, O₂(X) lies in O₂(K₀), so the original residual image is its cubic
plane. The actual product marking and the full quotient Sylow identify
the image of R as a four-group. Pulling back the literal quotient map
gives [R:O₂(K₀)] = [T ∩ K₀:R] = 4, with both containments proved.
The containing-core bounds put O₂(K₀) and O₂(H) in the original XT core.

`ModuleGeometry` applies these results to the original contrary point-Sylow
configuration. They do not exclude the nonabelian containing core. The
ambient Sylow contradiction and pure fusion/closure remain with this task.
The original MS fixed-subgroup premise remains with `qt-rank-two-ms93`
and final owner `qt-d-double-natural-centralizers`.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791. The quotient
calculation adapts the proved 10.2.5 calculation in
`BinaryThreeAction/OddSmallCoreSize` to these literal subgroups.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter1 Chapter1.XiEmbedding InvariantThree
variable {G : Type*} [Group G] [Finite G]

private theorem swapped_parabolic_core_image (T : Sylow 2 G) {X A H I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I) :
    let K := componentOrbit I (T : Subgroup G)
    quotientImage K ((X ⊔ ((T : Subgroup G) ⊓ K)).pCoreIn 2) =
      (quotientImage K X ⊔ quotientImage K (T : Subgroup G)).pCoreIn 2 := by
  let K := componentOrbit I (T : Subgroup G)
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  have hXK := hs.toLocalInput.le_of_complement_le hs.complement_le_orbit hHK
  let J := X ⊔ ((T : Subgroup G) ⊓ K)
  have hJK : J ≤ K := sup_le hXK inf_le_right
  change ((J.pCoreIn 2).subgroupOf K).map _ = _
  rw [←pCoreIn_subgroupOf 2 J K hJK,
    map_pCoreIn_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)]
  congr 1
  rw [show J = X ⊔ ((T : Subgroup G) ⊓ K) from rfl,
    subgroupOf_sup hXK inf_le_right,Subgroup.map_sup,inf_subgroupOf_right]
  rfl

/-- The original parabolic core has image of order four in K₀/O₂(K₀). -/
theorem collapsed_quotient_parabolic_core_card (T : Sylow 2 G) {X A H I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hc : X.pCoreIn 2 ≤ (componentOrbit I (T : Subgroup G)).pCoreIn 2) :
    let K := componentOrbit I (T : Subgroup G)
    Nat.card (quotientImage K ((X ⊔ ((T : Subgroup G) ⊓ K)).pCoreIn 2)) = 4 := by
  let K := componentOrbit I (T : Subgroup G)
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  have hXK := hs.toLocalInput.le_of_complement_le hs.complement_le_orbit hHK
  obtain ⟨S,hS⟩ := component_quotient_sylow hs.sylow_two hKH hs.orbit_normal
  obtain ⟨e,_,_,_⟩ := swapped_quotient_subgroup T hs X hs.invariant
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput e)
  let : IsElementaryAbelian 3 A := hpc.1
  let ep := complementEquiv hs.toLocalInput hs.complement_le_orbit
  let A' := quotientImage K A
  let : IsElementaryAbelian 3 A' :=
    IsElementaryAbelian.of_surjective ep.toMonoidHom ep.surjective
  have hA : Nat.card A' = 9 := (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let j := e.trans (eF.prodCongr eF)
  have hr : primeRank 3 (PSL(2,F) × PSL(2,F)) ≤ 2 := by
    rw [←primeRank_congr 3 j]
    exact (SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).stronglyQuasithin 3
      (by decide) (by decide)
  have hthree : IsPGroup 3 (A'.map j.toMonoidHom) :=
    (IsElementaryAbelian.isPGroup 3 A').map _
  let : IsCyclic ((A'.map j.toMonoidHom).map (MonoidHom.fst PSL(2,F) PSL(2,F))) :=
    SwappedFactorsProof.cyclic_pSubgroup_of_product_rank (by decide) hr _ (hthree.map _)
  let : IsCyclic ((A'.map j.toMonoidHom).map (MonoidHom.snd PSL(2,F) PSL(2,F))) :=
    SwappedFactorsProof.cyclic_pSubgroup_of_product_rank (by decide) hr _ (hthree.map _)
  have hN : (S : Subgroup (XiQuotient K)) ≤ normalizer (A' : Set _) := by
    rw [hS,show A' = quotientImage K X from
      (collapsed_quotient_residual_eq_complement T hs hc).symm]
    apply (map_mono ?_).trans (le_normalizer_map (QuotientGroup.mk' (pCore 2 K)))
    rw [←subgroupOf_normalizer_eq hXK]
    exact subgroupOf_mono K hs.invariant
  dsimp only
  rw [swapped_parabolic_core_image T hs,collapsed_quotient_residual_eq_complement T hs hc,←hS]
  exact Theory.PSL2.small_pair_cubic_core_card_of_equiv j
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩
    (Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (hF ▸ ho) (hF ▸ hmod)) S A' hA hN

omit [Finite G] in
private theorem quotientImage_card {K A : Subgroup G} (hA : A ≤ K) :
    Nat.card (quotientImage K A) = (K.pCoreIn 2).relIndex A := by
  have he : (K.pCoreIn 2).subgroupOf K = pCore 2 K :=
    comap_map_eq_self_of_injective K.subtype_injective _
  have hm := relIndex_ker (A.subgroupOf K) (QuotientGroup.mk' (pCore 2 K))
  rw [QuotientGroup.ker_mk'] at hm
  rw [←relIndex_subgroupOf hA,he]
  exact hm.symm

/-- Both steps in the actual core interval have index four. -/
theorem collapsed_parabolic_core_relIndex (T : Sylow 2 G) {X A H I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hc : X.pCoreIn 2 ≤ (componentOrbit I (T : Subgroup G)).pCoreIn 2) :
    let K := componentOrbit I (T : Subgroup G)
    let R := (X ⊔ ((T : Subgroup G) ⊓ K)).pCoreIn 2
    K.pCoreIn 2 ≤ R ∧ R ≤ (T : Subgroup G) ⊓ K ∧
      (K.pCoreIn 2).relIndex R = 4 ∧ R.relIndex ((T : Subgroup G) ⊓ K) = 4 := by
  let K := componentOrbit I (T : Subgroup G)
  let J := X ⊔ ((T : Subgroup G) ⊓ K)
  let R := J.pCoreIn 2
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  have hXK := hs.toLocalInput.le_of_complement_le hs.complement_le_orbit hHK
  have hJK : J ≤ K := sup_le hXK inf_le_right
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (le_sup_right.trans hs.overgroup).trans hHK
  have hJN : X ⊔ (T : Subgroup G) ≤ normalizer (J : Set G) := by
    apply sup_le ((show X ≤ J from le_sup_left).trans J.le_normalizer)
    exact (le_inf hs.invariant
      ((le_inf (T : Subgroup G).le_normalizer hTK).trans
        inf_normalizer_le_normalizer_inf)).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hRT : R ≤ (T : Subgroup G) := by
    apply (pCoreIn_mono_of_normalizes
      (show J ≤ X ⊔ (T : Subgroup G) from sup_le le_sup_left (inf_le_left.trans le_sup_right)) hJN).trans
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (X ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hRS : R ≤ (T : Subgroup G) ⊓ K := le_inf hRT ((pCoreIn_le 2 J).trans hJK)
  have hcS := SwappedSylow.orbit_core_le_two hs
  have hQR : K.pCoreIn 2 ≤ R :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) (hcS.trans le_sup_right)
      (hJK.trans (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))))
  have hfour : (K.pCoreIn 2).relIndex R = 4 := by
    rw [←quotientImage_card (hRS.trans inf_le_right)]
    exact collapsed_quotient_parabolic_core_card T hs hp ho hm hmod hc
  refine ⟨hQR,hRS,hfour,?_⟩
  obtain ⟨U,hU⟩ := component_quotient_sylow hs.sylow_two hKH hs.orbit_normal
  obtain ⟨e,_,_,_⟩ := swapped_quotient_subgroup T hs X hs.invariant
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let j := e.trans (eF.prodCongr eF)
  have h16 : Nat.card U = 16 := by
    have hh := Theory.PSL2.small_pair_sylow_card
      ⟨p,1,hp,ho,by decide,by simpa using hF⟩
      (Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (hF ▸ ho) (hF ▸ hmod))
      (U.mapSurjective (f := j.toMonoidHom) j.surjective)
    exact (Nat.card_congr (j.subgroupMap U).toEquiv).trans hh
  have hi : (K.pCoreIn 2).relIndex ((T : Subgroup G) ⊓ K) = 16 := by
    rw [←quotientImage_card (show (T : Subgroup G) ⊓ K ≤ K from inf_le_right)]
    unfold quotientImage
    rw [inf_subgroupOf_right]
    change Nat.card (quotientImage K (T : Subgroup G)) = 16
    rw [←hU]
    exact h16
  have hmul := relIndex_mul_relIndex (K.pCoreIn 2) R ((T : Subgroup G) ⊓ K) hQR hRS
  rw [hfour,hi] at hmul
  change R.relIndex ((T : Subgroup G) ⊓ K) = 4
  omega
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Both containing cores lie in the original XT core, with relative normality. -/
theorem swapped_containing_core_bounds (T : Sylow 2 G) {X A H I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I) :
    (componentOrbit I (T : Subgroup G)).pCoreIn 2 ≤ H.pCoreIn 2 ∧
      H.pCoreIn 2 ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let K := componentOrbit I (T : Subgroup G)
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hs.overgroup
  have hcoreT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  refine ⟨pCoreIn_mono_of_normalizes hKH hHK,?_⟩
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (hcoreT.trans le_sup_right)
    (hs.overgroup.trans (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
