module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCoreNoExchange
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedBorelAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointCoreCover
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedResidualFactors
public import Theory.GroupTheory.PCoreCommutingProduct
public import Theory.GroupTheory.PCoreImage

/-!
# The literal paired point-core cover in 14.6.9

Independent cubic actors prevent the normal two-core of I ∩ Mc from
exchanging the blocks. Its two marked normalizer actions lie in the two
Klein fours. Lifting both images leaves the original core O₂(I).
Once D vanishes, that core lies in the join of the two point cores.

Source: Aschbacher–Smith, proof of 14.6.9(l), printed p.1027.
-/
public section
open Subgroup BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Before eliminating D, the only additional kernel is the original core. -/
theorem source_paired_point_core_cover_mod_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    (I ⊓ Mc).pCoreIn 2 ≤
      ((((b.block i).map I.subtype ⊓ Mc).pCoreIn 2 ⊔
        ((b.block j).map I.subtype ⊓ Mc).pCoreIn 2) ⊔ I.pCoreIn 2) := by
  let R := (T : Subgroup G) ⊓ I
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let Iz := I ⊓ Mc
  let W := Iz.pCoreIn 2
  obtain ⟨h,h',hmark,hmark',_,_,hRIz,_⟩ := source_paired_borel_action_inputs
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨P,hP⟩ := c.sylow.exists_map_subtype_eq_of_le
    (show Iz ≤ I from inf_le_left) (by rw [c.sylow_image]; exact hRIz)
  have hWR : W ≤ R := (pCoreIn_le_sylow Iz P).trans_eq (hP.trans c.sylow_image)
  have hWN := source_paired_point_core_normalizes_blocks
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hIzW : Iz ≤ normalizer (W : Set G) := Iz.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Iz (pCore 2 Iz))
  have hPcore {K L : Subgroup G} (d : AlternatingPairSetup R K L) :
      (K ⊓ Mc).pCoreIn 2 ≤ R := by
    obtain ⟨PK,hPK⟩ := d.sylow.exists_map_subtype_eq_of_le
      (show K ⊓ Mc ≤ K from inf_le_left) (by
        rw [d.sylow_image]
        exact le_inf inf_le_right (inf_le_left.trans (hRIz.trans inf_le_right)))
    exact ((pCoreIn_le_sylow (K ⊓ Mc) PK).trans_eq
      (hPK.trans d.sylow_image)).trans inf_le_left
  have hfull : R ⊓ centralizer ((sourceModule K₁ ⊔ sourceModule K₂ : Subgroup G) : Set G) =
      I.pCoreIn 2 := by
    simpa only [ambientModule_eq_literal,K₁,K₂,R,ChapterC.Section05.ConjugateSource.sourceModule,moduleLayer] using
      Section06.Original.pair_core_centralizer c b i j hij hs
  apply h.paired_point_core_cover h' hmark hmark' (isPGroup_pCoreIn 2 Iz)
    hWR hWN _ (hPcore h) (hPcore h') hfull.le
  exact (sup_le (inf_le_inf (map_subtype_le _) le_rfl)
    (inf_le_inf (map_subtype_le _) le_rfl)).trans hIzW

/-- With the residual centralizer eliminated, the actual point core is the
join of the two original block point cores. -/
theorem source_paired_point_core_cover
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2)
    (hD : ((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) = ⊥) :
    (I ⊓ Mc).pCoreIn 2 =
      ((b.block i).map I.subtype ⊓ Mc).pCoreIn 2 ⊔
        ((b.block j).map I.subtype ⊓ Mc).pCoreIn 2 := by
  let R := (T : Subgroup G) ⊓ I
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let K := (pResidual 2 I).map I.subtype
  let Y := (K₁ ⊓ Mc) ⊔ (K₂ ⊓ Mc)
  obtain ⟨h,h',_,_,_,_,hRIz,_⟩ := source_paired_borel_action_inputs
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨hd,hc,_,_⟩ := source_paired_point_centralizer_product
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hY : Y ≤ I ⊓ Mc := sup_le (inf_le_inf (map_subtype_le _) le_rfl)
    (inf_le_inf (map_subtype_le _) le_rfl)
  have hNY : I ⊓ Mc ≤ normalizer (Y : Set G) :=
    source_paired_point_centralizer_normalizes
      hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hYcore : Y.pCoreIn 2 = (K₁ ⊓ Mc).pCoreIn 2 ⊔ (K₂ ⊓ Mc).pCoreIn 2 :=
    pCoreIn_sup_of_disjoint_of_commuting 2 _ _ (hd.mono inf_le_left inf_le_left)
      (inf_le_left.trans (hc.trans (centralizer_le inf_le_left)))
  have hcoreK {X L : Subgroup G} (d : AlternatingPairSetup R X L) :
      X.pCoreIn 2 ≤ (X ⊓ Mc).pCoreIn 2 := by
    have hXR : X.pCoreIn 2 ≤ R :=
      ((pCoreIn_le_sylow X d.sylow).trans_eq d.sylow_image).trans inf_le_left
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X)
      (le_inf (pCoreIn_le 2 X) (hXR.trans (hRIz.trans inf_le_right)))
    exact inf_le_left.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  obtain ⟨_,_,_,_,_,hcore,_⟩ := c.alternating_pair_family b i j hij hs hi hpairIndex
  have hIK : I.pCoreIn 2 = K.pCoreIn 2 := by
    simpa only [hD,sup_bot_eq] using hcore
  have hjoin : K₁ ⊔ K₂ = K := c.pair_join b i j hij hs
  have hA : I.pCoreIn 2 ≤ (K₁ ⊓ Mc).pCoreIn 2 ⊔ (K₂ ⊓ Mc).pCoreIn 2 := by
    rw [hIK,←hjoin,
      pCoreIn_sup_of_disjoint_of_commuting 2 K₁ K₂ hd hc]
    exact sup_le_sup (hcoreK h) (hcoreK h')
  apply le_antisymm
  · exact (source_paired_point_core_cover_mod_core
      hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi).trans
        (sup_le le_rfl hA)
  · rw [←hYcore]
    exact pCoreIn_mono_of_normalizes hY hNY

end CFSG.Quasithin.Chapter14.Section06
