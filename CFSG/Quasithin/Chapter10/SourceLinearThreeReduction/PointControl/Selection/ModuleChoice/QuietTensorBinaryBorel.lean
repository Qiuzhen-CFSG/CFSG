module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorFactorization
public import Theory.GroupTheory.CComponent.PairOvergroupContainment
public import Theory.SpecificGroups.PSL2.EvenOrder

/-!
# Binary component Borels in the original tensor point centralizer

The solvable Borel--Sylow join maps into the two actual binary PSL₂ factors.
It normalizes their full Sylow intersection, and the checked residual
normalizer theorem therefore places the Borel in M. Rank-one geometry and
the exchanged C-component overgroup theorem identify M intersect KT with
that Borel joined to the original T. Thus this same KT is an H-star and
has generation parameter at most two by the actual Hall-faithfulness bound.

All two-core kernels, original cubic complements, and quotient markings
are retained. The field-degree exclusion needs a further argument on this
extension; no equality of generation parameters with its simple quotient is
asserted. Source: Aschbacher--Smith 8.3.7, printed pp.724--725.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
open Chapter1 Chapter1.XiEmbedding ChapterF.Source
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {X P H I : Subgroup G}

private theorem binary_borel_facts
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X P H I)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 (2^n)) :
    RankOneBorelFacts I (T : Subgroup G) := by
  obtain ⟨S,hS⟩ := SwappedSylow.component_sylow hs
  apply rankOneBorelFacts_of_quotient I (T : Subgroup G) S hS
  obtain ⟨F,_,_,hF,⟨c⟩⟩ := hm
  exact rankOneSylowFacts_of_equiv _ c (rankOneSylowFacts_psl2 F n (by omega) hF _)

private theorem binary_solvable_overgroup_normalizes
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X P H I)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 (2^n))
    (A : Subgroup G) [Group.IsSolvable A] (hTA : (T : Subgroup G) ≤ A) :
    A ⊓ componentOrbit I (T : Subgroup G) ≤
      normalizer ((T : Subgroup G) ⊓ componentOrbit I (T : Subgroup G) : Set G) := by
  let K := componentOrbit I (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 K)
  obtain ⟨S,hS⟩ := SwappedSylow.orbit_quotient_sylow hs
  obtain ⟨c⟩ := swapped_product hs
  let S' := S.mapSurjective (f := c.toMonoidHom) c.surjective
  let B := (A.subgroupOf K).map q
  let B' := B.map c.toMonoidHom
  have hSB : (S : Subgroup (XiQuotient K)) ≤ B := by
    rw [hS]
    exact map_mono (comap_mono hTA)
  let : Group.IsSolvable (A.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := K.subtype.subgroupComap A) (by intro a b h; exact Subtype.ext (Subtype.ext (congrArg (fun x : A => (x : G)) h)))
  let : Group.IsSolvable B := Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  let : Group.IsSolvable B' := Group.isSolvable_of_surjective (c.toMonoidHom.subgroupMap_surjective B)
  let : Group.IsSolvable (B' ⊔ (S' : Subgroup (XiQuotient I × XiQuotient I)) : Subgroup _) := by
    have hS'B : (S' : Subgroup (XiQuotient I × XiQuotient I)) ≤ B' := map_mono hSB
    rw [sup_eq_left.mpr hS'B]
    infer_instance
  have hBN : B ≤ normalizer (S : Set (XiQuotient K)) := by
    apply (map_le_map_iff_of_injective (f := c.toMonoidHom) c.injective).mp
    change B.map c.toMonoidHom ≤ (normalizer ((S : Subgroup (XiQuotient K)) : Set _)).map c.toMonoidHom
    rw [map_equiv_normalizer_eq]
    exact SwappedSylow.binary_model_prod_le_normalizer hn hm S' B'
  change B ≤ normalizer ((S : Subgroup (XiQuotient K)) : Set _) at hBN
  rw [hS] at hBN
  change A ⊓ K ≤ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)
  apply le_normalizer_iff.mpr
  intro a ha s hs'
  let aK : K := ⟨a,ha.2⟩
  let sK : K := ⟨s,hs'.2⟩
  have hq : q (aK * sK * aK⁻¹) ∈ SwappedSylow.imageInOrbit I (T : Subgroup G) (T : Subgroup G) := by
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hBN (mem_map_of_mem q ha.1)) _).mp
      (mem_map_of_mem q hs'.1)
  have ht : aK * sK * aK⁻¹ ∈ (T : Subgroup G).subgroupOf K := by
    rw [←SwappedSylow.twoImage_preimage hs]
    exact hq
  exact ⟨ht,(aK * sK * aK⁻¹).property⟩

/-- The full binary component Borel normalizes the original cubic residual.
No normality of X in H, or component invariance under T, is assumed. -/
theorem swapped_binary_borel_normalizes
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X P H I)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 (2^n)) :
    RankOneBorelFacts I (T : Subgroup G) ∧
      borel I (T : Subgroup G) ≤ H ⊓ normalizer (X : Set G) := by
  have hb := binary_borel_facts hs hn hm
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hs.overgroup
  have hTN : (T : Subgroup G) ⊓ normalizer (I : Set G) ≤
      normalizer ((T : Subgroup G) ⊓ I : Set G) :=
    (le_inf (inf_le_left.trans (T : Subgroup G).le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf
  have hTB : (T : Subgroup G) ⊓ normalizer (I : Set G) ≤
      normalizer (borel I (T : Subgroup G) : Set G) :=
    (le_inf inf_le_right (hTN.trans (normalizer ((T : Subgroup G) ⊓ I : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let : Group.IsSolvable (borel I (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) :=
    hs.component.2.relative_local_adjoin_isSolvable hs.component.1 inf_le_left hTH T.isPGroup' hTB hb.solvable
  have hBKN := binary_solvable_overgroup_normalizes hs hn hm
    (borel I (T : Subgroup G) ⊔ (T : Subgroup G)) le_sup_right
  have hBK : borel I (T : Subgroup G) ≤ componentOrbit I (T : Subgroup G) :=
    inf_le_left.trans (le_componentOrbit I (T : Subgroup G))
  have hBH : borel I (T : Subgroup G) ≤ H := inf_le_left.trans hs.component.1
  exact ⟨hb,le_inf hBH ((le_inf hBH
    ((le_inf le_sup_left hBK).trans hBKN)).trans (swapped_binary_normalizer hs hn hm))⟩


variable {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem binary_point_mem_HOver {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ∈ Chapter1.HOver G (T : Set G) := by
  have hzInT := D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D) hzV
  have hcyc : zpowers z ≤ centralizer ({z} : Set G) := zpowers_le.mpr
    (mem_centralizer_singleton_iff.mpr rfl)
  have hncyc : centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
  have hcycCore := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le (zpowers_le.mpr hzInT)) hcyc hncyc
  refine ⟨?_,hzT⟩
  intro he
  exact hz1 (mem_bot.mp (he ▸ hcycCore (mem_zpowers z)))

private theorem binary_pair_proper_overgroups
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    {K : Subgroup G} (hK : K ∈ cComponentsIn (centralizer ({z} : Set G)))
    (hmove : ¬ (T : Subgroup G) ≤ normalizer (K : Set G))
    [IsSimpleGroup (XiQuotient K)] (heven : 2 ∣ Nat.card (XiQuotient K))
    (hb : RankOneBorelFacts K (T : Subgroup G)) :
    ∀ A : Subgroup G, (T : Subgroup G) ≤ A → A < K ⊔ (T : Subgroup G) →
      A ≤ borel K (T : Subgroup G) ⊔ (T : Subgroup G) := by
  let H := K ⊔ (T : Subgroup G)
  let I := K.subgroupOf H
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let B := borel K (T : Subgroup G) ⊔ (T : Subgroup G)
  have hKL : K ∈ Chapter1.L G (T : Subgroup G) :=
    (Chapter1.lemma_1_2_6 T (binary_point_mem_HOver D hzV hz1 hzT)).1 hK |>.2
  have hI : I.IsCComponent := hKL.1
  have hi : (normalizer (I : Set H)).index = 2 :=
    source_nonnormal_normalizer_index D.simpleQTKE hKL hmove
  let a := subgroupOfEquivOfLe (show K ≤ H from le_sup_left)
  let aq := QuotientGroup.congr (pCore 2 I) (pCore 2 K) a (pCore_map_iso 2 a)
  let : IsSimpleGroup (I ⧸ pCore 2 I) := aq.isSimpleGroup
  have hgen : I ⊔ (S : Subgroup H) = ⊤ := by
    change K.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [←subgroupOf_sup (show K ≤ H from le_sup_left) (show (T : Subgroup G) ≤ H from le_sup_right)]
    exact subgroupOf_self H
  have hlocal (A : Subgroup H) (hSA : I ⊓ (S : Subgroup H) ≤ A) (hAI : A < I) :
      A ≤ B.subgroupOf H := by
    have hAM : A.map H.subtype ≤ B := by
      apply le_trans (hb.unique_maximal _ ?_ ?_) le_sup_left
      · intro x hx
        have hxH : x ∈ H := (show K ≤ H from le_sup_left) hx.2
        exact mem_map_of_mem H.subtype
          (hSA (show (⟨x,hxH⟩ : H) ∈ I ⊓ (S : Subgroup H) from ⟨hx.2,hx.1⟩))
      · have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hAI
        rwa [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] at hh
    exact map_le_iff_le_comap.mp hAM
  have hbound := hI.pair_overgroups_le S I (B.subgroupOf H)
    (by rwa [Nat.card_congr aq.toEquiv]) hi hgen (fun _ hx => (show (T : Subgroup G) ≤ B from le_sup_right) hx) hlocal
  intro A hTA hAH
  have hAt : A.subgroupOf H < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => hAH.not_ge (subgroupOf_eq_top.mp he))
  have hh := hbound (A.subgroupOf H) (fun _ hx => hTA hx) hAt
  intro x hx
  exact hh (show (⟨x,hAH.le hx⟩ : H) ∈ A.subgroupOf H from hx)

/-- In the swapped binary row the literal component Borel lies in M, and
its Sylow join is exactly M intersect KT. Thus KT is the original H-star,
including any original two-core kernel and exchanged components. -/
theorem quiet_tensor_point_binary_hstar
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    {K : Subgroup G}
    (hs : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) d.X
        ((P : Subgroup d.X).map d.X.subtype) d.Gz K)
    (hclosure : CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩ = componentOrbit K (T : Subgroup G))
    {n : ℕ} (hn2 : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n)) :
    RankOneBorelFacts K (T : Subgroup G) ∧
      K ⊓ D.maximalLocal = borel K (T : Subgroup G) ∧
      (K ⊔ (T : Subgroup G)) ⊓ D.maximalLocal =
        borel K (T : Subgroup G) ⊔ (T : Subgroup G) ∧
      K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal ∧
      generationParameter (K ⊔ (T : Subgroup G) : Subgroup G) ≤ 2 := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  obtain ⟨hb,hBN⟩ := swapped_binary_borel_normalizes hs hn2 hm
  have hBM : borel K (T : Subgroup G) ≤ D.maximalLocal :=
    hBN.trans (quiet_tensor_point_normalizer_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
    le_sup_right.trans (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.1
  have hKM : ¬ K ≤ D.maximalLocal := by
    intro hKM
    exact quiet_tensor_point_normalClosure_not_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT P
      (hclosure.le.trans (iSup_conjugates_le_of_le_normalizer K (T : Subgroup G) D.maximalLocal hKM
        (hTM.trans D.maximalLocal.le_normalizer)))
  have hKM' : K ⊓ D.maximalLocal = borel K (T : Subgroup G) := by
    apply le_antisymm (hb.unique_maximal _ (le_inf inf_le_right (inf_le_left.trans hTM)) ?_)
      (le_inf inf_le_left hBM)
    exact lt_of_le_of_ne inf_le_left (fun he => hKM (he ▸ inf_le_right))
  let hA := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremC_knownSimple (G := Y)
  obtain ⟨_,hmodels⟩ := SwappedSylow.nonnormal_model_of_theoremsAC hA hC hs.toSwappedInput
  let : IsSimpleGroup (XiQuotient K) := SwappedFactorsProof.quotient_simple hs.toSwappedInput hmodels
  have heven : 2 ∣ Nat.card (XiQuotient K) := by
    obtain ⟨F,_,_,_,⟨a⟩⟩ := hm
    rw [Nat.card_congr a.toEquiv]
    exact Theory.PSL2.two_dvd_card
  have hproper := binary_pair_proper_overgroups D hzV hz1 hzT hs.component hs.not_invariant heven hb
  have hEM : (K ⊔ (T : Subgroup G)) ⊓ D.maximalLocal =
      borel K (T : Subgroup G) ⊔ (T : Subgroup G) := by
    apply le_antisymm
    · apply hproper _ (le_inf le_sup_right hTM)
      exact lt_of_le_of_ne inf_le_left (fun he => hKM (le_sup_left.trans (he ▸ inf_le_right)))
    · exact le_inf (sup_le_sup_right inf_le_left _) (sup_le hBM hTM)
  have hH : K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal := by
    have hOver := Chapter3.mem_HOver_of_sylow_interval T le_sup_right (sup_le hs.component.1 hzT)
      (binary_point_mem_HOver D hzV hz1 hzT)
    refine ⟨⟨hOver,fun hh => hKM (le_sup_left.trans hh)⟩,?_⟩
    intro A hA hAE
    by_contra hEA
    exact hA.2 ((hproper A hA.1.2 (lt_of_le_not_ge hAE hEA)).trans (sup_le hBM hTM))
  exact ⟨hb,hKM',hEM,hH,quiet_binaryThree_hstar_generation_le_two D hmany hmin hn hJ cL hH⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
