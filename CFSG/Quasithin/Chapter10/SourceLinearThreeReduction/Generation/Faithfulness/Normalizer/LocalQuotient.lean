module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalPlacement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LowRank

/-!
# Quotient geometry and first model exclusions under local fixation

A containing component retains the actual perfect residual, its original
orbit quotient, and the nonzero local moved module. The module normalizer
lies in the M-intersection, which normalizes the residual; equality is not
needed or asserted. Passing to the full central quotient preserves the
moved module and doubles every odd rank of the original component quotient.

These literal maps exclude every odd-field PSL₂ row and all alternating
rows through degree nine. Their known outer actions discharge residual
placement, with no fixation of the full M-orbit.
Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), printed pp.621--623,745
(combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The local moved module and literal residual retain the original orbit quotient and normalizer control inside the component. -/
theorem source_local_oddActor_component_geometry
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    let N := normalizer (B : Set G)
    let F := ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
    let P := F.subgroupOf K
    let W := (V.subgroupOf N).subgroupOf K
    let MK := (D.maximalLocal.subgroupOf N).subgroupOf K
    Group.IsPerfect P ∧ P ≤ MK ∧ MK ≤ normalizer (P : Set K) ∧
      W ≠ ⊥ ∧ IsElementaryAbelian 2 W ∧ W ≤ P.pCoreIn 2 ∧
      W = ⁅W,P⁆ ∧ normalizer (W : Set K) ≤ MK ∧
      Nonempty ((P ⧸ pCore 2 P) ≃*
        (localOrbit T L ⧸ pCore 2 (localOrbit T L))) := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let F0 := F.subgroupOf N
  let P := F0.subgroupOf K
  let U := V.subgroupOf N
  let W := U.subgroupOf K
  let Y := D.maximalLocal.subgroupOf N
  let MK := Y.subgroupOf K
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVN : V ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,hm,hVF⟩ := source_local_oddActor_cover D V hVV hVX hNV B hBC hodd hBV
  have hUF : U ≤ F0 := subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))
  have hUK : U ≤ K := hUF.trans hFK
  let a : P ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFN)
  let := source_oddNormalizer_residual_perfect (T := T) (L := L) B
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFK).symm.toMonoidHom)
    (subgroupOfEquivOfLe hFK).symm.surjective
  have hFY : F ≤ D.maximalLocal :=
    ((map_subtype_le _).trans inf_le_left).trans (localOrbit T L).le_normalizer
  have hYF : Y ≤ normalizer (F0 : Set N) := by
    have hnorm : D.maximalLocal ⊓ N ≤ normalizer (F : Set G) :=
      ((le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer B))).trans
        inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
    intro y hy f
    exact hnorm ⟨hy,y.property⟩ (f : G)
  have hMP : MK ≤ normalizer (P : Set K) := by
    rw [←subgroupOf_normalizer_eq hFK]
    exact subgroupOf_mono K hYF
  have hW : W ≠ ⊥ := by
    intro hb
    have hbV : V = ⊥ := by
      apply le_bot_iff.mp
      intro v hv
      have hw : (⟨⟨v,hVN hv⟩,hUK hv⟩ : K) ∈ W := hv
      have he := mem_bot.mp (hb ▸ hw)
      exact mem_bot.mpr (congrArg (fun x : K => x.val.val) he)
    exact hne hbV
  have heW : IsElementaryAbelian 2 W := by
    let := D.fullModule_elementary (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal)
    let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hVV
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.comap_of_injective (p := 2)
      N.subtype N.subtype_injective V
    exact IsElementaryAbelian.comap_of_injective (p := 2) K.subtype K.subtype_injective U
  have hWP : W ≤ P.pCoreIn 2 := by
    rw [pCoreIn_subgroupOf 2 F0 K hFK,pCoreIn_subgroupOf 2 F N hFN]
    exact subgroupOf_mono K (subgroupOf_mono N hVF)
  have hmove : W = ⁅W,P⁆ := by
    change U.subgroupOf K = ⁅U.subgroupOf K,F0.subgroupOf K⁆
    rw [←SubgroupTransport.subgroupOf_commutator U F0 hUK hFK,
      ←SubgroupTransport.subgroupOf_commutator V F hVN hFN,←hm]
  have hnormal : normalizer (W : Set K) ≤ MK := by
    rw [←subgroupOf_normalizer_eq hUK,←subgroupOf_normalizer_eq hVN]
    let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
    exact subgroupOf_mono K (subgroupOf_mono N
      (normalizer_le_of_unique_maximalTwoLocal
        (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2
        ((IsElementaryAbelian.isPGroup 2 D.fullModule).to_le hVV) hne hNV))
  obtain ⟨q,_⟩ := source_oddActorResidual_orbit_quotient_equiv (D := D) (B := B) hBC hodd
  exact ⟨inferInstance,subgroupOf_mono K (subgroupOf_mono N hFY),hMP,hW,heW,hWP,
    hmove,hnormal,⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans q⟩⟩

private theorem center_bot_transfer {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hY : center Y = ⊥) : center X = ⊥ := by
  apply bot_unique
  intro x hx
  have hy := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center Y at hy
  rw [hY,mem_bot] at hy
  exact mem_bot.mpr (e.map_eq_one_iff.mp hy)

/-- The actual residual and moved module retain their ranks and action in K/Z(K). -/
theorem source_local_oddActor_component_quotient_geometry
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    let N := normalizer (B : Set G)
    let F := ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
    let P := F.subgroupOf K
    let W := (V.subgroupOf N).subgroupOf K
    let q := QuotientGroup.mk' (center K)
    Group.IsPerfect (P.map q) ∧ W.map q ≠ ⊥ ∧
      IsElementaryAbelian 2 (W.map q) ∧ W.map q = ⁅W.map q,P.map q⁆ ∧
      P.map q ≤ normalizer (W.map q : Set (K ⧸ center K)) ∧
      ∀ p : ℕ, p.Prime → Odd p →
        primeRank p (P.map q) = 2 * primeRank p (L ⧸ pCore 2 L) := by
  let N := normalizer (B : Set G)
  let F := (solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let P := (F.subgroupOf N).subgroupOf K
  let W := (V.subgroupOf N).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  obtain ⟨hP,_,_,hW,hE,_,hm,_,⟨a⟩⟩ :=
    source_local_oddActor_component_geometry D V hVV hne hVX hNV B hBC hodd hBV K hFK
  let : Group.IsPerfect P := hP
  obtain ⟨b⟩ := source_nonnormal_orbit_product_equiv D hn
  let e : (P ⧸ pCore 2 P) ≃*
      ((L ⧸ pCore 2 L) × (L ⧸ pCore 2 L)) := a.trans b
  have hc : center (P ⧸ pCore 2 P) = ⊥ := by
    have ht : center ((L ⧸ pCore 2 L) × (L ⧸ pCore 2 L)) = ⊥ := by
      rw [Subgroup.center_prod,source_nonnormal_component_core_center D hn]
      exact bot_prod_bot
    exact center_bot_transfer e ht
  obtain ⟨hp,hne,he,hmove,hnorm⟩ := CentralQuotientLocalMarking.moved_image P W hW hE hm
  refine ⟨hp,hne,he,hmove,hnorm,?_⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  rw [CentralQuotientLocalMarking.primeRank_map P hc ho,
    ←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 P) pCore_isPGroup,
    primeRank_congr p e,primeRank_prod_eq_add,two_mul]


variable
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
  (hVX : V = ⁅V,localOrbit T L⁆)
  (hNV : localJoin T L ≤ normalizer (V : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
  (K : Subgroup (normalizer (B : Set G)))
include D hn hVV hne hVX hNV hBC hodd hBV

/-- The image of the original moved module forces two-rank at least three,
retaining the full central kernel of the containing component. -/
theorem source_local_oddActor_quotient_twoRank_ge_three
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    3 ≤ primeRank 2 (K ⧸ center K) := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := F.subgroupOf K
  let W := (V.subgroupOf N).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  obtain ⟨hP,hW,hE,hm,_,_⟩ :=
    source_local_oddActor_component_quotient_geometry D hn V hVV hne hVX hNV B hBC hodd hBV K hFK
  obtain ⟨_,_,_,_,_,hWP,_,_,_⟩ :=
    source_local_oddActor_component_geometry D V hVV hne hVX hNV B hBC hodd hBV K hFK
  let : Group.IsPerfect (P.map q) := hP
  let : IsElementaryAbelian 2 (W.map q) := hE
  exact three_le_primeRank_of_perfect_moved_elementary (P.map q) (W.map q)
    (map_mono (hWP.trans (pCoreIn_le 2 P))) hW hm
variable {p : ℕ} [Fact p.Prime] (hp : Odd p) (hB : IsPGroup p B)
  (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
include hp hB hperm hK hout
omit hodd in
/-- Every odd-field PSL₂ row of B is excluded, with no restriction on the
field exponent beyond its actual field witness. -/
theorem source_local_oddPrimeActor_no_odd_linear_two_component
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 q) : False := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    ChapterA.Section03.SourceComponents.TheoremBOuter.linear_two_odd
      (Group.IsPerfect.not_isMulCommutative _) ho hm
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  have hlo := source_local_oddActor_quotient_twoRank_ge_three D hn V hVV hne hVX hNV B hBC (by
      obtain ⟨k,hk⟩ := hB.exists_card_eq
      rw [hk]
      exact hp.pow) hBV K
    (source_local_oddPrimeActor_residual_le_of_solvable_outer D hn V hVV hne hVX hNV
      hp B hB hBC hBV hperm K hK hout)

  have hup := ChapterA.Section02.odd_psl_two_twoRank_le_two ho hm
  omega

omit hodd in
/-- All alternating rows through degree nine are excluded under local fixation alone. -/
theorem source_local_oddPrimeActor_no_alternating_component
    {n : ℕ} (hn9 : n ≤ 9) (e : K ⧸ center K ≃* alternatingGroup (Fin n)) : False := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    ChapterA.Section03.SourceComponents.TheoremBOuter.alternating
      (Group.IsPerfect.not_isMulCommutative _) ⟨e⟩
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  have hFK := source_local_oddPrimeActor_residual_le_of_solvable_outer D hn V hVV hne hVX hNV
    hp B hB hBC hBV hperm K hK hout
  have ho : Odd (Nat.card B) := by
    obtain ⟨k,hk⟩ := hB.exists_card_eq
    rw [hk]
    exact hp.pow
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  apply Perfect.no_doubled_odd_ranks S (K ⧸ center K) Nat.prime_three
  · intro r hr hor
    let : Fact r.Prime := ⟨hr⟩
    obtain ⟨_,_,_,_,_,he⟩ :=
      source_local_oddActor_component_quotient_geometry D hn V hVV hne hVX hNV B hBC ho hBV K hFK
    exact (he r hr hor).symm.le.trans (primeRank_subgroup_le r _)
  · intro r hr hor hne
    let : Fact r.Prime := ⟨hr⟩
    rw [primeRank_congr r e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n r hr
        (by intro he; subst r; exact hor.not_two_dvd_nat (dvd_refl 2))]
    have hr5 : 5 ≤ r := by
      have h2 := hr.two_le
      have hodd := hor.not_two_dvd_nat
      omega
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hr.pos).mpr (by omega))

end CFSG.Quasithin.Chapter10
