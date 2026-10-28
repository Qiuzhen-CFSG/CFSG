module

public import CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.Kernel
public import Theory.SpecificGroups.SymmetricEight.ComponentKernel
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank

/-!
# The source A₈ kernel and the maximal bad involution bound

For the literal odd-E orbit X above a bad involution, the original K is a
proper component of C_X(t). Its A₆ order and X ≃ A₈ give the compatible
six-point marking, hence the full fixer in Aut(X) has order at most two.
The original central involution t belongs to R and acts nontrivially on X,
so D=C_R(X) has index exactly two. The source maximality argument now gives
|R| ≤ 4: the nonnormal alternative is excluded by the quasithin A₆ theorem.

Source: Aschbacher–Smith, 2.5.19, printed pp.561–563. The only remaining
model premise is identification of the literal orbit with A₈; its producer
belongs to the source overcomponent classification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection OvercomponentsSource
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The literal A₈ source kernel has index two, with marking and nontriviality
of the original actor both derived internally. -/
theorem source_a8_orbit_kernel_index_two
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* alternatingGroup (Fin 6))
    (i : G) (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i)
    (eX : ((componentOrbit (K.subgroupOf (centralizer ({i} : Set G)))
      (oddELayer (centralizer ({i} : Set G)))).map
      (centralizer ({i} : Set G)).subtype) ≃* alternatingGroup (Fin 8)) :
    let Gi := centralizer ({i} : Set G)
    let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
    let R := ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓ Gi
    ((R ⊓ centralizer (X.map Gi.subtype : Set G)).subgroupOf R).index = 2 := by
  let : (K.subgroupOf H).Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) (K.subgroupOf H)
    ((subgroupOfEquivOfLe c.component_le).trans eK) c.component
  let Y := (S : Subgroup H).map H.subtype
  let Gi := centralizer ({i} : Set G)
  let O := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
  let X := O.map Gi.subtype
  let R := (Y ⊓ centralizer (K : Set G)) ⊓ Gi
  obtain ⟨t,ht,htC,htZ⟩ := MathieuSourceSetup.exists_central_core_involution c
  have hKt := source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  obtain ⟨hsub,hKX,hN⟩ := source_overcomponent_orbit_subnormal c hG hempty hgen hb hstar
    t i ht htC htZ hi.2.1 hi.1.1 hi.1.2
  have hXsub : (X.subgroupOf Gi).IsSubnormal := by
    change ((O.map Gi.subtype).comap Gi.subtype).IsSubnormal
    rw [comap_map_eq_self_of_injective Gi.subtype_injective]
    exact hsub
  have hproper : K < X := by
    refine lt_iff_le_not_ge.mpr ⟨hKX, ?_⟩
    intro hXK
    exact hi.2.2 ((hKt.restrict hKX (hXK.trans hKt.1)).of_subnormal
      (map_subtype_le _) hXsub)
  have hRN : R ≤ normalizer (X : Set G) := by
    apply le_trans ?_ hN
    exact le_inf inf_le_right
      (inf_le_left.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
  have htR : t ∈ R := by
    refine ⟨?_, mem_centralizer_singleton_iff.mpr (htZ.2 i hi.1.1).symm⟩
    rw [← MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact htC
  have htXC : t ∉ centralizer (X : Set G) := by
    intro htXC
    exact (source_overcomponent_kernel_involutions c hG hempty hgen hb hstar
      t i ht htC htZ hi.2.1 hi.1.1 hi.1.2 hi.2.2 t htXC) hKt
  have hcard : Nat.card K = 360 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hfix := Theory.SpecificGroups.SymmetricEight.ComponentKernel.component_fixer_card_le_two
    eX (hRN htR) ht hproper (hKt.restrict (le_inf hKX hKt.1) inf_le_right) hcard
  exact Theory.SpecificGroups.SymmetricEight.ComponentKernel.actor_centralizer_index_two
    hRN (inf_le_left.trans inf_le_right) hfix htR htXC

/-- The actual maximal bad involution has centralizer intersection of order at
most four in the A₈ orbit case. A₆ normality excludes the other source branch. -/
theorem source_maximal_a8_orbit_card_le_four
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* alternatingGroup (Fin 6))
    (i : G) (hi : MaximalBadInvolution ((S : Subgroup H).map H.subtype) K i)
    (eX : ((componentOrbit (K.subgroupOf (centralizer ({i} : Set G)))
      (oddELayer (centralizer ({i} : Set G)))).map
      (centralizer ({i} : Set G)).subtype) ≃* alternatingGroup (Fin 8)) :
    Nat.card ((((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G)) : Subgroup G) ≤ 4 := by
  have hn : (K.subgroupOf H).Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) (K.subgroupOf H)
    ((subgroupOfEquivOfLe c.component_le).trans eK) c.component
  have hCiN : (S : Subgroup H).map H.subtype ⊓ centralizer ({i} : Set G) ≤
      normalizer (K : Set G) :=
    inf_le_left.trans ((map_subtype_le _).trans
      ((normal_subgroupOf_iff_le_normalizer c.component_le).mp hn))
  exact (source_maximal_kernel_dichotomy c hG hempty hgen hb hstar i hi hCiN
    (source_a8_orbit_kernel_index_two c hG hempty hgen hb hstar eK i hi.1 eX)).resolve_right
      (fun h => h.1 hn)

/-- Uniform A₈ orbit identification closes the source centralizer-four conclusion
for every bad involution, using the actual maximal bad choice internally. -/
theorem source_a8_orbits_centralizer_four
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* alternatingGroup (Fin 6))
    (horbits : ∀ j : G, BadInvolution ((S : Subgroup H).map H.subtype) K j →
      Nonempty (((componentOrbit (K.subgroupOf (centralizer ({j} : Set G)))
        (oddELayer (centralizer ({j} : Set G)))).map
        (centralizer ({j} : Set G)).subtype) ≃* alternatingGroup (Fin 8)))
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (i : G) (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i) :
    (((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G)) = zpowers i ⊔ zpowers t ∧
      IsKleinFour ((((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
        centralizer ({i} : Set G)) : Subgroup G) := by
  let : (K.subgroupOf H).Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) (K.subgroupOf H)
    ((subgroupOfEquivOfLe c.component_le).trans eK) c.component
  let Y := (S : Subgroup H).map H.subtype
  let R := (Y ⊓ centralizer (K : Set G)) ⊓ centralizer ({i} : Set G)
  obtain ⟨j, hj⟩ := exists_maximal_bad_involution Y K ⟨i,hi⟩
  obtain ⟨eX⟩ := horbits j hj.1
  have hcard : Nat.card R ≤ 4 := (hj.2.1 i hi).trans
    (source_maximal_a8_orbit_card_le_four c hG hempty hgen hb hstar eK j hj eX)
  have hKt := source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  have hti : t ≠ i := by
    intro he
    exact hi.2.2 (he ▸ hKt)
  have hcomm : Commute t i := (htZ.2 i hi.1.1).symm
  have htR : t ∈ R := by
    refine ⟨?_, mem_centralizer_singleton_iff.mpr hcomm.eq⟩
    rw [← MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact htC
  have hiR : i ∈ R := ⟨hi.1, mem_centralizer_singleton_iff.mpr rfl⟩
  let V := closure ({t,i} : Set G)
  have hV : IsKleinFour V := isKleinFour_closure_pair_of_orderOf t i ht hi.2.1 hti hcomm
  have hVR : V ≤ R := (closure_le _).mpr (by rintro x (rfl | rfl) <;> assumption)
  have he : V = R := eq_of_le_of_card_ge hVR (by rw [hV.card_four]; exact hcard)
  have hVp : V = zpowers i ⊔ zpowers t := by
    apply le_antisymm
    · apply (closure_le _).mpr
      rintro x (rfl | rfl)
      · exact mem_sup_right (mem_zpowers _)
      · exact mem_sup_left (mem_zpowers _)
    · exact sup_le (zpowers_le.mpr (subset_closure (by simp)))
        (zpowers_le.mpr (subset_closure (by simp)))
  have hR : IsKleinFour R := he ▸ hV
  exact ⟨he.symm.trans hVp, hR⟩

end CFSG.Quasithin.Chapter2.Section05.Overcomponents
