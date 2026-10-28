module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.Constrained
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Numerical
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Contracts
public import CFSG.Quasithin.ChapterA.Section01.RankActions.LargeElementary
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimple
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Odd-core removal for the literal half-Sylow overgroup

Crossed centralization makes the original moved factor a proper subgroup of
its full module. The general eight-element lower bound therefore supplies
the strict size bound in A.1.26. In every overgroup H of L₀N_T(L), that module
centralizes O(H), placing O(H) in M. Since O₂(M) is also in the half-join,
characteristic two of M forces O(H)=1.

The source module choice is used only to obtain this crossed action; the
conclusion is independent of the chosen seed. A nonconstrained containing
C-component is consequently quasisimple. Its original smaller factor still
has noncentral two-core, even after restriction to the containing component,
and its image modulo the containing center is not quasisimple.

The final applications retain the original containing pair, exchanger and
all odd-prime ranks. They discharge odd-core removal and the nonconstrained
quasisimplicity step of 10.2.6. Distinctness and the final embedding exclusions
remain with qt-d-10-nona5-half-sylow-unique. The independent ModuleChoiceAt
input belongs to qt-d-10-nona5-point-selection; its ultimate discharge is
retained by qt-d-10-nona5-point-control.

Source: Aschbacher--Smith, 10.2.6, printed pp.748--749, using A.1.26--28,
pp.25--26, and A.3.12, pp.47--48.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem uniqueness (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- Crossed centralization forces the full module to be larger than one moved factor. -/
theorem fullModule_card_gt_eight_of_crossed
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t : G} (ht : t ∈ (T : Subgroup G))
    (hc : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    8 < Nat.card D.fullModule := by
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule :=
    le_normalizer_iff_commutator_le_left.mp hLV
  have hne : ⁅D.fullModule,L⁆ ≠ D.fullModule := by
    intro he
    have hmap : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp
        (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))
    rw [he,hmap] at hc
    exact source_full_moved_ne_bot D (commutator_eq_bot_iff_le_centralizer.mpr hc)
  exact (source_full_moved_card_ge_eight D).trans_lt
    (lt_of_not_ge (fun h => hne (Subgroup.eq_of_le_of_card_ge hWV h)))

/-- The literal half-join places the odd core in the characteristic-two maximal local. -/
theorem oddCore_eq_bot_of_halfJoin_le
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hc : 8 < Nat.card D.fullModule) {H : Subgroup G} (hhalf : halfJoin T L ≤ H) :
    pPrimeCore 2 H = ⊥ := by
  let X := localOrbit T L
  let V := D.fullModule
  let M := D.maximalLocal
  let O := (pPrimeCore 2 H).map H.subtype
  let Q := M.pCoreIn 2
  have hXH : X ≤ H := le_sup_left.trans hhalf
  have hVH : V ≤ H := D.fullModule_le_orbit.trans hXH
  let := D.fullModule_elementary (uniqueness D)
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  have heH : V.subgroupOf H = ⁅V.subgroupOf H,X.subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hXH]
    exact D.fullModule_eq_commutator (uniqueness D)
  have hcH : 8 < Nat.card (V.subgroupOf H) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv]
  have hXP : IsPPerfect 2 (X.subgroupOf H) :=
    ((pResidual_eq_top_iff 2 _).mp D.orbit_residual).of_surjective
      (subgroupOfEquivOfLe hXH).symm.toMonoidHom (subgroupOfEquivOfLe hXH).symm.surjective
  have hh := ChapterA.large_elementary_commutator_centralizes_oddCore
    (D.simpleQTKE.quasithin.subgroup H) (X.subgroupOf H) (V.subgroupOf H) hXP hcH heH
  have hm := congrArg (Subgroup.map H.subtype) hh
  have hcomm : ⁅V,O⁆ = ⊥ := by
    simpa only [map_commutator,map_subgroupOf_eq_of_le hVH,Subgroup.map_bot] using hm
  have hOM : O ≤ M := by
    change O ≤ D.maximalLocal
    rw [← source_fullModule_normalizer D]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQH : Q ≤ H :=
    ((pCoreIn_le_pCoreIn_of_sylow T le_sup_right
      (sup_le X.le_normalizer (le_normalizer_componentOrbit L T))).trans
      (join_core_le_stabilizer D)).trans (le_sup_right.trans hhalf)
  have hHO : H ≤ normalizer (O : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pPrimeCore 2 H).le_normalizer_map H.subtype
  have hMQ : M ≤ normalizer (Q : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hdis : Q ⊓ O = ⊥ := by
    apply (disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 M).exists_card_eq
    rw [hk,card_map_of_injective H.subtype_injective]
    exact (pPrimeCore_coprime_card (G := H) (p := 2)).pow_left k
  have hQO : ⁅Q,O⁆ = ⊥ := by
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp (hOM.trans hMQ))
      (le_normalizer_iff_commutator_le_right.mp (hQH.trans hHO))).trans_eq hdis
  have hchar : M ⊓ centralizer (Q : Set G) ≤ Q :=
    Chapter1.mem_He_iff.mpr (D.simpleQTKE.evenCharacteristic T M
      (uniqueness D).normalizer_maximal (le_normalizer_componentOrbit L T))
  have hOQ : O ≤ Q := (le_inf hOM
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQO))).trans hchar
  have hO : O = ⊥ := bot_unique ((le_inf hOQ le_rfl).trans_eq hdis)
  apply map_injective H.subtype_injective
  simpa only [Subgroup.map_bot] using hO

/-- Reselect internally; odd-core vanishing is independent of the original seed. -/
theorem oddCore_eq_bot_of_moduleChoice
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {H : Subgroup G} (hhalf : halfJoin T L ≤ H) : pPrimeCore 2 H = ⊥ := by
  obtain ⟨E,_,t,ht,_,hc,_⟩ :=
    hchoice hmany L D.maximal D.faithful D.quasisimple hn hna
  exact oddCore_eq_bot_of_halfJoin_le E (fullModule_card_gt_eight_of_crossed E ht hc) hhalf

/-- The nonconstrained member of the actual containing pair is quasisimple. -/
theorem RankedEnlargement.quasisimple_of_nonconstrained
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H K : Subgroup G} {s : G}
    (E : RankedEnlargement D H s K)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hf : generalizedFitting K ≠ pCore 2 K) : IsQuasisimple K := by
  let j := subgroupOfEquivOfLe E.component.1
  rcases E.component.2.component_or_generalizedFitting_eq_pCore
    (oddCore_eq_bot_of_moduleChoice hchoice hmany D hn hna E.half_le) with hq | he
  · let := hq.2
    exact IsQuasisimple.of_mulEquiv j
  · apply (hf ?_).elim
    have hm := congrArg (Subgroup.map j.toMonoidHom) he
    simpa only [map_generalizedFitting_equiv,pCore_map_iso] using hm

/-- The original factor retains its noncentral two-core inside the selected component. -/
theorem RankedEnlargement.smaller_core_not_central
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H K : Subgroup G} {s : G}
    (E : RankedEnlargement D H s K) :
    ¬ ((L.map (MulAut.conj s).toMonoidHom).subgroupOf K).pCoreIn 2 ≤ center K := by
  let B := L.map (MulAut.conj s).toMonoidHom
  let c := (MulAut.conj s).toMonoidHom
  intro hc
  have hBC : B.pCoreIn 2 ≤ centralizer (B : Set G) := by
    intro b hb a ha
    have hbK : b ∈ K := E.strict.le (B.pCoreIn_le 2 hb)
    have haK : a ∈ K := E.strict.le ha
    have hbC : (⟨b,hbK⟩ : K) ∈ center K := by
      apply hc
      rw [pCoreIn_subgroupOf 2 B K E.strict.le]
      exact hb
    exact congrArg K.subtype (mem_center_iff.mp hbC ⟨a,haK⟩)
  have hLC : L.pCoreIn 2 ≤ centralizer (L : Set G) := by
    intro l hl a ha
    apply (MulAut.conj s).injective
    simpa only [map_mul,c,MulEquiv.coe_toMonoidHom] using hBC
      ((map_pCoreIn_of_injective 2 L c (MulAut.conj s).injective) ▸ mem_map_of_mem c hl)
      (c a) (mem_map_of_mem c ha)
  have hz := commutator_eq_bot_iff_le_centralizer.mpr
    ((source_full_moved_le_component_core D).trans hLC)
  rw [source_full_moved_eq_commutator D] at hz
  exact source_full_moved_ne_bot D hz

/-- Passing to the containing center does not turn the smaller factor into an ordinary component. -/
theorem RankedEnlargement.center_image_not_quasisimple
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H K : Subgroup G} {s : G}
    (E : RankedEnlargement D H s K) :
    ¬ IsQuasisimple (((L.map (MulAut.conj s).toMonoidHom).subgroupOf K).map
      (QuotientGroup.mk' (center K))) := by
  let A := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  let e : L ≃* A := ((MulAut.conj s).subgroupMap L).trans
    (subgroupOfEquivOfLe E.strict.le).symm
  let f := (q.subgroupMap A).comp e.toMonoidHom
  apply source_central_image_not_quasisimple D f
    ((q.subgroupMap_surjective A).comp e.surjective)
  intro l hl
  have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
  change q (e l : K) = 1 at hh
  have hc := (QuotientGroup.eq_one_iff (e l : K)).mp hh
  apply mem_center_iff.mpr
  intro m
  apply e.injective
  simp only [map_mul]
  apply Subtype.ext
  exact mem_center_iff.mp hc (e m : K)

/-- The actual strict pair member has either the full C.2.7 input or an ordinary
component with a noncentral smaller two-core. Distinctness remains separate. -/
theorem ContainingPair.exists_enlargement_cases
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂) (hne : K₁ ≠ K₂) :
    ∃ (s : G) (K : Subgroup G), RankedEnlargement D H s K ∧
      ¬ ((L.map (MulAut.conj s).toMonoidHom).subgroupOf K).pCoreIn 2 ≤ center K ∧
      (IsQuasisimple K ∨
        RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
          KnownSimple.IsKnownSimple H ((localJoin T L).pCoreIn 2) (H ⊓ D.maximalLocal) K) := by
  obtain ⟨s,K,E⟩ := C.exists_rankedEnlargement hn hne
  refine ⟨s,K,E,E.smaller_core_not_central,?_⟩
  by_cases hf : generalizedFitting K = pCore 2 K
  · exact Or.inr (E.c27_input hf)
  · exact Or.inl (E.quasisimple_of_nonconstrained hchoice hmany hn hna hf)

/-- The primes three and five exclude the entire constrained branch of the
actual pair, leaving an ordinary strict component with its noncentral core. -/
theorem ContainingPair.exists_quasisimple_enlargement_of_three_five
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂) (hne : K₁ ≠ K₂)
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (h5 : 5 ∣ Nat.card (L ⧸ pCore 2 L)) :
    ∃ (s : G) (K : Subgroup G), RankedEnlargement D H s K ∧ IsQuasisimple K ∧
      ¬ ((L.map (MulAut.conj s).toMonoidHom).subgroupOf K).pCoreIn 2 ≤ center K := by
  obtain ⟨s,K,E⟩ := C.exists_rankedEnlargement hn hne
  exact ⟨s,K,E,E.quasisimple_of_nonconstrained hchoice hmany hn hna
    (E.not_constrained_of_three_five h3 h5),E.smaller_core_not_central⟩

/-- The even-degree binary source row supplies the numerical exclusion on the
same original quotient, with no point-centralizer premise. -/
theorem ContainingPair.exists_quasisimple_enlargement_of_even_binary_quotient
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂) (hne : K₁ ≠ K₂)
    {n : ℕ} (hnn : 2 ≤ n) (he : Even n)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    ∃ (s : G) (K : Subgroup G), RankedEnlargement D H s K ∧ IsQuasisimple K ∧
      ¬ ((L.map (MulAut.conj s).toMonoidHom).subgroupOf K).pCoreIn 2 ≤ center K := by
  obtain ⟨s,K,E⟩ := C.exists_rankedEnlargement hn hne
  exact ⟨s,K,E,E.quasisimple_of_nonconstrained hchoice hmany hn hna
    (E.not_constrained_of_even_binary_quotient hnn he hm),E.smaller_core_not_central⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
