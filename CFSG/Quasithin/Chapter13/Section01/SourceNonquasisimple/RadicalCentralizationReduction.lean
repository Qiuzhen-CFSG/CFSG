module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.SourceMany
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.PositiveStar.PositiveRadical
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedPositiveStar
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.LinearOrbit.Full
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.Embedding
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.ReducedModule
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ReducedDetection
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimaryExponent
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimaryAction
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ReducedAction
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.PrimeByTwo
public import Theory.GroupTheory.SolvableRadical.PrimaryDetection
public import Theory.GroupTheory.PResidual.NormalizedSupplement

/-!
# The actual radical-centralization obstruction in 13.1.4(5)

Suppose the canonical radical Ξ_p(L) has nonzero intrinsic module. The
proved guarded positive-star theorem supplies a quasisimple local overgroup.
A.4.10 transfers faithfulness to an actual maximal component K containing it.
If T normalized K, complete intrinsic embedding would leave an odd
linear-three quotient, excluded by the original whole-orbit cubic bound.
Thus K is a genuine nonnormal faithful quasisimple component. For the
literal U=[R₂(N_G(L)),L], the second theorem constructs its original
Chapter 10 Fundamental Setup, full module, and two-component orbit.

The odd-primary residuals detect the whole solvable radical on R₂(N_G(L)).
An exponent-p primary radical is Ξ_p(L) and follows the preceding reduction.
Otherwise A.1.30 gives p>5 and its actual higher homocyclic quotient.
The original reduced action, Frattini irreducibility, guarded 3.1.8 and
D.2.13 then construct a maximal two-local containing I_p T outside N_G(L).
The final theorem applies both reductions to failure of O∞(L) centralizing U.

No universal A.3.12, C.2.7 or additional embedding/ratio callback is assumed.
This is a source reduction, not a proof of radical centralization or13.1.7:
original Chapter 10 normalization and the surviving higher-primary escaping
configuration still require their source arguments.

Source: Aschbacher--Smith13.1.4(5), printed p.867;3.2.14, p.585;
1.3.4 and1.3.9, pp.509--514; original Chapter 10 setup, p.741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter1.XiEmbedding Chapter12.Section02
open Chapter1.RadicalExclusions.ModelReduction ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

omit [Finite G] in
private theorem moved_le_reduced (L : Subgroup G) :
    normalizerMoved L ≤ normalizerReduced L := by
  let M := normalizer (L : Set G)
  let : (reducedTwoSubgroup M).Normal := isPReduced_reducedPSubgroup.normal
  have hm := (reducedTwoSubgroup M).le_normalizer_map M.subtype
  rw [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hm
  have hLV : L ≤ normalizer (normalizerReduced L : Set G) := by
    rw [normalizerReduced_eq]
    exact L.le_normalizer.trans hm
  rw [normalizerMoved_eq,← normalizerReduced_eq]
  exact le_normalizer_iff_commutator_le_left.mp hLV

private theorem quasi_join_not_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (ho : Odd p)
    {X B : Subgroup G} (hB : B ∈ Chapter1.L G T)
    (hqB : IsQuasisimple (XiQuotient B))
    (hshape : XiOddQuotient p (XiQuotient X))
    (hXB : X ≤ B ⊔ (T : Subgroup G)) :
    ¬ (X.subgroupOf (B ⊔ (T : Subgroup G))).Normal := by
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  let C := radicalLocalImage (T : Subgroup G) B
  let e : XiQuotient B ≃* C := radicalLocalQuotientEquiv hB
  let : IsQuasisimple C := hqB.of_mulEquiv e
  have hc : A36Common C := (proposition_1_2_1_four_earlier_conclusion h36
    (uniqueness_local_quotient_sqtk hG hB.2.2) hB.1).2
  have hz := center_card_of_quasisimple_A36Common hc
  have hpf : ¬ p ∣ Nat.card (center (XiQuotient B)) := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    rcases hz with hz | hz
    · rw [hz]; exact (Fact.out : p.Prime).not_dvd_one
    · rw [hz]
      intro hd
      have := Nat.le_of_dvd (by decide : 0 < 3) hd
      omega
  have hcore := initial_quotient_pCore_eq_bot_of_center_primeFree ho hB hqB hpf
  have hcyc : IsCyclic (pCore p (XiQuotient (B ⊔ (T : Subgroup G)))) := by
    rw [hcore]
    infer_instance
  exact not_normal_of_cyclic_quotient_pCore hshape hXB hcyc

/-- Nonzero intrinsic action of the actual canonical radical forces an original
maximal faithful quasisimple component which the fixed Sylow group moves. -/
theorem canonical_radical_intrinsic_escape
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hne : intrinsicSignalizerModule (XiP p L) ≠ ⊥) :
    ∃ K : Subgroup G, FaithfulMaximalLocal T K ∧
      IsQuasisimple (XiQuotient K) ∧
      XiP p L ≤ componentOrbit K (T : Subgroup G) ∧
      ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
  let X := XiP p L
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hQ := uniqueness_local_quotient_sqtk h.simpleQTKE hL.2.2
  obtain ⟨hp3,hshape⟩ := XiP_oddQuotient_of_A36 h36 hL hQ hn ho hd
  have hplus := XiP_mem_XiPlus_source h.simpleQTKE T hL hn ho hd
  have hX : X ∈ Xi G (T : Subgroup G) := hplus.1
  have hHe : X ∈ He G := hX.mem_He
    (fun _ hM _ hN hNM hnorm => lemma_1_1_3_1 hM hN hNM hnorm)
    (lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T))
  have hfX : X ∈ XiF G (T : Subgroup G) :=
    ⟨hX,⟨⟨hX.ne_bot,hX.perfect,
      generalizedFitting_eq_pCore_of_selfCentralizing 2 (mem_He_iff.mp hHe)⟩,hne⟩⟩
  have hnotstar : X ∉ XiStar G (T : Subgroup G) := by
    intro hstar
    exact hne (GuardedPositiveStar.positive_star_intrinsicModule_eq_bot h.simpleQTKE
      (Chapter3.source_guardedTheorem318One h.simpleQTKE) T
      (Chapter3.hasMaximalOutside_of_many T hmany) ⟨hplus,hstar⟩)
  have hex : ∃ B ∈ Chapter1.L G (T : Subgroup G),
      IsQuasisimple (XiQuotient B) ∧ X ⊔ (T : Subgroup G) ≤ B ⊔ (T : Subgroup G) := by
    by_contra! ha
    exact hnotstar ⟨hX,ha⟩
  obtain ⟨B,hB,hqB,hXB⟩ := hex
  obtain ⟨K,hK,hBK⟩ := exists_mem_LStar_ge hB
  have hXKT : X ≤ K ⊔ (T : Subgroup G) :=
    le_sup_left.trans (hXB.trans (sup_le_sup_right hBK _))
  have hXorb : X ≤ componentOrbit K (T : Subgroup G) :=
    le_of_isPPerfect_of_le_sup_of_normalizes X (componentOrbit K T) T
      hX.perfect T.isPGroup' (le_normalizer_componentOrbit K T)
      (hXKT.trans (sup_le_sup_right (le_componentOrbit K T) _))
  have hf := (Chapter1.Terminal.lemma_1_3_9_two_of_A_4_10 T
    (lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T))
    ChapterA.Section04.SourceChains.terminal_source hfX hK.1 hXorb).2
  have hfK : FaithfulMaximalLocal T K :=
    ⟨hK,((mem_faithfulLocalComponents_iff T K).mp hf).2⟩
  have hmove : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
    intro hTK
    have hXK : X ≤ K := le_of_isPPerfect_of_le_sup_of_normalizes X K T
      hX.perfect T.isPGroup' hTK hXKT
    let P : Sylow p X := default
    have hinput := localInput_of_mem_Xi hX hK.1.2.1
      (sup_le_sup_right hXK _) ho hshape P
    have hnon := RadicalActions.XiP_automizer_not_isCyclic_of_A36 h36 hL hQ hn ho hd P
    rcases RadicalNormality.normal_or_linear_three hK.1 hTK hXK hinput
      (Chapter3.sqtk_of_mem_H h.simpleQTKE hK.1.2.2) hp3 hnon with hnorm | ⟨hq,hm,_⟩
    · have hKN : K ≤ normalizer (X : Set G) :=
        (normal_subgroupOf_iff_le_normalizer hXK).mp hnorm
      exact quasi_join_not_normal h.simpleQTKE hp3 ho hB hqB hshape
        (le_sup_left.trans hXB)
        (normal_subgroupOf_of_le_normalizer (sup_le (hBK.trans hKN) hX.invariant))
    · let h12 : Hypothesis1221 KnownSimple.IsKnownSimple T K :=
        ⟨h.simpleQTKE,hfK,hq⟩
      obtain ⟨V,⟨D⟩⟩ := h12.exists_chosen_of_normalizes hTK
      exact linear_three_whole_orbit_excluded D h12 Fact.out ho hp3 hm
        (D.orbit_cubicRatio_le_source h12 (Chapter3.hasMaximalOutside_of_many T hmany))
  have hqK : IsQuasisimple (XiQuotient K) := by
    by_contra hq
    exact hmove (radicalLocal_invariant_source hK.1
      (uniqueness_local_quotient_sqtk h.simpleQTKE hK.1.2.2) hq)
  exact ⟨K,hfK,hqK,hXorb,hmove⟩

/-- For the literal U=[R₂(N_G(L)),L], movement by the canonical radical
constructs the original nonnormal two-component setup of Chapter 10. -/
theorem canonical_radical_moved_action_pair
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (ha : ¬ XiP p L ≤ centralizer (normalizerMoved L : Set G)) :
    ∃ K : Subgroup G, Hypothesis1221 KnownSimple.IsKnownSimple T K ∧
      XiP p L ≤ componentOrbit K (T : Subgroup G) ∧
      ¬ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ∃ D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K,
        IsMaximalTwoLocal D.maximalLocal ∧
        normalizer (D.fullModule : Set G) = D.maximalLocal ∧
        IsElementaryAbelian 2 D.fullModule ∧
        K < Chapter3.Section02.localOrbit T K ∧
        (normalizer (K : Set G)).relIndex (T : Subgroup G) = 2 ∧
        ∃ t ∈ (T : Subgroup G), t ∉ normalizer (K : Set G) ∧
          Chapter3.Section02.localOrbit T K = K ⊔ K.map (MulAut.conj t).toMonoidHom ∧
          ⁅K,K.map (MulAut.conj t).toMonoidHom⁆ ≤
            (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let M := normalizer (L : Set G)
  let X := XiP p L
  have hXM : X ≤ M := (XiP_le p L).trans L.le_normalizer
  have hXn : (X.subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_le_normalizer_XiP p L)
  have hUV := moved_le_reduced L
  have hm : ⁅reducedTwoSubgroup M,X.subgroupOf M⁆ ≠ ⊥ := by
    intro hz
    have he := congrArg (Subgroup.map M.subtype) hz
    rw [map_commutator,map_subgroupOf_eq_of_le hXM,Subgroup.map_bot] at he
    change ⁅(reducedTwoSubgroup (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype,X⁆ = ⊥ at he
    rw [← normalizerReduced_eq] at he
    have hc : X ≤ centralizer (normalizerReduced L : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans he)
    exact ha (hc.trans (centralizer_le hUV))
  have hi := Chapter3.RadicalCentralization.intrinsicModule_ne_bot_of_reduced_action X M
    hXM hXn.isSubnormal (XiP_isPPerfect p L) hm
  obtain ⟨K,hfK,hqK,hXK,hmove⟩ := canonical_radical_intrinsic_escape h hmany hL.1.1 hn ho hd hi
  exact ⟨K,⟨h.simpleQTKE,hfK,hqK⟩,hXK,hmove,
    Chapter10.source_nonnormal_preparation h.simpleQTKE hfK.1 hfK.2 hqK hmove⟩

private theorem radical_centralizes_reduced_of_primary (L : Subgroup G)
    (hc : ∀ p : ℕ, p.Prime → Odd p →
      Chapter3.RadicalCentralization.primaryRadical p L ≤
        centralizer (normalizerReduced L : Set G)) :
    (solvableRadical L).map L.subtype ≤ centralizer (normalizerReduced L : Set G) := by
  let J := normalizer (L : Set G)
  let R := (solvableRadical L).map L.subtype
  have hRJ : R ≤ J := (map_subtype_le _).trans L.le_normalizer
  let N := R.subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_le_normalizer_characteristic_image L (solvableRadical L))
  have hNC : N ≤ centralizer (reducedTwoSubgroup J : Set J) := by
    apply normal_centralizes_reduced_of_primary_residuals N _ isPReduced_reducedPSubgroup
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    have he : ((primeToResidual p N).map N.subtype).map J.subtype =
        Chapter3.RadicalCentralization.primaryRadical p L := by
      rw [map_embedded_primeToResidual_of_hom,
        map_subgroupOf_eq_of_le hRJ,← map_embedded_primeToResidual_of_hom p (solvableRadical L) L.subtype]
      rfl
    intro x hx
    apply mem_centralizer_iff.mpr
    intro v hv
    have hh := mem_centralizer_iff.mp (hc p hp ho (he ▸ mem_map_of_mem J.subtype hx))
      (v : G) (by rw [normalizerReduced_eq]; exact mem_map_of_mem J.subtype hv)
    exact Subtype.ext hh
  intro r hr
  apply mem_centralizer_iff.mpr
  rw [normalizerReduced_eq]
  rintro v ⟨w,hw,rfl⟩
  exact congrArg Subtype.val
    (mem_centralizer_iff.mp (hNC (show (⟨r,hRJ hr⟩ : J) ∈ N from hr)) w hw)

/-- An active primary radical at p>5 has an actual maximal two-local overgroup
outside N_G(L). The source reduced module and its Sylow centralizer are built;
guarded 3.1.8 and D.2.13 rule out uniqueness over this same primary radical. -/
theorem active_large_primary_escaping_maximal
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp5 : 5 < p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hi : intrinsicSignalizerModule (Chapter3.RadicalCentralization.primaryRadical p L) ≠ ⊥) :
    ∃ H : Subgroup G, IsMaximalTwoLocal H ∧
      Chapter3.RadicalCentralization.primaryRadical p L ⊔ (T : Subgroup G) ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) := by
  let I := Chapter3.RadicalCentralization.primaryRadical p L
  let M := normalizer (L : Set G)
  have hM : IsMaximalTwoLocal M :=
    (RadicalConjugateRigidity.maximal_radical_structure h.simpleQTKE T hL hn ho hd).2.2
  have hTM : (T : Subgroup G) ≤ M := radicalLocal_invariant_source hL.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.2.2) hn
  have hIM : I ≤ M := (map_subtype_le _).trans L.le_normalizer
  have hMN : M ≤ normalizer (I : Set G) :=
    Chapter3.RadicalCentralization.normalizer_le_normalizer_primaryRadical L p
  have hTI := hTM.trans hMN
  have hpI := Chapter3.RadicalCentralization.primaryRadical_twoPerfect L ho
  have hquot := Chapter3.RadicalCentralization.primaryRadical_quotient_isPGroup
    h.simpleQTKE T hL.1 ho
  have hirr := Chapter3.RadicalCentralization.primaryRadical_irreducible
    h.simpleQTKE T hL.1 hn ho hd hTI
  have hne := Chapter3.RadicalCentralization.reduced_action_ne_bot_of_intrinsic_module
    (T : Subgroup G) I hTI hpI ho hquot hi
  have hc := Chapter3.RadicalCentralization.reduced_sylow_centralizer T I hTI hpI hirr hne
  by_contra! hno
  have hu (N : Subgroup G) (hN : IsMaximalTwoLocal N)
      (hIN : I ⊔ (T : Subgroup G) ≤ N) : N = M := by
    have hNM := hno N hN hIN
    exact le_antisymm hNM (hN.2 hM.1 hNM)
  have hAt := Chapter3.sourceTheorem318OneAt_of_guarded
    (Chapter3.source_guardedTheorem318One h.simpleQTKE) hM hTM
    (Chapter3.hasMaximalOutside_of_many T hmany M hM hTM)
  have hr := hAt.cubicRatio_le I hpI hIM (normal_subgroupOf_of_le_normalizer hMN)
    hM (sup_le hIM hTM) hu (reducedTwoSubgroup (I ⊔ (T : Subgroup G) : Subgroup G))
    isPReduced_reducedPSubgroup hc
  let J := I ⊔ (T : Subgroup G)
  let I₀ := I.subgroupOf J
  let T₀ := (T : Subgroup G).subgroupOf J
  let : I₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le I.le_normalizer hTI)
  have hgen : I₀ ⊔ T₀ = ⊤ := by
    rw [← subgroupOf_sup (show I ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self _
  let e : I₀ ≃* I := subgroupOfEquivOfLe (show I ≤ J from le_sup_left)
  let eq : (I₀ ⧸ pCore 2 I₀) ≃* (I ⧸ pCore 2 I) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hb := ChapterD.prime_restriction_of_reduced_extension I₀ T₀ hgen ho
    (hquot.of_equiv eq.symm) T.isPGroup'.comap_subtype (reducedTwoSubgroup J)
    isPReduced_reducedPSubgroup hr
  rcases hb with hb | hb <;> omega

/-- Failure of original radical centralization on U leaves exactly a nonnormal
faithful component or an active higher homocyclic primary radical at p>5. -/
theorem radical_moved_action_obstruction
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (ha : ¬ (solvableRadical L).map L.subtype ≤
      centralizer (normalizerMoved L : Set G)) :
    (∃ K : Subgroup G, Hypothesis1221 KnownSimple.IsKnownSimple T K ∧
      ¬ (T : Subgroup G) ≤ normalizer (K : Set G)) ∨
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 5 < p ∧
      p ∣ Nat.card (fittingSubgroup (XiQuotient L)) ∧
      intrinsicSignalizerModule (Chapter3.RadicalCentralization.primaryRadical p L) ≠ ⊥ ∧
      ∃ a : ℕ, 2 ≤ a ∧
        Nonempty ((Chapter3.RadicalCentralization.primaryRadical p L ⧸
          pCore 2 (Chapter3.RadicalCentralization.primaryRadical p L)) ≃*
          Multiplicative (Fin 2 → ZMod (p^a))) ∧
        ∃ H : Subgroup G, IsMaximalTwoLocal H ∧
          Chapter3.RadicalCentralization.primaryRadical p L ⊔ (T : Subgroup G) ≤ H ∧
          ¬ H ≤ normalizer (L : Set G) := by
  have hex : ∃ p : ℕ, p.Prime ∧ Odd p ∧
      ¬ Chapter3.RadicalCentralization.primaryRadical p L ≤
        centralizer (normalizerReduced L : Set G) := by
    by_contra! hc
    exact ha ((radical_centralizes_reduced_of_primary L hc).trans
      (centralizer_le (moved_le_reduced L)))
  obtain ⟨p,hp,ho,hact⟩ := hex
  let : Fact p.Prime := ⟨hp⟩
  have hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)) := by
    by_contra hd
    have he := Chapter3.RadicalCentralization.primaryRadical_eq_bot_of_not_dvd
      h.simpleQTKE T hL.1.1 ho hd
    exact hact (he ▸ bot_le)
  let I := Chapter3.RadicalCentralization.primaryRadical p L
  let M := normalizer (L : Set G)
  have hIM : I ≤ M := (map_subtype_le _).trans L.le_normalizer
  have hiN : (I.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    (Chapter3.RadicalCentralization.normalizer_le_normalizer_primaryRadical L p)
  have hm : ⁅reducedTwoSubgroup M,I.subgroupOf M⁆ ≠ ⊥ := by
    intro hz
    have he := congrArg (Subgroup.map M.subtype) hz
    rw [map_commutator,map_subgroupOf_eq_of_le hIM,Subgroup.map_bot] at he
    change ⁅(reducedTwoSubgroup (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype,I⁆ = ⊥ at he
    rw [← normalizerReduced_eq] at he
    exact hact (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans he))
  have hi := Chapter3.RadicalCentralization.intrinsicModule_ne_bot_of_reduced_action I M
    hIM hiN.isSubnormal (Chapter3.RadicalCentralization.primaryRadical_twoPerfect L ho) hm
  by_cases he : ∀ x : I ⧸ pCore 2 I, x ^ p = 1
  · have hle := Chapter3.RadicalCentralization.primaryRadical_le_XiP_of_exponent
      h.simpleQTKE T hL.1.1 ho he
    have hshape := (RadicalConjugateRigidity.maximal_radical_structure
      h.simpleQTKE T hL.1 hn ho hd).1
    have heq : I = XiP p L := le_antisymm hle
      (Chapter3.RadicalCentralization.XiP_le_primaryRadical L hshape)
    rw [heq] at hi
    obtain ⟨K,hf,hq,_,hm⟩ := canonical_radical_intrinsic_escape h hmany hL.1.1 hn ho hd hi
    exact Or.inl ⟨K,⟨h.simpleQTKE,hf,hq⟩,hm⟩
  · obtain ⟨hp5,a,ha,ea⟩ := Chapter3.RadicalCentralization.primaryRadical_higher_structure
      h.simpleQTKE T hL.1.1 hn ho he
    exact Or.inr ⟨p,hp,ho,hp5,hd,hi,a,ha,ea,
      active_large_primary_escaping_maximal h hmany hL.1 hn ho hp5 hd hi⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
