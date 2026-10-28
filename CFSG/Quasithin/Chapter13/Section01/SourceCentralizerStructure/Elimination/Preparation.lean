module
public import Theory.GroupTheory.LocalSylowCentralizerRepresentative
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.TI
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure

/-!
# Representatives and earlier-source control for original 13.1.12(3)

The literal moved subgroup is elementary abelian and lies in T. Select a
conjugate inside M=N_G(L) with C_T(u) Sylow in C_M(u), and transport centralizer
containment back through that same conjugator. This feeds the actual TI
consumer. The index and core-action assumptions are retained only for selected
representatives; they are the original module-orbit calculations, not a
centralizer-containment assumption.

The equality C_{O₂(XT)}(u)=C_{O₂(XT)}(U) makes this core XT-invariant.
Consequently uniqueness of the maximal two-local above XT controls its
characteristic normalizers. The same uniqueness and the proved radical
centralization on R₂(M) control every central Sylow involution, since
Ω₁Z(T) lies in R₂(M). Neither universal C.2.7 nor a centralizer bound is used
in these two deductions. The XT-uniqueness premise and component elimination
remain genuine source obligations.

Source: Aschbacher--Smith, 13.1.4(4--6), pp.867--868, and 13.1.12--13,
printed pp.872--875.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter12.Section02 SourceNonquasisimple
open Chapter3.RadicalCentralization
variable {G : Type*} [Group G] [Finite G]

/-- The original ambient and maximal nonquasisimple setup, with a chosen canonical prime. -/
structure Context (T : Sylow 2 G) (L : Subgroup G) (p : ℕ) : Prop where
  hypothesis : Hypothesis1311 T
  many : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  maximal : FaithfulMaximalLocal T L
  nonquasisimple : ¬ IsQuasisimple (XiQuotient L)
  odd : Odd p
  divides : p ∣ Nat.card (fittingSubgroup (XiQuotient L))

/-- Exactly the permitted local Sylow-centralizer choice in 13.1.12. -/
structure Selected (T : Sylow 2 G) (L : Subgroup G) (u : G) : Prop where
  mem : u ∈ normalizerMoved L
  ne_one : u ≠ 1
  local_sylow : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
    (normalizer (L : Set G) ⊓ centralizer ({u} : Set G))

/-- The literal R=C_{O₂(XT)}(u) used by the pushing-up argument. -/
def centralizerCore (T : Sylow 2 G) (L : Subgroup G) (p : ℕ) (u : G) : Subgroup G :=
  (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer ({u} : Set G)

/-- Earlier module-orbit consequences; none asserts ambient centralizer containment. -/
structure OrbitFacts (T : Sylow 2 G) (L : Subgroup G) (p : ℕ) : Prop where
  irreducible : ∀ u ∈ normalizerMoved L, u ≠ 1 →
    ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) → RadicalCentralizerIrreducible L p u
  index : ∀ u : G, Selected T L u →
    ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2
  core_action : ∀ u : G, Selected T L u →
    ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
    centralizerCore T L p u ≤ centralizer (normalizerMoved L : Set G)

variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ}

/-- Source normality makes the fixed Sylow normalize L. -/
theorem Context.sylow_normalizes (h : Context T L p) :
    (T : Subgroup G) ≤ normalizer (L : Set G) :=
  radicalLocal_invariant_source h.maximal.1.1
    (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2) h.nonquasisimple

/-- The moved module lies in the actual fixed Sylow subgroup. -/
theorem Context.moved_le_sylow (h : Context T L p) : normalizerMoved L ≤ (T : Subgroup G) := by
  have hU := (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal
    h.sylow_normalizes).2.2.1
  have hcore := pCoreIn_le_sylow (normalizer (L : Set G)) (T.subtype h.sylow_normalizes)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_normalizes] at hcore
  exact hU.trans hcore

/-- The moved module has the same full normalizer as L. -/
theorem Context.moved_normalizer (h : Context T L p) :
    normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) :=
  (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal h.sylow_normalizes).2.2.2

/-- Every nonidentity moved vector is an involution in G. -/
theorem Context.involution (h : Context T L p) {u : G}
    (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) : orderOf u = 2 := by
  let he := (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal
    h.sylow_normalizes).1
  have hpow : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu
  exact orderOf_eq_prime hpow hne

/-- Select a permitted representative while retaining moved-module membership. -/
theorem Context.exists_selected (h : Context T L p) {u : G}
    (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    ∃ g ∈ normalizer (L : Set G), Selected T L (g * u * g⁻¹) := by
  obtain ⟨g,hg,S,hS⟩ := T.exists_conjugate_local_centralizer_sylow
    (normalizer (L : Set G)) h.sylow_normalizes u (h.moved_le_sylow hu)
  refine ⟨g,hg,?_,?_,⟨S,hS⟩⟩
  · exact (mem_normalizer_iff.mp (h.moved_normalizer.symm ▸ hg) u).mp hu
  · intro he
    apply hne
    exact (MulAut.conj g).injective (he.trans (map_one (MulAut.conj g)).symm)

/-- Centralizer containment on the selected representatives implies containment on all U#. -/
theorem Context.centralizer_le_of_selected (h : Context T L p)
    (hc : ∀ v : G, Selected T L v → centralizer ({v} : Set G) ≤ normalizer (L : Set G))
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨g,hg,hs⟩ := h.exists_selected hu hne
  intro x hx
  have hconj : g * x * g⁻¹ ∈ centralizer ({g * u * g⁻¹} : Set G) :=
    mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul,MulAut.conj_apply] using congrArg (MulAut.conj g)
        (mem_centralizer_singleton_iff.mp hx))
  have hm := (normalizer (L : Set G)).mul_mem
    ((normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem hg)
      (hc _ hs hconj)) hg
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hm

/-- The actual 13.1.13 TI consumer of the representative reduction. -/
theorem Context.ti_of_selected [Fact p.Prime] (h : Context T L p) (o : OrbitFacts T L p)
    (hc : ∀ v : G, Selected T L v → centralizer ({v} : Set G) ≤ normalizer (L : Set G)) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply normalizerMoved_ti_of_centralizer_analysis h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides o.irreducible
  exact fun _ hu hne => h.centralizer_le_of_selected hc hu hne

/-- Include the Sylow-central branch using the original canonical radical action. -/
theorem Context.selected_irreducible [Fact p.Prime] (h : Context T L p) (o : OrbitFacts T L p)
    {u : G} (s : Selected T L u) : RadicalCentralizerIrreducible L p u := by
  by_cases hTu : (T : Subgroup G) ≤ centralizer ({u} : Set G)
  · exact radicalCentralizerIrreducible_of_sylow_centralizes h.hypothesis.simpleQTKE
      h.maximal.1.1 h.nonquasisimple h.odd h.divides hTu
  · exact o.irreducible u s.mem s.ne_one hTu

/-- The source core-action fact identifies the point centralizer with the module centralizer. -/
theorem Context.core_eq_fixed (_h : Context T L p) (o : OrbitFacts T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    centralizerCore T L p u =
      (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (normalizerMoved L : Set G) := by
  apply le_antisymm
  · exact le_inf inf_le_left (o.core_action u s hnt)
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr s.mem))

/-- The core is normalized by the original XT, using the actual module action. -/
theorem Context.core_normalized (h : Context T L p) (o : OrbitFacts T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    XiP p L ⊔ (T : Subgroup G) ≤ normalizer (centralizerCore T L p u : Set G) := by
  rw [h.core_eq_fixed o s hnt]
  apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
  · let J := XiP p L ⊔ (T : Subgroup G)
    simpa only [pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 J).le_normalizer_map J.subtype
  · apply le_trans _ (normalizer_le_normalizer_centralizer (normalizerMoved L))
    rw [h.moved_normalizer]
    exact sup_le ((XiP_le p L).trans L.le_normalizer) h.sylow_normalizes

/-- XT-uniqueness controls every characteristic-subgroup normalizer of the actual core. -/
theorem Context.core_characteristic_control (h : Context T L p) (o : OrbitFacts T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    (hunique : ∀ M : Subgroup G, IsMaximalTwoLocal M → XiP p L ⊔ (T : Subgroup G) ≤ M →
      M = normalizer (L : Set G)) :
    (centralizerCore T L p u).characteristicNormalizerClosure ≤ normalizer (L : Set G) := by
  apply characteristicNormalizerClosure_le_of_unique_maximalTwoLocal hunique
    ((isPGroup_pCoreIn 2 _).to_le inf_le_left)
  exact h.core_normalized o s hnt

/-- The central elementary subgroup of T lies in the literal reduced normalizer module. -/
theorem Context.sylowOmega_le_reduced [Fact p.Prime] (h : Context T L p) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ normalizerReduced L := by
  let M := normalizer (L : Set G)
  have hm := (RadicalConjugateRigidity.maximal_radical_structure h.hypothesis.simpleQTKE
    T h.maximal.1 h.nonquasisimple h.odd h.divides).2.2
  have hHe := lemma_1_1_4_6 T (h.hypothesis.simpleQTKE.evenCharacteristic T)
    (show M ∈ HOver G (T : Set G) from ⟨mem_H_of_isTwoLocal hm.1,h.sylow_normalizes⟩)
  have hi := sylow_omegaCenter_le_reduced (T.subtype h.sylow_normalizes) (mem_He_iff.mp hHe)
  change Stellmacher.omegaOneCenterAmbient
    ((T.subtype h.sylow_normalizes) : Subgroup M) ≤ reducedTwoSubgroup M at hi
  have hj := map_mono (f := M.subtype) hi
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective M.subtype M.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_normalizes] at hj
  rw [normalizerReduced_eq]
  exact hj

/-- Derive central-involution control from XT-uniqueness and proved radical centralization. -/
theorem Context.central_involution_control_of_unique [Fact p.Prime] (h : Context T L p)
    (hunique : ∀ M : Subgroup G, IsMaximalTwoLocal M → XiP p L ⊔ (T : Subgroup G) ≤ M →
      M = normalizer (L : Set G))
    (z : G) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  let Z := zpowers z
  have hpZ : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by
    simpa only [Z,Nat.card_zpowers,pow_one] using hz)
  have hnZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    have he : centralizer (Z : Set G) = centralizer ({z} : Set G) := by
      change centralizer (zpowers z : Set G) = centralizer ({z} : Set G)
      rw [zpowers_eq_closure,centralizer_closure]
    exact hTz.trans (he ▸ centralizer_le_normalizer (Z : Set G))
  have heT : (T : Subgroup G) ⊔ Z = (T : Subgroup G) :=
    T.is_maximal' (T.isPGroup'.to_sup_of_normal_right' hpZ hnZ) le_sup_left
  have hzT : z ∈ (T : Subgroup G) := heT ▸ mem_sup_right (mem_zpowers z)
  have hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hzT,hz ▸ pow_orderOf_eq_one z,fun t ht => mem_centralizer_singleton_iff.mp (hTz ht)⟩
  have hXz : XiP p L ≤ centralizer ({z} : Set G) := by
    apply ((XiP_le_solvableRadical L p).trans
      (solvableRadical_centralizes_normalizerReduced h.hypothesis h.many h.maximal.1
        h.nonquasisimple)).trans
    exact centralizer_le (Set.singleton_subset_iff.mpr (h.sylowOmega_le_reduced hzOmega))
  have hZne : Z ≠ ⊥ := zpowers_ne_bot.mpr (by intro he; simp [he] at hz)
  have hCZ : centralizer ({z} : Set G) ≤ normalizer (Z : Set G) := by
    rw [show centralizer ({z} : Set G) = centralizer (Z : Set G) from by
      change centralizer ({z} : Set G) = centralizer (zpowers z : Set G)
      rw [zpowers_eq_closure,centralizer_closure]]
    exact Subgroup.centralizer_le_normalizer _
  exact hCZ.trans (normalizer_le_of_unique_maximalTwoLocal hunique hpZ hZne
    ((sup_le hXz hTz).trans hCZ))

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
