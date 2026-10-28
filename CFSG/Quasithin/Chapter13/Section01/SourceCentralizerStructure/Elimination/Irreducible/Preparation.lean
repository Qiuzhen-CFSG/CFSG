module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Reduction
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.LinearThreeMarking
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# The irreducibly normalized component in original 13.1.12

The actual normalizer action puts X = Ξₚ(L) in K. Distinct C-components
commute modulo the ambient two-core, so the escaping component is the unique
component containing X. Consequently C_M(u), its Sylow two-subgroup, and the
pushing-up core all normalize K. This obtains K₀ = K without identifying
K with either its two-core quotient or its central quotient.

Triviality of the centralizer's odd core gives the ordinary/characteristic-two
dichotomy. In the latter case these same subgroups satisfy the literal C.2.7
input; the existing source theorem constructs its star model and central
comparison kernel. The subsequent model sieve and both branch exclusions
remain separate mathematical obligations.

Source: Aschbacher–Smith, 13.1.12(3), printed pp.874–875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding Chapter12.Section02 SourceNonquasisimple
open Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The canonical radical prime is greater than three, from the actual A.3.6 structure. -/
theorem Context.prime_gt_three (h : Context T L p) : 3 < p := by
  exact (XiP_oddQuotient_of_A36
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    h.maximal.1.1 (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2)
    h.nonquasisimple h.odd h.divides).1

/-- The canonical radical is contained in the literal local point stabilizer. -/
theorem Context.radical_le_local (h : Context T L p) {u : G} (s : Selected T L u) :
    XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G) :=
  XiP_le_moved_centralizer h.hypothesis h.many h.maximal.1 h.nonquasisimple p s.mem

/-- Irreducibility of the relative component normalizer forces X into K. -/
theorem Context.radical_le_component (h : Context T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) : XiP p L ≤ K := by
  exact SourceCentralizerComponents.source_XiP_le_component_of_normalizer_irreducible
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides u
    (h.involution s.mem s.ne_one) (h.radical_le_local s) K e.component e.quotient
    e.normalized e.moved hi

omit [Finite G] [Fact p.Prime] in
/-- The full local point stabilizer retains the same irreducible Frattini action. -/
theorem ComponentNormalizerIrreducible.local {u : G} {K : Subgroup G}
    (hi : ComponentNormalizerIrreducible L K p u) : RadicalCentralizerIrreducible L p u := by
  intro A hA
  apply hi A
  intro g a ha
  exact hA ⟨g,g.property.1⟩ a ha

omit [Fact p.Prime] in
/-- The actual component Sylow has its literal ambient intersection and normalizes X. -/
theorem Context.component_sylow (h : Context T L p) {u : G}
    {K : Subgroup G} (e : Escape T L p u K) :
    ∃ S : Sylow 2 K,
      (S : Subgroup K).map K.subtype = ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ⊓ K ∧
      (S : Subgroup K).map K.subtype ≤ normalizer (XiP p L : Set G) := by
  obtain ⟨S,hS,_⟩ := SourceCentralizerComponents.component_sylow_normalizes_radical
    (centralizer ({u} : Set G)) (XiP p L) K
    ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) e.component e.full_sylow
    (XiP_invariant p (inf_le_left.trans h.sylow_normalizes))
  exact ⟨S,hS,hS ▸ inf_le_left.trans (XiP_invariant p (inf_le_left.trans h.sylow_normalizes))⟩

/-- No distinct component can contain the escaping canonical radical. -/
theorem Context.component_unique (h : Context T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    {D : Subgroup (centralizer ({u} : Set G))} (hD : D.IsCComponent)
    (hXD : (XiP p L).subgroupOf (centralizer ({u} : Set G)) ≤ D) :
    D = K.subgroupOf (centralizer ({u} : Set G)) := by
  let H := centralizer ({u} : Set G)
  let X := XiP p L
  let B := K.subgroupOf H
  have hXH : X ≤ H := (h.radical_le_local s).trans inf_le_right
  have hsq := h.hypothesis.simpleQTKE.involution_centralizer_sqtk (h.involution s.mem s.ne_one)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) :=
    ⟨Chapter1.XiEmbedding.quotient_stronglyQuasithin hsq.stronglyQuasithin,
      hsq.isKGroup.quotient _⟩
  by_contra hne
  have hc := (ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
    hQ e.component.2 hD (Ne.symm hne)).1.trans inf_le_left
  have hcc : ⁅B,X.subgroupOf H⁆ ≤ pCore 2 H :=
    (commutator_mono le_rfl hXD).trans
      (hc.trans (pCoreIn_le_of_subnormal 2 e.component.2.subnormal))
  apply e.moved_mod_core
  change ⁅K,X⁆ ≤ (pCore 2 H).map H.subtype
  have hm := map_mono (f := H.subtype) hcc
  simpa only [B,map_commutator,map_subgroupOf_eq_of_le (show K ≤ H from e.component.1),
    map_subgroupOf_eq_of_le hXH] using hm

/-- Uniqueness supplies normality in C_M(u), without ambient normality in C_G(u). -/
theorem Context.local_normalizes_component (h : Context T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) :
    normalizer (L : Set G) ⊓ centralizer ({u} : Set G) ≤ normalizer (K : Set G) := by
  let H := centralizer ({u} : Set G)
  let M := normalizer (L : Set G) ⊓ H
  have hn : M.subgroupOf H ≤ normalizer ((XiP p L).subgroupOf H : Set H) :=
    (comap_mono (XiP_invariant p (show M ≤ normalizer (L : Set G) from inf_le_left))).trans
      ((XiP p L).le_normalizer_comap H.subtype)
  have hNK : M.subgroupOf H ≤ normalizer (K.subgroupOf H : Set H) :=
    cComponent_le_normalizer_of_unique e.component.2
      (subgroupOf_mono H (h.radical_le_component s e hi))
      (fun D hD hXD => h.component_unique s e hD hXD) hn
  have hm := (map_mono (f := H.subtype) hNK).trans
    ((K.subgroupOf H).le_normalizer_map H.subtype)
  simpa only [map_subgroupOf_eq_of_le (show M ≤ H from inf_le_right),
    map_subgroupOf_eq_of_le (show K ≤ H from e.component.1)] using hm

/-- The source orbit K₀ has only one component in the irreducible branch. -/
theorem Context.component_orbit_eq (h : Context T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) :
    componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) = K := by
  apply le_antisymm _ (le_componentOrbit _ _)
  exact iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
    ((inf_le_inf_right _ h.sylow_normalizes).trans (h.local_normalizes_component s e hi))

omit [Fact p.Prime] in
/-- The odd core of the actual component vanishes by subnormal restriction. -/
theorem Escape.component_odd_core {u : G} {K : Subgroup G} (e : Escape T L p u K) :
    pPrimeCore 2 K = ⊥ := by
  have ho := e.component.2.subnormal.pPrimeCore_eq_bot e.odd_core
  have hm := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe e.component.1)
  simpa only [ho,Subgroup.map_bot] using hm.symm

omit [Fact p.Prime] in
/-- The source ordinary/characteristic-two split preserves the whole carrier K. -/
theorem Escape.ordinary_or_characteristic_two {u : G} {K : Subgroup G}
    (e : Escape T L p u K) : IsQuasisimple K ∨ generalizedFitting K = pCore 2 K := by
  rcases e.component.2.component_or_generalizedFitting_eq_pCore e.odd_core with hc | hf
  · exact Or.inl (hc.2.of_mulEquiv (subgroupOfEquivOfLe e.component.1))
  · right
    have hm := congrArg (map (subgroupOfEquivOfLe e.component.1).toMonoidHom) hf
    simpa only [map_generalizedFitting_equiv,pCore_map_iso] using hm

omit [Fact p.Prime] in
/-- In the ordinary branch the actual center is the actual two-core. -/
theorem Escape.ordinary_center {u : G} {K : Subgroup G} (e : Escape T L p u K)
    (hq : IsQuasisimple K) : center K = pCore 2 K := by
  let := hq
  exact IsQuasisimple.center_eq_pCore e.component_odd_core

/-- The characteristic-two branch satisfies C.2.7 on the literal source subgroups. -/
theorem Context.characteristic_two_input (h : Context T L p) (c : Control T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K) :
    ModelReduction.FullSieve.SourceInterface.Input KnownSimple.IsKnownSimple
      (centralizer ({u} : Set G)) (centralizerCore T L p u)
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) K := by
  have hs := c.pushing_up u s hnt
  have hRM : centralizerCore T L p u ≤
      normalizer (L : Set G) ⊓ centralizer ({u} : Set G) :=
    (isSylowIn_iff.mp hs.sylow).2.1.trans (map_subtype_le _)
  refine ⟨hs,e.component,e.quotient,hf,?_,hRM.trans (h.local_normalizes_component s e hi)⟩
  intro hk
  apply e.escapes
  rw [(RadicalConjugateRigidity.maximal_radical_structure h.hypothesis.simpleQTKE
    T h.maximal.1 h.nonquasisimple h.odd h.divides).2.1]
  exact hk.trans inf_le_left

/-- Actual application of C.2.7: the star component has a genuine group model. -/
theorem Context.characteristic_two_star_model (h : Context T L p) (c : Control T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K) :
    ChapterC.C27Source.StarModels.Model
      (ModelReduction.starImage K (centralizerCore T L p u) K) :=
  ChapterC.C27Source.star_model_from_source (h.characteristic_two_input c s hnt e hi hf)

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
