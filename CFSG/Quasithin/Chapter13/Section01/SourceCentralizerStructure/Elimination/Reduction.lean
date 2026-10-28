module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Preparation

/-!
# The remaining component branches of original 13.1.12(3)

The original XT-uniqueness and pushing-up setup are named source contracts.
From uniqueness, the preceding module derives central-involution control;
choose such an involution using Ω₁Z(T), and apply the proved Sylow upgrade
and centralizer structure theorem. A failure of containment then gives an
actual escaping C-component of C_G(u), with trivial odd core and its exact
Xi action. No whole-component identification is made from K/O₂(K).

The two remaining branches distinguish the action of C_M(u)∩N_G(K) on the
original odd Frattini quotient. Their exclusion implies centralizer
containment for every moved vector through the proved representative
transport, and feeds the actual TI theorem. These branch exclusions and
the Control contract remain explicit mathematical obligations; this module
does not claim the full source theorem without them. OrbitFacts is supplied
by the earlier original module classification.

Source: Aschbacher--Smith, 13.1.12(3)--13, printed pp.873--875.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter12.Section02 SourceNonquasisimple
open Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]

/-- The original uniqueness and local C.2.3 inputs, before component elimination. -/
structure Control (T : Sylow 2 G) (L : Subgroup G) (p : ℕ) : Prop where
  unique_overgroup : ∀ M : Subgroup G, IsMaximalTwoLocal M →
    XiP p L ⊔ (T : Subgroup G) ≤ M → M = normalizer (L : Set G)
  pushing_up : ∀ u : G, Selected T L u →
    ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
    PushingUpSetup KnownSimple.IsKnownSimple (centralizer ({u} : Set G))
      (centralizerCore T L p u) (normalizer (L : Set G) ⊓ centralizer ({u} : Set G))

/-- The literal escaping component produced by the existing centralizer theorem. -/
structure Escape (T : Sylow 2 G) (L : Subgroup G) (p : ℕ) (u : G) (K : Subgroup G) : Prop where
  full_sylow : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
    (centralizer ({u} : Set G))
  fitting_le : (twoFittingCore (centralizer ({u} : Set G))).map
    (centralizer ({u} : Set G)).subtype ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G)
  odd_core : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥
  component : K ∈ cComponentsIn (centralizer ({u} : Set G))
  quotient : IsQuasisimple (XiQuotient K)
  moved_mod_core : ¬ ⁅K,XiP p L⁆ ≤ (centralizer ({u} : Set G)).pCoreIn 2
  normalized : XiP p L ≤ normalizer (K : Set G)
  moved : ⁅K,XiP p L⁆ = K
  escapes : ¬ K ≤ normalizer (XiP p L : Set G)

/-- Irreducibility for precisely the relative component-normalizer actor in the source. -/
def ComponentNormalizerIrreducible (L K : Subgroup G) (p : ℕ) (u : G) : Prop :=
  ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
    (∀ s : ((normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) ⊓
      normalizer (K : Set G) : Subgroup G), ∀ a ∈ A,
      xiFrattiniAction
        ((normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) ⊓ normalizer (K : Set G))
        (XiP p L) (inf_le_left.trans (XiP_invariant p inf_le_left)) s a ∈ A) →
      A = ⊥ ∨ A = ⊤

variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Choose an actual central involution in the original nontrivial Sylow subgroup. -/
theorem Context.exists_central_involution (h : Context T L p) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
  have hUne := (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE
    h.maximal h.sylow_normalizes).2.1
  have hTne : (T : Subgroup G) ≠ ⊥ := fun he => hUne (bot_unique (h.moved_le_sylow.trans_eq he))
  let : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot (T : Subgroup G)).mpr hTne
  have hZne : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
    exact fun he => omega_center_ne_bot (G := T) T.isPGroup'
      ((((omega₁ (center T) (p := 2)).map (center T).subtype).map_eq_bot_iff_of_injective
        (T : Subgroup G).subtype_injective).mp he)
  obtain ⟨z,hz,hne⟩ := (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).bot_or_exists_ne_one.resolve_left hZne
  obtain ⟨hzT,hz2,hzC⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
  exact ⟨z,orderOf_eq_prime hz2 hne,hzT,fun t ht => mem_centralizer_singleton_iff.mpr (hzC t ht)⟩

/-- Failure of centralizer containment constructs all component, core and Sylow data. -/
theorem Context.escape_of_not_le (h : Context T L p) (o : OrbitFacts T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hout : ¬ centralizer ({u} : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup G, Escape T L p u K := by
  have hu := h.involution s.mem s.ne_one
  have hcentral : ∀ g : G, (T : Subgroup G) ≤ centralizer ({g * u * g⁻¹} : Set G) →
      centralizer ({g * u * g⁻¹} : Set G) ≤ normalizer (L : Set G) := by
    intro g hg
    apply h.central_involution_control_of_unique c.unique_overgroup _ _ hg
    simpa only [MulAut.conj_apply] using ((MulAut.conj g).orderOf_eq u).trans hu
  have hX := XiP_le_moved_centralizer h.hypothesis h.many h.maximal.1 h.nonquasisimple p s.mem
  have hi := h.selected_irreducible o s
  have hS := SourceCentralizerSylow.source_centralizer_sylow h.hypothesis.simpleQTKE T h.maximal.1
    h.nonquasisimple h.odd h.divides u h.sylow_normalizes s.local_sylow (o.index u s) hcentral hX hi
  obtain ⟨z,hz,hzT,hTz⟩ := h.exists_central_involution
  obtain ⟨hf,ho,hK⟩ := SourceCentralizerComponents.source_centralizer_structure
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides u hu
    h.sylow_normalizes s.local_sylow (o.index u s) hcentral hX hi z hz hzT
    (fun t ht => mem_centralizer_singleton_iff.mp (hTz ht))
    (h.central_involution_control_of_unique c.unique_overgroup z hz hTz)
  obtain ⟨K,hK,hq,hm,hn,hmove,he⟩ := hK.resolve_left hout
  exact ⟨K,⟨hS,hf,ho,hK,hq,hm,hn,hmove,he⟩⟩

/-- Assemble both component branches, then transport from selected representatives to every U#. -/
theorem Context.centralizer_le_of_component_exclusions (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p)
    (hirr : ∀ (u : G), Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u → False)
    (hred : ∀ (u : G), Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_selected _ hu hne
  intro v s
  by_contra hout
  have hnt : ¬ (T : Subgroup G) ≤ centralizer ({v} : Set G) :=
    fun ht => hout (h.central_involution_control_of_unique c.unique_overgroup v
      (h.involution s.mem s.ne_one) ht)
  obtain ⟨K,hK⟩ := h.escape_of_not_le o c s hout
  by_cases hi : ComponentNormalizerIrreducible L K p v
  · exact hirr v s hnt K hK hi
  · exact hred v s hnt K hK hi

/-- The literal TI consumer of the two remaining component exclusions. -/
theorem Context.ti_of_component_exclusions (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p)
    (hirr : ∀ (u : G), Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u → False)
    (hred : ∀ (u : G), Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply normalizerMoved_ti_of_centralizer_analysis h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides o.irreducible
  exact fun _ hu hne => h.centralizer_le_of_component_exclusions o c hirr hred hu hne

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
