module

public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.Centralizer
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BorelNormalizer
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.CubicMovement
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SylowStabilizer

/-!
# The terminal common component from the original fundamental setup

Retain the original L and the opposite Borel A = S₂D₂. The original local
family restricts to N_T(L), so the Borel-normalizer Sylow theorem supplies
its exact local-family membership inside N_G(A). The known-simple quotient
condition follows from the proved SQTK condition there. The actual cubic
movement then constructs the common component and its centralization;
faithfulness of the opposite cubic bounds its three-rank by one.

No local-family membership, SQTK quotient, or containing component is added
to the original source assumptions. Source: Aschbacher--Smith 10.2.3(4),
printed p.747, using 1.2.4 and 9.3.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original component belongs to the literal local family of every
overgroup whose marked Sylow is the original stabilizer N_T(L). -/
theorem source_original_stabilizer_local_family
    (D₀ : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (N : Subgroup G) (hLN : L ≤ N)
    (P : Sylow 2 N)
    (hP : (P : Subgroup N).map N.subtype =
      (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    L.subgroupOf N ∈ Chapter1.L N P := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hRN : R ≤ N := by
    change (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ N
    rw [← hP]
    exact map_subtype_le (P : Subgroup N)
  have hR : R.subgroupOf N = (P : Subgroup N) := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hRN, hP]
  rw [← hR]
  exact (Chapter1.mem_LIn_iff_subgroupOf hRN hLN).mp
    ⟨hLN, mem_L_sylow_stabilizer D₀.maximal.1⟩

/-- Original-setup construction of the common component at the opposite Borel.
The local family and both SQTK hypotheses are discharged internally. -/
theorem source_original_borel_common_component
    (D₀ : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (S₂ D₂ K D₁ : Subgroup G)
    (hA : pCore 2 (S₂ ⊔ D₂ : Subgroup G) ≠ ⊥)
    (hLA : L ≤ centralizer ((S₂ ⊔ D₂ : Subgroup G) : Set G))
    (hR : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer ((S₂ ⊔ D₂ : Subgroup G) : Set G))
    (hK : K ≤ normalizer ((S₂ ⊔ D₂ : Subgroup G) : Set G))
    (hout : ¬ K ≤ D₀.maximalLocal) (hD₁ : D₁ ≤ L) (hmove : ⁅K, D₁⁆ = K)
    (hfaithful : D₂ ⊓ centralizer (S₂ : Set G) = ⊥) (hD₂ : Nat.card D₂ = 3) :
    ∃! C : Subgroup G,
      C ∈ Chapter1.cComponentsIn (normalizer ((S₂ ⊔ D₂ : Subgroup G) : Set G)) ∧
      L ≤ C ∧ K ≤ C ∧ C ≤ centralizer ((S₂ ⊔ D₂ : Subgroup G) : Set G) ∧
      primeRank 3 C ≤ 1 := by
  let A := S₂ ⊔ D₂
  let N := normalizer (A : Set G)
  have hLN : L ≤ N := hLA.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨⟨P, hP⟩, hN⟩ := source_natural_borel_normalizer_sylow D₀ e hn A K
    hA hLN hR hK hout
  have hlocal := source_original_stabilizer_local_family D₀ N hLN P hP
  have hQ : IsSQTK KnownSimple.IsKnownSimple (N ⧸ pCore 2 N) := by
    refine ⟨?_, hN.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hN.stronglyQuasithin p hp ho)
  obtain ⟨C, ⟨hC, hLC, hKC, hCA⟩, hu⟩ :=
    source_natural_pair_common_centralizing_component A L K D₁ hQ P hlocal hLA hK hD₁ hmove
  have hrank : primeRank 3 C ≤ 1 :=
    source_borel_component_cubic_rank_le_one S₂ D₂ L C hN hfaithful hD₂ hC hLC
      (Chapter1.mem_L_not_isSolvable D₀.maximal.1) hLA
  exact ⟨C, ⟨hC, hLC, hKC, hCA, hrank⟩,
    fun E hE => hu E ⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2.1⟩⟩

/-- The original natural-block consumer discharges cubic movement and proves
proper containment using the actual block escaping M. -/
theorem source_original_natural_borel_proper_common_component
    (D₀ : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (S₂ D₂ K D₁ : Subgroup G)
    (hA : pCore 2 (S₂ ⊔ D₂ : Subgroup G) ≠ ⊥)
    (hLA : L ≤ centralizer ((S₂ ⊔ D₂ : Subgroup G) : Set G))
    (hR : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer ((S₂ ⊔ D₂ : Subgroup G) : Set G))
    (hK : K ≤ normalizer ((S₂ ⊔ D₂ : Subgroup G) : Set G))
    (hout : ¬ K ≤ D₀.maximalLocal) (hKn : ChapterC.IsL2EvenBlock K 2)
    (hD₁L : D₁ ≤ L) (hD₁K : D₁ ≤ K) (hD₁ : Nat.card D₁ = 3)
    (hfaithful : D₂ ⊓ centralizer (S₂ : Set G) = ⊥) (hD₂ : Nat.card D₂ = 3) :
    ∃! C : Subgroup G,
      C ∈ Chapter1.cComponentsIn (normalizer ((S₂ ⊔ D₂ : Subgroup G) : Set G)) ∧
      L < C ∧ K ≤ C ∧ C ≤ centralizer ((S₂ ⊔ D₂ : Subgroup G) : Set G) ∧
      primeRank 3 C ≤ 1 := by
  obtain ⟨C, ⟨hC, hLC, hKC, hCA, hrank⟩, hu⟩ :=
    source_original_borel_common_component D₀ e hn S₂ D₂ K D₁ hA hLA hR hK hout hD₁L
      (source_natural_cubic_component_moved K D₁ hKn hD₁K hD₁) hfaithful hD₂
  have hLM : L ≤ D₀.maximalLocal :=
    (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hproper : L < C := lt_of_le_of_ne hLC (fun he => hout (hKC.trans (he ▸ hLM)))
  exact ⟨C, ⟨hC, hproper, hKC, hCA, hrank⟩,
    fun E hE => hu E ⟨hE.1, hE.2.1.le, hE.2.2.1, hE.2.2.2.1, hE.2.2.2.2⟩⟩

end CFSG.Quasithin.Chapter10
