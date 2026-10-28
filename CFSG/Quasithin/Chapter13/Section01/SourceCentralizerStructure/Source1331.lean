module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.Source1331.Source318

/-!
# The original 13.3.1 counterexample's centralizer structure

The earlier 3.1.8 source theorem selects the actual maximal faithful
nonquasisimple overgroup used in 13.3.2. Its uniqueness construction supplies
T-normalization. Apply the source 13.1.12 argument to that same overgroup:
every involution and odd radical satisfying the preceding orbit and action
data has the proved Fitting inclusion, trivial odd core, and moved-component
alternative. No new component-selection, solvability, or Fitting premise is
introduced. The earlier orbit/action data and later component-model sieve
remain with the full 13.1.7 assembly.

Source: Aschbacher–Smith, 13.3.2, printed p.884, using 13.1.7 and the proof
of 13.1.12(3), pp.868 and 873–874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceCentralizerComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The literal maximal counterexample in 13.3.2 satisfies the source
centralizer alternative, with T-normalization supplied by its construction. -/
theorem Hypothesis1331.nonquasisimple_centralizer_structure
    (h : Hypothesis1331 T L₀) (h318 : Chapter3.SourceTheorem318One G)
    (hn0 : ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ L ∈ LStar G T, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      L ∈ nonquasisimpleFaithful T ∧
      ∀ {p : ℕ} [Fact p.Prime]
        (_ho : Odd p) (_hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
        (u : G) (_hu : orderOf u = 2)
        (_hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
          (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)))
        (_hindex : ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2)
        (_hcentral : ∀ g : G,
          (T : Subgroup G) ≤ centralizer ({g * u * g⁻¹} : Set G) →
            centralizer ({g * u * g⁻¹} : Set G) ≤ normalizer (L : Set G))
        (_hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
        (_hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
          (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
            ∀ a ∈ A, xiFrattiniAction
              (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
              (XiP_invariant p inf_le_left) s a ∈ A) → A = ⊥ ∨ A = ⊤)
        (z : G) (_hz : orderOf z = 2) (_hzT : z ∈ (T : Subgroup G))
        (_hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
        (_hCz : centralizer ({z} : Set G) ≤ normalizer (L : Set G)),
        (twoFittingCore (centralizer ({u} : Set G))).map
            (centralizer ({u} : Set G)).subtype ≤
              normalizer (L : Set G) ⊓ centralizer ({u} : Set G) ∧
          pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥ ∧
          (centralizer ({u} : Set G) ≤ normalizer (L : Set G) ∨
            ∃ K : Subgroup G, K ∈ cComponentsIn (centralizer ({u} : Set G)) ∧
              IsQuasisimple (XiQuotient K) ∧
                ¬ ⁅K,XiP p L⁆ ≤ (centralizer ({u} : Set G)).pCoreIn 2 ∧
                  XiP p L ≤ normalizer (K : Set G) ∧ ⁅K,XiP p L⁆ = K ∧
                    ¬ K ≤ normalizer (XiP p L : Set G)) := by
  obtain ⟨L,hL,hL0,hf,hn,hmax,hjoin,huniq,_⟩ :=
    h.maximal_counterexample_of_source318 h318 hn0
  refine ⟨L,hL,hL0,hf,hn,?_⟩
  intro p hp ho hd u hu hlocal hindex hcentral hXMu hirr z hz hzT hzcentral hCz
  exact source_centralizer_structure h.qtke T hL hn.2 ho hd u hu
    (le_sup_right.trans hjoin) hlocal hindex hcentral hXMu hirr z hz hzT hzcentral hCz

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
