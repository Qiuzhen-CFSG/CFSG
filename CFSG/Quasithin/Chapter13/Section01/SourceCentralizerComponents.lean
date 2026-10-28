module

public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.Basic
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerSylow

/-!
# Original 13.1.12: the Fitting preimage and an escaping component

The actual radical Xi_p(L) and full actor C_M(u) act on their original
Frattini quotient. Original13.1.11 supplies the centralizer Sylow upgrade.
The source supercritical argument then proves O_{2,F}(C_G(u))≤C_M(u).
If C_G(u) escapes M, it contains a C-component with quasisimple own
O₂-quotient that the original radical moves modulo O₂(C_G(u)).

The earlier13.1.12(1--2) orbit/index/irreducibility data remain explicit,
as in SourceCentralizerSylow. No Fitting-control, component-existence,
A.1.21 or A.1.32 premise remains. The later component catalogue, its
exclusion, full C_G(u)≤M and Theorem13.1.7 remain separate obligations.

Source: Aschbacher--Smith,13.1.12(3), printed pp.873--874, with13.1.11.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- The original centralizer alternative after the Sylow upgrade. Every
Fitting and component-detection premise is derived from the earlier
13.1.12(1--2) action and index data on the actual Xi radical. -/
theorem source_centralizer_fitting_and_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G) (hu : orderOf u = 2) (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)))
    (hindex : ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2)
    (hcentral : ∀ g : G,
      (T : Subgroup G) ≤ centralizer ({g * u * g⁻¹} : Set G) →
        centralizer ({g * u * g⁻¹} : Set G) ≤ normalizer (L : Set G))
    (hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
        ∀ a ∈ A, xiFrattiniAction
          (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
          (XiP_invariant p inf_le_left) s a ∈ A) → A = ⊥ ∨ A = ⊤) :
    (twoFittingCore (centralizer ({u} : Set G))).map
        (centralizer ({u} : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer ({u} : Set G) ∧
      (centralizer ({u} : Set G) ≤ normalizer (L : Set G) ∨
        ∃ K : Subgroup G, K ∈ cComponentsIn (centralizer ({u} : Set G)) ∧
          IsQuasisimple (XiQuotient K) ∧
            ¬ ⁅K,XiP p L⁆ ≤ (centralizer ({u} : Set G)).pCoreIn 2) := by
  let H := centralizer ({u} : Set G)
  let M := normalizer (L : Set G) ⊓ H
  let S := (T : Subgroup G) ⊓ H
  obtain ⟨hq,hNX,_⟩ := RadicalConjugateRigidity.maximal_radical_structure hG T hL hn ho hd
  have hS := SourceCentralizerSylow.source_centralizer_sylow hG T hL hn ho hd u
    hTM hlocal hindex hcentral hXMu hirr
  obtain ⟨hfit,hcomp⟩ := fitting_and_component_in ho H (XiP p L) M S
      (hG.involution_centralizer_sqtk hu).stronglyQuasithin hXMu inf_le_right
      (XiP_invariant p inf_le_left) (XiP_isPPerfect p L) hq hS
      (XiP_invariant p (inf_le_left.trans hTM)) hirr
  refine ⟨le_inf (hfit.trans_eq hNX) (map_subtype_le _),?_⟩
  rcases hcomp with hc | hc
  · exact Or.inl (hc.trans_eq hNX)
  · exact Or.inr hc

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
