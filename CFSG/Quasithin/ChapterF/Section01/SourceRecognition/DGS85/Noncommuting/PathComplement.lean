module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PathSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathComplement

/-!
# Odd complements inside the constructed singular path stabilizer

The first-singular-length construction proves regularity at all shorter
lengths. The Chapter 3 prefix induction therefore supplies the exact rooted
path transitivity needed by the independently proved Chapter 6 path-supplement
theorem. Schur--Zassenhaus chooses an odd complement to the full last edge
two-core inside the pointwise path stabilizer.

The reduced F1.11 application constructs the singular path from corrected
recognition of the two critical center sections. It discharges transitivity
rather than requiring a path-transitivity hypothesis. The local branching
condition is still an earlier-source premise; the last odd quotient exclusion
and final index comparison of (7.5) remain separate obligations.

Source: DGS, *Groups and Graphs* (1985), (6.7), p.123, and (7.5)(4)--(5), p.130.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk Theory.GroupAction.CubicTree
open SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Short-path regularity supplies the transitivity premise of source (6.7),
so the literal edge complement can be chosen inside the same path fixer. -/
theorem graph_path_complement_of_short_regular (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    {s n : ℕ} (hs : n + 1 ≤ s)
    (hshort : ∀ k x (q : BasedWalk (graph (family P)) k x),
      k < s → q.Nonbacktracking → Regular (A := G) q)
    {v a b : Vertex (family P)} (p : BasedWalk (graph (family P)) (n+1) v)
    (hp : p.Nonbacktracking) (hab : (graph (family P)).Adj a b)
    (ha : a ∈ p.vertices) (hb : b ∈ p.vertices) :
    ∃ K : Subgroup G, K ≤ pathStabilizer (family P) p ∧
      Disjoint K ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ∧
      K ⊔ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
        stabilizer (family P) a ⊓ stabilizer (family P) b ∧
      Nat.Coprime 2 (Nat.card K) := by
  let := finite_endpoints h
  let : Finite (stabilizer (family P) a ⊓ stabilizer (family P) b : Subgroup G) :=
    Finite.of_injective (inclusion (show stabilizer (family P) a ⊓ stabilizer (family P) b ≤
      stabilizer (family P) a from inf_le_left)) (inclusion_injective _)
  have hact : GraphAction (graph (family P)) G :=
    ⟨fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso (family P) g).toHom.map_adj he⟩
  have ht := rootPathTransitive_of_short_rightRegular hact s
    (fun k x q hk hq => (hshort k x q hk hq).2) v (n+1) hs
  have hgen := pathStabilizer_sup_core (family P) 2
    (fun i => ((family P (!i)).subgroupOf (family P i)).index) (fun _ => rfl)
    hbranch ht p hp hab ha hb (source_edge_core_sylow h hB hab)
  exact exists_complement_le_of_core_supplement 2 _ _ (pathStabilizer_le_edge (family P) p ha hb)
    (source_edge_core_sylow h hB hab) hgen

namespace Reduction
open DGS85.Reduction Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- Recognition and the critical center identities construct a first singular
path. The earlier (6.7) theorem then supplies an odd complement to the full
last edge core inside its pointwise stabilizer, with no transitivity premise
left for this application. Local branching remains an earlier-source input. -/
theorem reduced_epsilonTwo_singular_path_complement
    (h : HypothesisF11 L₀ S₀)
    (L : Vertex F → Subgroup (G₀ L₀ S₀))
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph F).Adj x y →
      LocalRankOneData (stabilizer F x)
        (stabilizer F x ⊓ stabilizer F y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer F x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x)
      (L x ⊓ centralizer (Z F x : Set (G₀ L₀ S₀))) ∨
      Z F x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph F).Adj x y → ¬ stabilizer F y ≤ normalizer
      ((Q F x ⊓ Q F y : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
    {v w u : Vertex F} (hc : IsCriticalPair F v w)
    (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hvu : (graph F).Adj v u)
    (hdu : (graph F).dist u w + 1 = b F)
    (hepsilon : Z F u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2))
    (E₀ E₁ : Subgroup (G₀ L₀ S₀))
    (c₀ : LocalRankOneData (stabilizer F v) E₀)
    (c₁ : LocalRankOneData (stabilizer F w) E₁)
    (h₀ : c₀.Pstar = L v) (h₁ : c₁.Pstar = L w)
    [((Q F v).subgroupOf c₀.Pstar).Normal]
    [((Q F w).subgroupOf c₁.Pstar).Normal]
    {W₀ W₁ : Type*}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (σ₀ : Representation (ZMod 2) (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar) W₀)
    (σ₁ : Representation (ZMod 2) (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar) W₁)
    (d₀ : BinaryConjugationSection c₀.Pstar (Z F v) (Stellmacher.omegaOneCenterAmbient c₀.Pstar)
      (σ₀.comp (QuotientGroup.mk' ((Q F v).subgroupOf c₀.Pstar))))
    (d₁ : BinaryConjugationSection c₁.Pstar (Z F w) (Stellmacher.omegaOneCenterAmbient c₁.Pstar)
      (σ₁.comp (QuotientGroup.mk' ((Q F w).subgroupOf c₁.Pstar))))
    (M₀ : BinaryRankOneModel (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar))
    (M₁ : BinaryRankOneModel (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar))
    (hf₀ : Function.Injective σ₀) (hf₁ : Function.Injective σ₁)
    (hr₀ : fixedSpace σ₀ (pResidual 2 (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar)) = ⊥)
    (hr₁ : fixedSpace σ₁ (pResidual 2 (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)) = ⊥)
    (hbranch : ∀ i, ∃ k, ((F (!i)).subgroupOf (F i)).index - 1 = 2^k) :
    EqualFieldNaturalSections σ₀ σ₁ ∧
      (b F = 2 ∨ ∃ (n : ℕ) (x : Vertex F) (p : BasedWalk (graph F) (n+1) x),
        n + 3 ≤ b F ∧ p.Nonbacktracking ∧ ¬ RightRegular (A := G₀ L₀ S₀) p ∧
        (∀ k y (q : BasedWalk (graph F) k y), k < n+1 → q.Nonbacktracking →
          Regular (A := G₀ L₀ S₀) q) ∧
        ∃ K : Subgroup (G₀ L₀ S₀), K ≤ pathStabilizer F p ∧
          Disjoint K ((stabilizer F p.penultimate ⊓ stabilizer F p.endpoint).pCoreIn 2) ∧
          K ⊔ (stabilizer F p.penultimate ⊓ stabilizer F p.endpoint).pCoreIn 2 =
            stabilizer F p.penultimate ⊓ stabilizer F p.endpoint ∧
          Nat.Coprime 2 (Nat.card K)) := by
  obtain ⟨hr,hp⟩ := reduced_epsilonTwo_path_regularity h L hcov d hstar hodd hdich hob
    hc hne hvu hdu hepsilon E₀ E₁ c₀ c₁ h₀ h₁ σ₀ σ₁ d₀ d₁ M₀ M₁ hf₀ hf₁ hr₀ hr₁
  refine ⟨hr,?_⟩
  rcases hp with hb | ⟨s,hs,hsb,hshort,hbad,_⟩
  · exact Or.inl hb
  right
  cases s with
  | zero => omega
  | succ n =>
    obtain ⟨x,p,hp,hbad⟩ := hbad
    have hpm : p.penultimate ∈ p.vertices := by
      have hh := (p.take n (Nat.le_succ _)).toWalk.end_mem_support
      rw [BasedWalk.support_toWalk,BasedWalk.endpoint_take_penultimate,
        BasedWalk.vertices_take] at hh
      exact List.mem_of_mem_take hh
    have hem : p.endpoint ∈ p.vertices := by
      simpa only [BasedWalk.support_toWalk] using p.toWalk.end_mem_support
    have hc := graph_path_complement_of_short_regular (reduced_triple h)
      (reduced_borel_core_sylow h) hbranch le_rfl hshort p hp p.adj_penultimate_endpoint hpm hem
    exact ⟨n,x,p,by omega,hp,hbad,hshort,hc⟩

end Reduction

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
