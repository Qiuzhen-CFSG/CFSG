module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SaturatedProjection
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ResidualPair

/-!
# Actual Hall-counterexample data for the remaining ordinary inspection

The original fixed residual has its literal A5 times A5 quotient with
two-core kernel. Under inner action on an escaping component, the same
residual has a perfect coordinate projection whose two-core is noncentral
and lies in the actual normalizer overlap. This theorem joins the independent
quotient and projection constructions without replacing their carriers.

Source: Aschbacher--Smith4.4.10--12, printed pp.621--622, as used in10.2.3.
This records the proved marked input to the remaining component inspection;
it does not assert component normality or placement of the whole residual.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual marked quotient and saturated projection are simultaneously
available on the same original residual and component. -/
theorem source_a5_oddNormalizer_marked_projection_data
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    let F := (solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype
    let Y := D.maximalLocal.subgroupOf (normalizer (B : Set G))
    (∃ f : F →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      Function.Surjective f ∧ f.ker = pCore 2 F) ∧
    ∃ P Q : Subgroup (normalizer (B : Set G)), P ≤ K ∧
      Q ≤ centralizer (K : Set (normalizer (B : Set G))) ∧
      Group.IsPerfect P ∧ Group.IsPerfect Q ∧
      F.subgroupOf (normalizer (B : Set G)) ≤ P ⊔ Q ∧
      P ≤ F.subgroupOf (normalizer (B : Set G)) ⊔ Q ∧
      ⁅P.pCoreIn 2,P⁆ ≠ ⊥ ∧ P.pCoreIn 2 ≤ Y.pCoreIn 2 ∧
      Y ⊓ normalizer (K : Set (normalizer (B : Set G))) ≤
        normalizer (P : Set (normalizer (B : Set G))) := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  exact ⟨source_a5_oddActorResidual_product_quotient D e hn B hBC hodd,
    source_a5_oddNormalizer_component_projection_saturated D e hn hp B hB hBC hBV hperm K hK houtK hinner⟩
end CFSG.Quasithin.Chapter10
