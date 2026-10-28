module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.FiniteInner
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SymplecticSix.BinarySylowFrattini

/-!
# Inner action on the normal binary symplectic six-space component

The actual projective model supplies the seven-generator Sylow Frattini
bound, proved from an order-eight matrix and the group order. The original
pair's Sylow restriction theorem therefore places the literal residual in
K times its centralizer before assuming that the residual lies in K.
Together with FiniteInner this supplies the three remaining finite model
inputs J₃, McL and Sp₆(2), preserving the central quotient conventions.

Source: Aschbacher--Smith 4.4.10, printed p.621.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The original residual acts innerly when the normal quasisimple
component has the actual binary projective symplectic six-space quotient. -/
theorem source_a5_oddNormalizer_inner_of_binary_symplectic_six
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) [K.Normal] [IsQuasisimple K]
    (hmodel : ClassicalGroup.IsPSp (K ⧸ center K) 3 2) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  obtain ⟨F, hF, hfin, hcard, ⟨a⟩⟩ := hmodel
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  exact source_a5_oddNormalizer_inner_of_smallFrattini D e hn hp B hB hBC hperm K P
    (Theory.SpecificGroups.SymplecticSix.BinarySylowFrattini.frattini_card_le_of_equiv
      hcard a P)

end CFSG.Quasithin.Chapter10
