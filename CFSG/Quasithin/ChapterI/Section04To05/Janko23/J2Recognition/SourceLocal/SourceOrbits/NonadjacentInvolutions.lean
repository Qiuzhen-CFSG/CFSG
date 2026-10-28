module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.NonadjacentInvolutions.CentralizerCalculation

/-!
# The two nonneighbor involution branches

The actual 47.5 representatives supply the A₅ edge fixer at the prescribed
neighbor and both nonneighbor pair stabilizers. The centralizer calculation
identifies C_L(U) as Sylow two or D₁₀, respectively. The literal action on
L/(FX) then supplies an involution in C_L(U) fixing FX. Its order and the
central order-three factor X place it in F, giving a conjugate of z that
centralizes all three literal vertex subgroups.

`commonInvolution_of_representatives` assembles both branches without a
centralizer-type or fixed-point premise. The remaining inputs are exactly
the permitted earlier source data: the orders from 47.1 and 47.3, the two
five-normalizer alternatives from 47.2, the quasisimple centralizer and
central quotient from 47.3, and the representatives and involution class
from 47.5. The earlier-source producers and the representative construction
retain their discharge; the surrounding 47.6 assembly retains the base and
adjacent cases. Source: Aschbacher, *Sporadic Groups* (1994), final paragraph
of the proof of 47.6(4), printed p.264.
-/

public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.NonadjacentInvolutions
variable {G : Type*} [Group G] [Finite G]

/-- Apply the coset construction to the literal source representatives with
explicit centralizer types. The assembly below constructs this premise. -/
theorem commonInvolution_of_representatives_and_centralizerTypes (D : Seed G)
    [Theory.GroupTheory.IsQuasisimple (localCentralizer D)]
    (R : ThreePairRepresentatives D)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (Y : D.Vertex) (hY : D.graph.Adj D.base Y)
    (hclass : ∀ t ∈ edgeFixer G D.base Y, orderOf t = 2 → IsConj D.z t)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6))
    (types : CentralizerTypes D) (U : D.Vertex)
    (hU : sl2Join D D.base U ∨ a5Join D D.base U) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t :=
  commonInvolution_of_centralizerTypes D Y (R.edgeFixer_equiv hG hM hY)
    hclass hZ e types U hU

/-- Both nonneighbor branches of source 47.6(4), from the genuine earlier
source conclusions and 47.5 representatives. The centralizer types are proved,
and the witness centralizes the actual join of all three vertex subgroups. -/
theorem commonInvolution_of_representatives (D : Seed G)
    [Theory.GroupTheory.IsQuasisimple (localCentralizer D)]
    (R : ThreePairRepresentatives D)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (Y : D.Vertex) (hY : D.graph.Adj D.base Y)
    (hclass : ∀ t ∈ edgeFixer G D.base Y, orderOf t = 2 → IsConj D.z t)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G) (U : D.Vertex)
    (hU : sl2Join D D.base U ∨ a5Join D D.base U) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t :=
  commonInvolution_of_representatives_and_centralizerTypes D R hG hM Y hY hclass hZ e
    (centralizerTypes_of_representatives D R hG hM hZ e h₅) U hU

/-- The A₅ nonneighbor branch, paired with the exported
`commonInvolution_of_sl2Join` for the SL₂(3) branch. -/
theorem commonInvolution_of_a5Join (D : Seed G)
    [Theory.GroupTheory.IsQuasisimple (localCentralizer D)]
    (R : ThreePairRepresentatives D)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (Y : D.Vertex) (hY : D.graph.Adj D.base Y)
    (hclass : ∀ t ∈ edgeFixer G D.base Y, orderOf t = 2 → IsConj D.z t)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G) (U : D.Vertex)
    (hU : a5Join D D.base U) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t :=
  commonInvolution_of_representatives D R hG hM Y hY hclass hZ e h₅ U (Or.inr hU)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.NonadjacentInvolutions
