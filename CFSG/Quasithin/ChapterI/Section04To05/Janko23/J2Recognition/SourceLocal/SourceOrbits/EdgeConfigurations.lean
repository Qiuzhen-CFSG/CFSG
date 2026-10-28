module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.ExternalOrbit
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.InternalTriangles
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.EdgeCentralizer

/-!
# Source edge configurations for J₂ recognition

The internal common neighbors form one orbit under the literal setwise
edge stabilizer. The transporter lies in the endpoint A₄. The earlier
five-normalizer alternatives construct the local A₅ used in that proof,
so no extra local-model hypothesis remains in this internal branch.

The exact double-coset intersections, their triple-centralizer embeddings,
and the involution extraction are organized in `EdgeConfigurations.Basic`.
The actual A₆ quotient calculations and the external incidence calculation
remain required before asserting 47.6(1), (2), or the complete two-orbit
statement. Final assembly remains with the edge-configuration task.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6, pp.263–264.
-/

public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
variable {G : Type*} [Group G] [Finite G]

/-- The genuine five-local normalizer alternatives and the preceding edge
fixer theorem suffice for internal triangle transitivity. -/
theorem internal_third_transitive_of_five_normalizers (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G) (U V : D.Vertex)
    (hUX : D.graph.Adj D.base U) (hUY : D.graph.Adj Y U)
    (hVX : D.graph.Adj D.base V) (hVY : D.graph.Adj Y V)
    (hU : U.val ≤ D.X ⊔ Y.val) (hV : V.val ≤ D.X ⊔ Y.val) :
    ∃ g : edgeStabilizer G D.base Y,
      (g : G) ∈ D.X ⊔ Y.val ∧ (g : G) • U = V := by
  let E := edgeFrameOfAlternatingFixer D Y hY hF.some
  obtain ⟨eK⟩ := PrimeNormalizers.edgeFrame_centralizer_equiv E hF h₅
  exact E.internal_third_transitive hF eK U V hUX hUY hVX hVY hU hV

/-- The distinguished vertex in 47.6(4) needs only the preceding fixer and
its source involution class. The witness is constructed inside that fixer. -/
theorem commonInvolution_at_base (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ D.X ≤ involutionCentralizer t :=
  commonInvolution_of_le_join D Y D.base hF hclass le_sup_left

/-- Complete the adjacent-vertex involution construction once the two actual
intersection types have been established. These types are the outstanding
47.6 double-coset calculation, not additional earlier-source assumptions. -/
theorem commonInvolution_at_neighbor_of_intersection_types
    (D : Seed G) (R : FourSuborbits D) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (hinner : ∀ g : localNormalizer D, (g : G) ∈ localCentralizer D →
      (g : G) ∉ actor D Y → Nonempty (intersection D Y g ≃* alternatingGroup (Fin 4)))
    (houter : ∀ g : localNormalizer D, (g : G) ∉ localCentralizer D →
      Nonempty (intersection D Y g ≃* DihedralGroup 5))
    (U : D.Vertex) (hU : D.graph.Adj D.base U) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t := by
  rcases neighbor_cover D R Y hY hF U hU with h | h | h
  · exact commonInvolution_of_le_join D Y U hF hclass (endpointOrbit_le_join D Y U h)
  · obtain ⟨g, hg, ha, rfl⟩ := h
    let m : localNormalizer D := ⟨g, centralizer_le_normalizer _ hg⟩
    apply commonInvolution_of_even_intersection D Y hF hclass m
    rw [Nat.card_congr (hinner m hg ha).some.toEquiv, nat_card_alternatingGroup]
    norm_num
  · obtain ⟨g, hg, hl, rfl⟩ := h
    let m : localNormalizer D := ⟨g, hg⟩
    apply commonInvolution_of_even_intersection D Y hF hclass m
    rw [Nat.card_congr (houter m hl).some.toEquiv, DihedralGroup.nat_card]
    norm_num

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
