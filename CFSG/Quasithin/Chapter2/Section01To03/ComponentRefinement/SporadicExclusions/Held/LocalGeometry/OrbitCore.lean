module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.LocalGeometry.Transport
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.Quasithin.EvenCharacteristic

/-!
# Characteristic two for the Held component orbit

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
2.3.9(7), printed p.526.

The quotient preimage of an invariant Held local subgroup has a
self-centralizing intrinsic two-core.  Relative component-orbit calculus then
transports this condition across the full supplied Sylow subgroup, allowing
that subgroup to permute conjugate components.  Only the stabilizer of the
component is used to normalize the preimage.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The self-centralizing two-core of a model subgroup lifts to its actual
component preimage, retaining the central two-kernel. -/
theorem componentPreimage_selfCentralizingCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (P : Subgroup Held.He)
    (hP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    centralizer (pCore 2 (componentPreimage d P) :
      Set (componentPreimage d P)) ≤
        pCore 2 (componentPreimage d P) := by
  have hi := preimage_selfCentralizingCore h d P hP
  let e := (P.comap (modelMap d)).equivMapOfInjective
    L.subtype L.subtype_injective
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hi

/-- An invariant Held local subgroup gives a characteristic-two overgroup after
adjoining the whole supplied Sylow subgroup.  The model Sylow containment is
retained as an explicit source hypothesis for the concrete local pair. -/
theorem localOvergroup_mem_He (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (P : Subgroup Held.He)
    (_hSylow : (modelSylow h d : Subgroup Held.He) ≤ P)
    (hP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P)
    (hInv : ∀ a ∈ modelActors d ((S : Subgroup H).map H.subtype),
      P.map a.toMonoidHom = P) :
    localOvergroup d ((S : Subgroup H).map H.subtype) P ∈ Chapter1.He G := by
  let := h.finite
  exact h.component.relative_local_adjoin_centralizer h.component_le
    (componentPreimage_le d P) (map_subtype_le _)
    (S.isPGroup'.map H.subtype)
    (componentPreimage_normalized d ((S : Subgroup H).map H.subtype) P hInv)
    ((inf_centralizer_pCoreIn_le_iff 2 _).mpr
      (componentPreimage_selfCentralizingCore h d P hP))

end CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

end
