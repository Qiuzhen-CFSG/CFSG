module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.Construction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.RootValues
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.Assembly
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.ActorCentralizers

/-!
# The five characters induced from the marked inertia subgroup

The construction supplies five distinct actual normalizer characters of degrees
45,45,30,15,15. The marked actor centralizer orders 32,36,8 complete the nine
centralizer orders used by the class-sum calculation. Character norm integrality
selects the correct order-four fusion, giving every printed table value and
norm one for each induced character, hence irreducibility.

`normalizerInducedBlock` packages these very induced characters, and
`nonempty_normalizerInducedBlock` supplies the requested existence theorem.
Only the original local-analysis and class-data inputs remain; all fusion and
centralizer premises of the conditional assembly are discharged. The arbitrary
A6 complement is used through the actual quotient, without assuming it contains
the marked S4 actors.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.10–11.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)

include L in
/-- All nine centralizer orders for the classes meeting the marked inertia subgroup. -/
public theorem normalizerFixedCentralizer_card (i : Fin 9) :
    Nat.card (centralizer ({normalizerFixedRepresentative D k i} :
      Set (normalizer (CaseII.E D k : Set G)))) = normalizerFixedCentralizerOrders i :=
  normalizerFixedCentralizer_card_of_actors D k L
    (normalizerFixedCentralizer_card_actors D k L) i

/-- Every value of each actual induced character agrees with Janko's printed row. -/
public theorem normalizerInducedCharacter_values (Q : NormalizerClassData D k)
    (j : Fin 5) (r : Fin 12) :
    normalizerInducedCharacter D k L j (Q.representative r) =
      normalizerFullValues 0 (Fin.natAdd 7 j) r := by
  obtain ⟨swap, hf⟩ := exists_normalizerInertiaFusion D k L
  exact normalizerInducedCharacter_values_of_fusion_centralizers D k L Q swap hf
    (normalizerFixedCentralizer_card D k L) j r

/-- The five actual characters induced from the marked inertia subgroup are irreducible. -/
public theorem normalizerInducedCharacter_irreducible (Q : NormalizerClassData D k)
    (j : Fin 5) : IsIrreducibleCharacter (normalizerInducedCharacter D k L j) := by
  obtain ⟨swap, hf⟩ := exists_normalizerInertiaFusion D k L
  exact normalizerInducedCharacter_irreducible_of_fusion_centralizers D k L Q swap hf
    (normalizerFixedCentralizer_card D k L) j

/-- The five constructed induced characters, with irreducibility and all twelve columns. -/
public def normalizerInducedBlock (Q : NormalizerClassData D k) :
    NormalizerInducedBlock Q where
  character := normalizerInducedCharacter D k L
  irreducible := normalizerInducedCharacter_irreducible D k L Q
  values := normalizerInducedCharacter_values D k L Q

include L in
/-- The induced block exists from the original local analysis and chosen class representatives. -/
public theorem nonempty_normalizerInducedBlock (Q : NormalizerClassData D k) :
    Nonempty (NormalizerInducedBlock Q) :=
  ⟨normalizerInducedBlock D k L Q⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
