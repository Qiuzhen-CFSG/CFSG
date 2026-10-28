module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.XCensus

/-!
# Construction of Janko's local configuration

The original local analysis constructs the literal derived F-normalizer X,
the common order-three actor Q*, and an involution z* outside N(F). The
reflection theorem proves X ∩ Xᶻ* = EQ* and the complete census of EQ*⟨z*⟩.
Combining it with the census of X discharges every premise of the local
configuration assembly, including the double-coset lower bound 20160.

The only inputs are the stated local analysis and ambient source hypotheses.
The resulting configuration supplies the local subgroup input to the later
degree-21 character argument; properness and index 22 are proved there.
This extension keeps the reflection proofs independent of their final assembly.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, Section 8, Lemma 17, pp.16--17;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The full local configuration in Janko's Lemma 17, with the X census and
reflection geometry proved from the explicit local and ambient hypotheses. -/
public theorem exists_localConfiguration (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ)) :
    Nonempty (LocalConfiguration G) :=
  localConfiguration_of_X_census D k L hcard hN3 horders (X_count D k L)

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
