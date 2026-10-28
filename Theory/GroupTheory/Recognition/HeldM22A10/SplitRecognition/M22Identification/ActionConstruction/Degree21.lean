module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.ConditionalAssembly
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.Existence
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.OddOrders
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction

/-!
# Janko's degree-21 character

The actual normalizer characters and their special inductions construct an
irreducible complex character with the seven marked local values. The complete
irreducible-family calculation proves minimum nonprincipal degree 21 and
uniqueness at that degree. The local group analysis excludes every additional
odd order, and the conditional assembly supplies the prime-order values and
all even-order alternatives. Together these prove every field of
`Degree21Character` from the stated local analysis, ambient order and
Sylow-three normalizer order.

The public conditional assembly is preserved in `ConditionalAssembly`, so its
independent prerequisites do not import this final construction.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 6--7, especially pp.15--16,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
open LocalModelDichotomy
universe u

/-- Janko's genuine irreducible character of degree 21, with minimum degree,
uniqueness, and the exhaustive order/value table. The special induction data,
character existence, degree bounds and odd-order spectrum are all constructed
from the original inputs. -/
public theorem nonempty_of_local_analysis
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (Subgroup.normalizer (P : Set G)) = 72) :
    Nonempty (Degree21Character G) := by
  obtain ⟨I⟩ := CharacterOrder.nonempty_specialInductionData D k L
  obtain ⟨χ, hχ, hloc⟩ := exists_irreducible_of_local_analysis D k L hcard hN3 I
  exact SmallDegrees.nonempty_of_induction_character_and_odd_structure D k L hcard I
    χ hχ hloc (odd_orders D k L hcard hN3)

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
