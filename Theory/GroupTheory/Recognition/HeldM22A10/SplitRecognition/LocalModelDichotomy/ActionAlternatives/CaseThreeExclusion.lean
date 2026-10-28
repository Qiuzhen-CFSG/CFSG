module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.AmbientCoordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseThreeExclusion.SourceGroups
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseThreeExclusion.Ambient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseThreeExclusion.LocalGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseThreeExclusion.WordInvolutions

/-!
# Excluding Janko Case III by ambient transfer

The embedded source subgroups and source marking are those of `SourceGroups`.
`LocalGeometry` proves their orders, word coverage and the derived subgroup
of the full local centralizer of `d`. `WordInvolutions` constructs an
elementary subgroup of order sixteen centralizing each involution of `H`.

The characteristic derived line is the original involution line, so the
local centralizer is Sylow in the ambient centralizer of `d`. Thompson
transfer conjugates `d` into `H`, forcing that nonabelian Sylow subgroup
to be elementary abelian. `Ambient` proves this contradiction, and the final
theorem supplies every local premise to exclude Case III under the original
finite simple ambient hypotheses. The earlier conditional assembly remains
available as `false_of_source_computations`.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, pp.2–3, DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseThreeExclusion
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- The five local computations and the coordinate involution calculation feed
Thompson transfer on the literal source Sylow subgroup. The source marking is
identified with the original involution by `sourceZ_eq`. -/
public theorem false_of_source_computations
    (D : LocalData G) (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)
    (R : JankoCoordinates (D.binaryAction K hK) .three)
    (hT : Nat.card (sourceT D K hK R) = 128)
    (hH : Nat.card (sourceH D K hK R) = 64)
    (hwords : ∀ t : G, t ∈ sourceH D K hK R →
      ∃ (v : BinaryFour) (i j : Fin 2), t = sourceHWord D K hK R v i j)
    (hcard : Nat.card (D.centralizer ⊓
      centralizer ({jankoAmbientComplement D K hK jankoD} : Set G) : Subgroup G) = 16)
    (hderived : ⁅D.centralizer ⊓
        centralizer ({jankoAmbientComplement D K hK jankoD} : Set G),
      D.centralizer ⊓ centralizer ({jankoAmbientComplement D K hK jankoD} : Set G)⁆ =
        zpowers (sourceZ D K hK R))
    (helementary : ∀ (v : BinaryFour) (i j : Fin 2),
      orderOf (sourceHWord D K hK R v i j) = 2 →
      ∃ E : Subgroup G, E ≤ centralizer ({sourceHWord D K hK R v i j} : Set G) ∧
        IsElementaryAbelian 2 E ∧ Nat.card E = 16) : False := by
  apply false_of_local_configuration D (sourceT D K hK R) (sourceH D K hK R)
    (jankoAmbientComplement D K hK jankoD) hT (sourceH_le_sourceT D K hK R) hH
    (sourceD_mem_sourceT D K hK R) (sourceD_order D K hK) hcard
  · simpa only [sourceZ_eq D K hK R] using hderived
  · intro t ht horder
    obtain ⟨v, i, j, rfl⟩ := hwords t ht
    exact helementary v i j horder

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseThreeExclusion

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- Janko Case III cannot occur for the actual binary complement action in
a finite simple ambient group. All local computations needed by the transfer
argument are discharged using the literal kernel and complement embeddings. -/
public theorem not_nonempty_jankoCoordinates_three
    (D : LocalData G) (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K) :
    ¬ Nonempty (JankoCoordinates (D.binaryAction K hK) .three) := by
  rintro ⟨R⟩
  exact CaseThreeExclusion.false_of_source_computations D K hK R
    (CaseThreeExclusion.sourceT_card D K hK R)
    (CaseThreeExclusion.sourceH_card D K hK R)
    (CaseThreeExclusion.sourceH_words D K hK R)
    (CaseThreeExclusion.sourceCentralizer_card D K hK R)
    (CaseThreeExclusion.sourceCentralizer_derived D K hK R)
    (CaseThreeExclusion.sourceHWord_elementary_centralizer D K hK R)

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
