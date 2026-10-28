module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.LocalLowerBound

/-!+# Order comparison for the ambient max1 seed centralizer

The centralizer of `(xy)^14` inside literal max1 embeds in its centralizer
in the actual J₄ matrix carrier. The checked 276-point local orbit bound
gives at least 1816657920 elements in this embedded subgroup. An ambient
upper bound of the same size therefore forces equality and containment
in max1.

The ambient upper bound remains a separate proof obligation. In particular,
neither intrinsic self-centralization of the binary kernel nor fusion of
the seed identifies its full ambient centralizer.

Source: GLS3, Table 5.3i, printed p.270, gives the expected 2B centralizer
shape E₂¹¹.(M₂₂.2). The actual matrix word and its local order are certified
in `Cardinality.Subgroup` and `Cardinality.LocalOrder`.
-/

public section

namespace Janko4.LocalStructure.MathieuSeedCentralizer
open Subgroup Cardinality

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

/-- The full centralizer of the literal seed in the original matrix carrier. -/
@[expose] def ambientSeedCentralizer : Subgroup Model :=
  centralizer ({(localKernelSeed hA hB : Model)} : Set Model)

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernelSeed

/-- Faithful inclusion transports the local centralizer into the ambient one. -/
theorem map_localSeedCentralizer_le :
    (centralizer ({localKernelSeed hA hB} : Set (max1Subgroup hA hB))).map
      (max1Subgroup hA hB).subtype ≤ ambientSeedCentralizer hA hB := by
  rintro g ⟨z, hz, rfl⟩ t ht
  obtain rfl := Set.mem_singleton_iff.mp ht
  exact congrArg (fun w : max1Subgroup hA hB => (w : Model))
    (hz _ (Set.mem_singleton _))

/-- The ambient centralizer contains the independently counted local subgroup. -/
theorem ambientSeedCentralizer_card_ge :
    1816657920 ≤ Nat.card (ambientSeedCentralizer hA hB) := by
  have h := Subgroup.card_le_of_le (map_localSeedCentralizer_le hA hB)
  rw [Subgroup.card_map_of_injective (max1Subgroup hA hB).subtype_injective] at h
  exact (localSeedCentralizer_card_ge hA hB).trans h

/-- A matching ambient upper bound forces every centralizer element into max1.
The numerical hypothesis must be established for the full matrix centralizer. -/
theorem ambientSeedCentralizer_le_max1_of_card_le
    (hcard : Nat.card (ambientSeedCentralizer hA hB) ≤ 1816657920) :
    ambientSeedCentralizer hA hB ≤ max1Subgroup hA hB := by
  have hge : Nat.card (ambientSeedCentralizer hA hB) ≤
      Nat.card ((centralizer ({localKernelSeed hA hB} : Set (max1Subgroup hA hB))).map
        (max1Subgroup hA hB).subtype) := by
    rw [Subgroup.card_map_of_injective (max1Subgroup hA hB).subtype_injective]
    exact hcard.trans (localSeedCentralizer_card_ge hA hB)
  rw [← Subgroup.eq_of_le_of_card_ge (map_localSeedCentralizer_le hA hB) hge]
  rintro g ⟨z, _, rfl⟩
  exact z.property

end Janko4.LocalStructure.MathieuSeedCentralizer
