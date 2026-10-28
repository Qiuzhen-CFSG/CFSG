module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.Subgroup
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Cosets
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson
public import Theory.GroupTheory.PresentedGroupBounds

/-!
# Exact order and counting interfaces for the concrete J₄ matrix group

`model_card` proves the order of the original ATLAS matrix carrier
unconditionally. The proof in `Cardinality.Thompson` combines the two full
involution centralizers and their certified local conjugacy census with the
refined Thompson bound. Certified subgroup and element orders give divisibility
by the source order; the proved ambient two-part makes the quotient odd, and
the bound below three source orders forces equality.

The preserved coset interfaces use the particular subgroup defined by the ATLAS program `J4G1-max1W1`;
see `Cardinality.Subgroup` for the source and its corrected word expansion.
The count is 501397585920 subgroup elements times 173067389 cosets.

A `GeneratorCosetCover` supplies the identity representative and actual group
identities for multiplication by each source generator and its inverse.
The established generation theorem therefore proves coverage of the concrete
matrix carrier. A separate coset-distinctness proof makes the multiplication
map from subgroup elements and representatives injective. Its bijectivity
then gives the exact cardinality without assuming an external enumeration.

The local subgroup's order is certified in `Cardinality.LocalOrder`. The
conditional coset and vector-orbit APIs remain available independently of the
Thompson proof; the exact index is now a consequence of the proved ambient order.

Source for the proposed subgroup and numerical factors:
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/J4G1-max1W1 .
-/

@[expose] public section
namespace Janko4.Cardinality

/-- The exact order of the original binary ATLAS matrix carrier, unconditionally. -/
theorem model_card : Nat.card Model = 86775571046077562880 :=
  Thompson.model_card

/-- A certified cover by distinct right cosets counts the concrete carrier. -/
theorem model_card_eq_of_max1_cover
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    {ι : Type*}
    (C : Subgroup.GeneratorCosetCover (max1Subgroup hA hB) (sourceGenerators hA hB) ι)
    (separate : ∀ i j, C.repr i * (C.repr j)⁻¹ ∈ max1Subgroup hA hB → i = j) :
    Nat.card Model = Nat.card (max1Subgroup hA hB) * Nat.card ι := by
  let H := max1Subgroup hA hB
  let f : H × ι → Model := fun p => p.1.val * C.repr p.2
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨h, i, hi⟩ := C.covers (sourceGenerators_generate hA hB) x
    exact ⟨(h, i), hi.symm⟩
  have hinj : Function.Injective f := by
    rintro ⟨h, i⟩ ⟨k, j⟩ he
    change h.val * C.repr i = k.val * C.repr j at he
    have hij : i = j := by
      apply separate
      have hr : C.repr i * (C.repr j)⁻¹ = h.val⁻¹ * k.val := by
        calc
          C.repr i * (C.repr j)⁻¹ =
              h.val⁻¹ * (h.val * C.repr i) * (C.repr j)⁻¹ := by simp
          _ = h.val⁻¹ * (k.val * C.repr j) * (C.repr j)⁻¹ := by rw [he]
          _ = h.val⁻¹ * k.val := by simp [mul_assoc]
      rw [hr]
      exact H.mul_mem (H.inv_mem h.property) k.property
    subst j
    have hhk : h = k := Subtype.ext (mul_right_cancel he)
    exact Prod.ext hhk rfl
  calc
    Nat.card Model = Nat.card (H × ι) :=
      Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
    _ = Nat.card (max1Subgroup hA hB) * Nat.card ι := Nat.card_prod _ _

/-- Final arithmetic assembly once the actual subgroup and coset certificates
have been supplied. This conditional theorem is not an order certification. -/
theorem model_card_of_max1_certificates
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hH : Nat.card (max1Subgroup hA hB) = 501397585920)
    (C : Subgroup.GeneratorCosetCover (max1Subgroup hA hB)
      (sourceGenerators hA hB) (Fin 173067389))
    (separate : ∀ i j, C.repr i * (C.repr j)⁻¹ ∈ max1Subgroup hA hB → i = j) :
    Nat.card Model = 86775571046077562880 := by
  rw [model_card_eq_of_max1_cover hA hB C separate, hH, Nat.card_fin]

/-- The certified local order leaves precisely the subgroup index to count. -/
theorem model_card_eq_max1_index_mul
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Nat.card Model = 501397585920 * (max1Subgroup hA hB).index := by
  rw [← (max1Subgroup hA hB).card_mul_index, max1Subgroup_card hA hB]

/-- The target group order is equivalent to the remaining concrete index
obligation. No index certificate is assumed to exist. -/
theorem model_card_iff_max1_index
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Nat.card Model = 86775571046077562880 ↔
      (max1Subgroup hA hB).index = 173067389 := by
  rw [model_card_eq_max1_index_mul hA hB]
  omega

/-- A distinct coset cover suffices now that the local subgroup order has
been proved. The cover and separation remain concrete proof obligations. -/
theorem model_card_of_max1_cover
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (C : Subgroup.GeneratorCosetCover (max1Subgroup hA hB)
      (sourceGenerators hA hB) (Fin 173067389))
    (separate : ∀ i j, C.repr i * (C.repr j)⁻¹ ∈ max1Subgroup hA hB → i = j) :
    Nat.card Model = 86775571046077562880 :=
  model_card_of_max1_certificates hA hB (max1Subgroup_card hA hB) C separate

/-- Assemble the checked local order with the two outstanding vector-action
obligations. Neither the orbit count nor the stabilizer identification follows
from the local order alone. -/
theorem model_card_of_vectorOrbit
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (horbit : Nat.card CosetVectorOrbit = 173067389)
    (hst : cosetVectorStabilizer ≤ max1Subgroup hA hB) :
    Nat.card Model = 86775571046077562880 := by
  obtain ⟨C, separate⟩ := max1_cosetCertificate_of_vectorOrbit hA hB horbit hst
  exact model_card_of_max1_cover hA hB C separate

/-- The literal max1 subgroup has the source index, for either proof of the
certified generator identities. -/
theorem max1Subgroup_index
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    (max1Subgroup hA hB).index = 173067389 :=
  (model_card_iff_max1_index hA hB).mp model_card

end Janko4.Cardinality
