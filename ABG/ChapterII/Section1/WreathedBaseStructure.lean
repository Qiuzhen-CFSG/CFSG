module
public import ABG.ChapterII.Section1.WreathedAbelianMaximal

/-!
# The abelian base structure of a wreathed group

This assembles ABG Chapter II §1 Lemma 2(ii), article pp.9–10: the chosen
base `U` is an abelian maximal subgroup of type `(2^n, 2^n)`, and is the unique
abelian subgroup of its order. The product coordinate equivalence gives the
type and cardinality; `abelian_maximal_unique` gives commutativity, maximality,
and uniqueness. The height and cardinality assumptions remain exactly those
of the chosen wreathed presentation.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

public theorem base_structure :
    Nonempty (P.U ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) ∧
    Nat.card P.U = 2 ^ (2 * n) ∧ IsMulCommutative P.U ∧ IsCoatom P.U ∧
      ∀ H : Subgroup S, IsMulCommutative H → Nat.card H = 2 ^ (2 * n) → H = P.U := by
  have h := P.abelian_maximal_unique
  refine ⟨⟨P.baseEquiv⟩, P.card_U, h.1, h.2.1, ?_⟩
  intro H hH hcard
  exact h.2.2 H hH (hcard.trans P.card_U.symm)

end ABG.Wreathed.Presentation
