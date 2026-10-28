module

public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.IndexNormal

/-!
# The cubic normalizer on a binary plane

Every order-three subgroup of the order-six automorphism group is normal.
The full normalizer therefore acts as S₃, with an actual group isomorphism
from the original four-group to the standard binary plane intertwining all
automorphisms. The model action permutes the three nonzero plane vectors.

Source: Aschbacher--Smith, 15.4.12(6)(i), printed pp.1160--1161.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer

abbrev BinaryPlane := Multiplicative (ZMod 2 × ZMod 2)

/-- The usual action of S₃ on the three nonzero vectors of the binary plane. -/
noncomputable def symmetricThreeAction : Equiv.Perm (Fin 3) →* MulAut BinaryPlane :=
  (IsKleinFour.autEquivPermThree BinaryPlane).symm.toMonoidHom

/-- The full automorphism normalizer of a cubic on a binary plane is S₃,
with coordinates intertwining its given action on every vector. -/
theorem single_normalizer_coordinates {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (A : Subgroup (MulAut W)) (hA : Nat.card A = 3) :
    ∃ (c : W ≃* BinaryPlane) (e : normalizer (A : Set (MulAut W)) ≃* Equiv.Perm (Fin 3)),
      ∀ (g : normalizer (A : Set (MulAut W))) (w : W),
        c ((g : MulAut W) w) = symmetricThreeAction (e g) (c w) := by
  have : Nontrivial W := (Finite.one_lt_card_iff_nontrivial (α := W)).mp (by omega)
  let : IsKleinFour W := ⟨hW, IsElementaryAbelian.exponent_eq_prime⟩
  have hindex : A.index = 2 := by
    have hc := A.card_mul_index
    rw [hA,IsKleinFour.card_mulAut] at hc
    omega
  let : A.Normal := A.normal_of_index_eq_two hindex
  have hn : normalizer (A : Set (MulAut W)) = ⊤ := normalizer_eq_top A
  let r : normalizer (A : Set (MulAut W)) ≃* MulAut W :=
    (MulEquiv.subgroupCongr hn).trans Subgroup.topEquiv
  obtain ⟨c⟩ := (IsKleinFour.nonempty_mulEquiv : Nonempty (W ≃* BinaryPlane))
  let e := r.trans ((MulAut.congr c).trans (IsKleinFour.autEquivPermThree BinaryPlane))
  refine ⟨c,e,?_⟩
  intro g w
  change c ((g : MulAut W) w) =
    (IsKleinFour.autEquivPermThree BinaryPlane).symm
      ((IsKleinFour.autEquivPermThree BinaryPlane) (MulAut.congr c (r g))) (c w)
  rw [MulEquiv.symm_apply_apply]
  change c ((g : MulAut W) w) = c ((r g) (c.symm (c w)))
  rw [c.symm_apply_apply]
  rfl

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer
