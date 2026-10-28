module

public import Theory.Representation.DegreeFourFrattini
public import Theory.SpecificGroups.SymplecticFour.Flag
public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Small Sylow Frattini quotients of odd classical groups

A Sylow subgroup of a quotient is the image of an actual Sylow subgroup of
its cover. Frattini functoriality makes its Frattini quotient an image too.
The natural representations of SL, SU and Sp in dimension at most four
therefore give a bound of 128 in characteristic different from two.

The consumer is the original residual's inner action in Aschbacher–Smith
4.4.10, printed p.621, through the Sylow restriction criterion of I.3.1.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.OddClassicalSylowFrattini

/-- Surjective images preserve any uniform Sylow Frattini bound. -/
theorem card_le_of_surjective {H S : Type*} [Group H] [Group S] [Finite H]
    (f : H →* S) (hf : Function.Surjective f) {b : ℕ}
    (hH : ∀ Q : Sylow 2 H, Nat.card (Q ⧸ frattini Q) ≤ b)
    (P : Sylow 2 S) : Nat.card (P ⧸ frattini P) ≤ b := by
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf 2 P
  let g := f.subgroupMap (Q : Subgroup H)
  have hg : Function.Surjective g := f.subgroupMap_surjective (Q : Subgroup H)
  have hphi := frattini_le_comap_frattini_of_surjective hg
  have hq := QuotientGroup.map_surjective_of_surjective
    (frattini Q) (frattini ((Q : Subgroup H).map f)) g
    ((QuotientGroup.mk'_surjective _).comp hg) hphi
  exact (Nat.card_le_card_of_surjective _ hq).trans (hH Q)

variable {F : Type*} [Field F] [Finite F]

/-- The actual projective linear quotient inherits the degree-four bound. -/
theorem psl_card_le_128 {n : ℕ} (hn : n ≤ 4) (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 PSL(n,F)) : Nat.card (P ⧸ frattini P) ≤ 128 := by
  apply card_le_of_surjective (QuotientGroup.mk' (center SL(n,F)))
    (QuotientGroup.mk'_surjective _) ?_ P
  intro Q
  exact Representation.card_frattini_quotient_le_128_of_injective_generalLinear Q.isPGroup'
    (Matrix.SpecialLinearGroup.toGL.comp (Q : Subgroup SL(n,F)).subtype)
    (Matrix.SpecialLinearGroup.toGL_injective.comp Subtype.val_injective) h2 hn

/-- The unitary quotient uses its literal projective image in PGL. -/
theorem psu_card_le_128 {n : ℕ} (J : BenderSuzuki.MatrixGroups.HermitianForm n F)
    (hn : n ≤ 4) (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) ≤ 128 := by
  apply card_le_of_surjective (Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup)
    (Matrix.ProjGenLinGroup.mk.subgroupMap_surjective J.specialSubgroup) ?_ P
  intro Q
  exact Representation.card_frattini_quotient_le_128_of_injective_generalLinear Q.isPGroup'
    (J.specialSubgroup.subtype.comp (Q : Subgroup J.specialSubgroup).subtype)
    (Subtype.val_injective.comp Subtype.val_injective) h2 hn

/-- The symplectic four-space quotient inherits the same uniform bound. -/
theorem psp_four_card_le_128 (h2 : (2 : F) ≠ 0)
    (P : Sylow 2 (SymplecticFour.Sp F ⧸ center (SymplecticFour.Sp F))) :
    Nat.card (P ⧸ frattini P) ≤ 128 := by
  apply card_le_of_surjective (QuotientGroup.mk' (center (SymplecticFour.Sp F)))
    (QuotientGroup.mk'_surjective _) ?_ P
  intro Q
  have hi : Function.Injective (Representation.symplecticNatural (k := F) 2) := by
    intro x y hxy
    apply Subtype.ext
    apply Matrix.toLin'.injective
    exact hxy
  apply Representation.card_frattini_quotient_le_128_of_faithful_degree_four Q.isPGroup'
    ((Representation.symplecticNatural 2).comp (Q : Subgroup (SymplecticFour.Sp F)).subtype)
    (hi.comp Subtype.val_injective) h2
  simp only [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]
  norm_num

end Theory.SpecificGroups.OddClassicalSylowFrattini
