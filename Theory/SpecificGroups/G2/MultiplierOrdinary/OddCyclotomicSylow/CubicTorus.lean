module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.BlockRealization.Algebra
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.GroupTheory.Index

/-!
# A cubic norm-one torus in the actual G₂ model

The norm-one units of the degree-three finite-field extension form a cyclic
subgroup of order q² + q + 1. Their regular multiplication matrices have
determinant one. The faithful Peirce-block homomorphism embeds these matrices
in the literal split-octonion automorphism group, in every characteristic.

This supplies the cubic cyclotomic branch of the Sylow calculation behind
Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408, and GLS III §6.1. The
Sylow-index calculation and the universal-kernel application are supplied
by `OddCyclotomicSylow`. This result does not construct the twisted torus
of order q² − q + 1.

The Peirce-block multiplication uses the attributed ATLAS octonion model;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow

open Matrix Subgroup
open scoped MatrixGroups
open Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization

noncomputable section
variable (F : Type*) [Field F] [Finite F]

/-- A faithful image of the cubic norm-one units in the actual model. -/
theorem exists_cubic_torus (p : ℕ) [Fact p.Prime] [CharP F p] :
    ∃ C : Subgroup (Atlas.G2.Model F), IsCyclic C ∧
    Nat.card C = Nat.card F ^ 2 + Nat.card F + 1 := by
  let E := FiniteField.Extension F p 3
  let N : Eˣ →* Fˣ := Units.map (Algebra.norm F)
  let b := Module.finBasisOfFinrankEq F E (FiniteField.finrank_extension F p 3)
  let ρ : N.ker →* SL(3,F) :=
    { toFun := fun u => ⟨Algebra.leftMulMatrix b (u.val : E), by
        rw [← Algebra.norm_eq_matrix_det]
        exact congrArg Units.val u.property⟩
      map_one' := by apply Subtype.ext; exact map_one (Algebra.leftMulMatrix b)
      map_mul' := by intro u v; apply Subtype.ext; exact map_mul (Algebra.leftMulMatrix b) _ _ }
  have hρ : Function.Injective ρ := by
    intro u v huv
    apply Subtype.ext
    apply Units.ext
    exact Algebra.leftMulMatrix_injective b (congrArg Subtype.val huv)
  have hb : Function.Injective (blockHom (K := F)) := by
    intro A B h
    apply Subtype.ext
    simpa only [peirceMatrix_blockHom] using congrArg
      Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.peirceMatrix h
  let f := (blockHom (K := F)).comp ρ
  let e : N.ker ≃* f.range := MonoidHom.ofInjective (show Function.Injective f from hb.comp hρ)
  have hc : Nat.card N.ker * (Nat.card F - 1) = Nat.card F ^ 3 - 1 := by
    have h := N.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
      (FiniteField.unitsMap_norm_surjective F E), Nat.card_congr Subgroup.topEquiv.toEquiv,
      Nat.card_units, Nat.card_units, FiniteField.natCard_extension] at h
    exact h
  refine ⟨f.range, e.isCyclic.mp inferInstance, ?_⟩
  rw [← Nat.card_congr e.toEquiv]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card F - 1 by omega)
  rw [hc]
  have he : Nat.card F - 1 + 1 = Nat.card F := Nat.sub_add_cancel (by omega)
  apply Nat.sub_eq_of_eq_add
  nlinarith

end

end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow
