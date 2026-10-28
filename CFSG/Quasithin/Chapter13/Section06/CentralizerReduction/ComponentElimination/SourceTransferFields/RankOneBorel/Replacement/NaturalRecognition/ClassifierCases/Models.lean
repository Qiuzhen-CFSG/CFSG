module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.Contracts
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.OrderFour
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Rank-one field transport and model exclusions

The strictly increasing SL₂ order polynomial identifies the field cardinality.
Finite-field uniqueness then gives an actual field isomorphism, which transports
both matrices and vectors in the natural representation. Thus a classified
natural action can use the original supplied field, rather than merely another
field of the same degree. Cyclic odd Sylow subgroups bound the three-rank, and
the order-four obstruction excludes the SL₃ rows.

These are the model comparisons in B.5.1 and B.5.6 used in the first paragraph
of 13.6.18 (Aschbacher–Smith, combined 1 March 2004 manuscript, pp.99–105, 931).
The order and field-action imports retain their ATLAS source attribution.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open scoped MatrixGroups CharTwo
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases
open ChapterB.QuasisimpleSource

private theorem polynomial_strictMono :
    StrictMonoOn (fun q : ℕ => q * (q ^ 2 - 1)) (Set.Ici 2) := by
  intro x hx y hy hxy
  change 2 ≤ x at hx
  change 2 ≤ y at hy
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hsq : x ^ 2 < y ^ 2 := by nlinarith
  have hmul := Nat.mul_lt_mul_of_pos_left (show x ^ 2 - 1 < y ^ 2 - 1 by omega)
    (show 0 < x by omega)
  exact hmul.trans_le (Nat.mul_le_mul_right (y ^ 2 - 1) hxy.le)

/-- The actual SL₂ isomorphism recovers the field cardinality. -/
theorem field_card_eq (F E : BinaryField)
    (e : SL(2,F.Carrier) ≃* SL(2,E.Carrier)) : Nat.card F.Carrier = Nat.card E.Carrier := by
  apply polynomial_strictMono.injOn (show 2 ≤ Nat.card F.Carrier from Finite.one_lt_card)
    (show 2 ≤ Nat.card E.Carrier from Finite.one_lt_card)
  simpa only [Atlas.card_sl_two] using Nat.card_congr e.toEquiv

/-- Transport all matrix entries and vector coordinates through one field isomorphism. -/
noncomputable def fieldNatural (F E : BinaryField) (d : ℕ) (e : F.Carrier ≃+* E.Carrier) :
    ActionEquiv (linearNatural F d) (linearNatural E d) := by
  let l : F.Carrier ≃ₗ[ZMod 2] E.Carrier :=
    { e.toAddEquiv with map_smul' := ZMod.map_smul e }
  refine ⟨Atlas.fieldEquivSL d e, LinearEquiv.piCongrRight (fun _ : Fin d => l), ?_⟩
  intro g v
  funext i
  change e (∑ j, g.val i j * v j) = ∑ j, e (g.val i j) * e (v j)
  simp only [map_sum, map_mul]

/-- An actual SL₂ isomorphism supplies field transport to the specified target field.
The resulting actor map is induced by that field transport. -/
noncomputable def sameFieldNatural (F E : BinaryField)
    (e : SL(2,F.Carrier) ≃* SL(2,E.Carrier)) :
    ActionEquiv (linearNatural F 2) (linearNatural E 2) := by
  letI := Fintype.ofFinite F.Carrier
  letI := Fintype.ofFinite E.Carrier
  exact fieldNatural F E 2 (FiniteField.ringEquivOfCardEq
    (by simpa only [← Nat.card_eq_fintype_card] using field_card_eq F E e))

/-- Odd Sylow subgroups in a faithful binary degree-two action are cyclic. -/
theorem three_rank_le (F : BinaryField) : primeRank 3 SL(2,F.Carrier) ≤ 1 := by
  let P : Sylow 3 SL(2,F.Carrier) := Classical.choice inferInstance
  let f : P →* SL(2,F.Carrier) := (P : Subgroup SL(2,F.Carrier)).subtype
  have hi : Function.Injective f := fun x y h => Subtype.ext h
  exact P.primeRank_le_one_of_isCyclic
    (Matrix.SL2.odd_pGroup_isCyclic_of_injective (F := F.Carrier) P.isPGroup' (by decide) f hi)

private theorem sl_three_order_four (F : BinaryField) : ∃ g : SL(3,F.Carrier), orderOf g = 4 := by
  let g := SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F.Carrier) *
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F.Carrier)
  have hs : g ^ 2 = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : F.Carrier) := by
    apply Subtype.ext
    simp [g, pow_two, SpecialLinearGroup.transvection_coe, mul_add, add_mul]
    ext a b
    simp only [Matrix.add_apply]
    abel_nf
    simp
  have hn : g ^ 2 ≠ 1 := by
    rw [hs]
    intro h
    have hh := congrArg (fun x : SL(3,F.Carrier) => x 0 2) h
    simp [SpecialLinearGroup.transvection_coe] at hh
  have hf : g ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, hs, pow_two,
      ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      SpecialLinearGroup.transvection_coeff_zero]
  exact ⟨g, @orderOf_eq_prime_pow _ _ g 1 2 ⟨Nat.prime_two⟩ hn hf⟩

/-- A size-three unipotent Jordan block excludes every SL₃ model. -/
theorem not_linearThree (F E : BinaryField) (e : SL(2,F.Carrier) ≃* SL(3,E.Carrier)) : False := by
  obtain ⟨g, hg⟩ := sl_three_order_four E
  exact CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.sl_order_ne_four
    (e.symm g) ((e.symm.orderOf_eq g).trans hg)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases
end
