module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion.Inputs
public import Theory.Representation.BinaryOffender.InnerNormalizerActors
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer
public import Theory.GroupAction.AutomorphismNormalizer

/-!
# Source hypotheses and Rudvalis normalizer automorphisms

The small double-centralizer calculation bounds the matrix group's center
by two. Binary irreducibility and faithfulness kill its central involutions,
so the center is trivial. The supplied quasisimplicity then yields simplicity
of the marked permutation model, allowing the existing point-stabilizer-class
producer to be used with its literal hypotheses.

Preservation of that class and the checked full permutation-normalizer
calculation make every automorphism inner. Trivial center ensures that an
involutory automorphism has an involutory inner representative. This is the
precise premise needed to descend elementary linear-normalizer actors.

Source: GLS3, Table 5.3r, and Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, Ru paragraph, manuscript p.17. Stabilizer preservation and
the local centralizer calculation remain explicit independent obligations.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion

/-- Schur's lemma eliminates the at-most-two-element center. -/
theorem standard_center_eq_bot_of_lowCentralizers
    (hi : standardRepresentation.IsIrreducible) (hC : LowInvolutionCentralizers) :
    center standardGroup = ⊥ := by
  let C := centralizer ({standardB ^ 2} : Set standardGroup)
  have hle : center standardGroup ≤ centralizer (C : Set standardGroup) := by
    intro z hz
    exact mem_centralizer_iff.mpr fun g _ => mem_center_iff.mp hz g
  have hc : Nat.card (center standardGroup) ≤ 2 :=
    (Nat.card_le_card_of_injective _ (inclusion_injective hle)).trans
      (hC (standardB ^ 2) (IsConj.refl _)).2
  have hcpos : 0 < Nat.card (center standardGroup) := Nat.card_pos
  have hdiv : Nat.card (center standardGroup) ∣ 2 := by
    have hcases : Nat.card (center standardGroup) = 1 ∨
        Nat.card (center standardGroup) = 2 := by omega
    rcases hcases with h | h <;> simp [h]
  let : IsIrreducible (standardRepresentation.comp (⊤ : Subgroup standardGroup).subtype) :=
    (irreducible_comp_surjective_iff (⊤ : Subgroup standardGroup).subtype (fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
      standardRepresentation).mpr hi
  apply le_bot_iff.mp
  intro z hz
  rw [mem_bot]
  have hz2 : (⟨z, hz⟩ : center standardGroup) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard _).trans hdiv)
  apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
    standardRepresentation (⊤ : Subgroup standardGroup) standardRepresentation_injective
    (congrArg Subtype.val hz2)
  exact mem_centralizer_iff.mpr fun g _ => mem_center_iff.mp hz g

/-- Source quasisimplicity becomes actual simplicity after the center calculation. -/
theorem model_isSimple_of_lowCentralizers (hmodel : StandardComparison)
    (hq : IsQuasisimple standardGroup) (hi : standardRepresentation.IsIrreducible)
    (hC : LowInvolutionCentralizers) : IsSimpleGroup Rudvalis.Model := by
  let : IsSimpleGroup (standardGroup ⧸ center standardGroup) := hq.simple
  let : IsSimpleGroup standardGroup :=
    ((QuotientGroup.quotientMulEquivOfEq (standard_center_eq_bot_of_lowCentralizers hi hC)).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨e, _, _⟩ := hmodel
  exact e.isSimpleGroup

/-- Transport the perfectness already present in the source hypothesis. -/
theorem model_isPerfect (hmodel : StandardComparison) (hq : IsQuasisimple standardGroup) :
    Group.IsPerfect Rudvalis.Model := by
  let : IsQuasisimple standardGroup := hq
  obtain ⟨e, _, _⟩ := hmodel
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The existing stabilizer-class obligation supplies the needed inner representatives. -/
theorem standard_involutory_inner_of_pointStabilizers (hmodel : StandardComparison)
    (hi : standardRepresentation.IsIrreducible) (hC : LowInvolutionCentralizers)
    (hstable : ∀ f : MulAut Rudvalis.Model, ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y) :
    ∀ α : MulAut standardGroup, α ^ 2 = 1 →
      ∃ x : standardGroup, x ^ 2 = 1 ∧ α = MulAut.conj x := by
  let : MulAction.IsPretransitive Rudvalis.modelSubgroup (Fin 4060) :=
    Rudvalis.model_isPretransitive
  have hs := Subgroup.conj_surjective_of_stabilizers_of_normalizer
    Rudvalis.modelSubgroup 0 hstable Rudvalis.outer_permutation_normalizer_eq
  obtain ⟨e, _, _⟩ := hmodel
  intro α hα
  obtain ⟨y, hy⟩ := hs (MulAut.congr e.symm α)
  obtain ⟨x, hx⟩ := (MulAut.congr_inner_iff e.symm α).mp ⟨y, hy.symm⟩
  refine ⟨x, ?_, hx⟩
  apply MulAut.conj_injective_of_center_eq_bot (standard_center_eq_bot_of_lowCentralizers hi hC)
  rw [map_pow, ← hx, hα, map_one]

/-- A marked group equivalence transports the intrinsic rank bound. -/
theorem standard_rank_le_of_model_rank (hmodel : StandardComparison)
    (hr : primeRank 2 Rudvalis.Model ≤ 6) : primeRank 2 standardGroup ≤ 6 := by
  obtain ⟨e, _, _⟩ := hmodel
  rwa [← primeRank_equiv 2 e]

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion
