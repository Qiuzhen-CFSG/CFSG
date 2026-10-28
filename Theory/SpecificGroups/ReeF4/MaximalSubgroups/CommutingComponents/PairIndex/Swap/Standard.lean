module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.PairIndex.Geometry
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits

/-!
# A concrete Weyl interchange for the two orthogonal B₂ planes

The square of the product of the middle and end relative reflections acts on
root coordinates by `(x₁,x₂,x₃,x₄) ↦ (x₃,x₄,-x₁,-x₂)`. Its square negates every
root, so it normalizes the full signed middle-node Levi. The fixed Weyl element
therefore interchanges that Levi with its conjugate in the orthogonal plane.

These are subgroups of the concrete Ree model. Identifying arbitrary supplied
components with this pair and proving properness of the pair normalizer remain
separate obligations; they are not encoded into either subgroup definition.

Source: the F₄ root and Weyl construction in GLS3, §2.3–2.4,
`refs/KGroup/GLS3/chapter2.tex`; the Suzuki-wreath subgroup in Malle,
J. Algebra 139 (1991), 52–69, DOI 10.1016/0021-8693(91)90283-E.
The coordinate reflection calculation follows `FixedCollection/WeylGeometry/Orbits`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.MaximalSubgroups.CommutingComponents.PairSwap

open Subgroup Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics.Binary.FixedGeometry LocalBlockInput.PairRigidity
open LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open CarrierIdentification

private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- A fixed Weyl word exchanging the two coordinate planes supporting B₂. -/
def interchangeElement (m : ℕ) : Model m :=
  (weylLift m .suzuki * weylLift m .linear) ^ 2

/-- The partner is an actual conjugate subgroup of the concrete Ree group. -/
def standardPartner (m : ℕ) : Subgroup (Model m) :=
  (standardSuzukiLevi m).map (MulAut.conj (interchangeElement m)).toMonoidHom

/-- The numbered simple-root word for the fixed interchange. -/
def interchangeWord : List (Fin 4) :=
  (sideWord .suzuki ++ sideWord .linear) ++ (sideWord .suzuki ++ sideWord .linear)

@[simp] theorem interchangeElement_val (m : ℕ) :
    (interchangeElement m).val = simpleWord m interchangeWord := by
  simp [interchangeElement, interchangeWord, weylLift, simpleWord, pow_two, mul_assoc]

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

/-- The root action exchanges the two orthogonal coordinate planes. -/
theorem interchangeWord_action_val (r : F4Chevalley.Root) :
    (wordAction interchangeWord r).val = ![r.val 2, r.val 3, -r.val 0, -r.val 1] := by
  ext k
  fin_cases k <;>
    norm_num [wordAction, interchangeWord, sideWord, Equiv.Perm.mul_apply,
      reflection_val, reflectedVector, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

private theorem interchangeWord_action_twice (r : F4Chevalley.Root) :
    wordAction interchangeWord (wordAction interchangeWord r) = -r := by
  apply Subtype.ext
  have hn : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  rw [hn, interchangeWord_action_val, interchangeWord_action_val]
  ext k
  fin_cases k <;> rfl

/-- Conjugation acts on every root matrix with the parameter unchanged. -/
theorem interchangeElement_conj_root (m : ℕ) (r : F4Chevalley.Root)
    (t : CoefficientField m) :
    (interchangeElement m).val * rootGeneratorInGroup m r t *
      (interchangeElement m).val⁻¹ =
      rootGeneratorInGroup m (wordAction interchangeWord r) t := by
  rw [interchangeElement_val, simpleWord_conj_root]

/-- The square of the interchange negates every root, with its parameter unchanged. -/
theorem interchangeElement_sq_conj_root (m : ℕ) (r : F4Chevalley.Root)
    (t : CoefficientField m) :
    ((interchangeElement m).val ^ 2) * rootGeneratorInGroup m r t *
      ((interchangeElement m).val ^ 2)⁻¹ =
      rootGeneratorInGroup m (typeF4RootPairing.reflectionPerm r r) t := by
  rw [interchangeElement_val]
  calc
    _ = simpleWord m interchangeWord *
        (simpleWord m interchangeWord * rootGeneratorInGroup m r t *
          (simpleWord m interchangeWord)⁻¹) * (simpleWord m interchangeWord)⁻¹ := by rw [pow_two]; group
    _ = _ := by
      rw [simpleWord_conj_root, simpleWord_conj_root, interchangeWord_action_twice]
      rfl

private theorem interchangeElement_sq_mem_split_normalizer (m : ℕ) :
    (interchangeElement m).val ^ 2 ∈ normalizer (splitLevi m .suzuki : Set (SplitGroup m)) := by
  have h : splitLevi m .suzuki ≤ (splitLevi m .suzuki).comap
      (MulAut.conj ((interchangeElement m).val ^ 2)).toMonoidHom := by
    apply sup_le
    all_goals
      apply (closure_le _).mpr
      rintro _ ⟨r, t, hr, rfl⟩
      change ((interchangeElement m).val ^ 2) * rootGeneratorInGroup m r t *
        ((interchangeElement m).val ^ 2)⁻¹ ∈ splitLevi m .suzuki
      rw [interchangeElement_sq_conj_root]
    · exact mem_sup_right (subset_closure ⟨-r, t,
        (isSimpleBlockRoot_neg_iff .suzuki true r).mpr hr, rfl⟩)
    · exact mem_sup_left (subset_closure ⟨-r, t,
        (isSimpleBlockRoot_neg_iff .suzuki false r).mpr hr, rfl⟩)
  exact mem_normalizer_fintype fun _ hx => h hx

/-- No order-two assertion is needed: the square normalizes the full fixed Levi. -/
theorem interchangeElement_sq_mem_normalizer (m : ℕ) :
    interchangeElement m ^ 2 ∈ normalizer (standardSuzukiLevi m : Set (Model m)) := by
  apply Subgroup.le_normalizer_comap (fixedSubgroup m).subtype
  exact interchangeElement_sq_mem_split_normalizer m

/-- The fixed Weyl word really interchanges both specified standard subgroups. -/
theorem interchange_standard_pair (m : ℕ) :
    (standardSuzukiLevi m).map (MulAut.conj (interchangeElement m)).toMonoidHom =
        standardPartner m ∧
      (standardPartner m).map (MulAut.conj (interchangeElement m)).toMonoidHom =
        standardSuzukiLevi m := by
  refine ⟨rfl, ?_⟩
  have he : ((MulAut.conj (interchangeElement m)).toMonoidHom).comp
      (MulAut.conj (interchangeElement m)).toMonoidHom =
      (MulAut.conj (interchangeElement m ^ 2)).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [pow_two]
    group
  rw [standardPartner, map_map, he]
  exact mem_normalizer_iff_map_conj_eq.mp (interchangeElement_sq_mem_normalizer m)

/-- Remaining common-centralizer bound for the concrete fixed middle-node Levi.
The supplied carrier equivalence is inherited from the identified component. -/
def StandardCentralizerBound : Prop :=
  ∀ m, 1 ≤ m →
    (standardSuzukiLevi m ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
      centralizer (standardSuzukiLevi m : Set (Model m)) ≤ standardPartner m

/-- Remaining properness calculation for the concrete pair. The carrier
equivalence is available without a separate model-identification theorem. -/
def StandardPairProper : Prop :=
  ∀ m, 1 ≤ m →
    (standardSuzukiLevi m ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
      normalizer ((standardSuzukiLevi m ⊔ standardPartner m : Subgroup (Model m)) :
        Set (Model m)) ≠ ⊤

end ReeF4.MaximalSubgroups.CommutingComponents.PairSwap
