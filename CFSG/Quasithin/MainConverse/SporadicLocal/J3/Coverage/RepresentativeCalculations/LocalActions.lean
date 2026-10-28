module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.LocalActions.Binary
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.LocalActions.Basis
import Mathlib.Tactic.FinCases

/-!
# Local actions and a rank-three transporter for the fixed J₃ representatives

The basis equations are checked on all 6156 letters in `LocalActions.Basis`.
Binary addition extends them to the elementary spans. Positive words in the
unchanged local generators take the standard involution to every nonidentity
point of E and U. The fixed affine word [5,5,5,6,5,5] has basis images
[4,6,5,8], normalizes E, and carries B into D.

Source: the concrete finite-calculation route to GLS, Number 3, Table 5.3h,
printed p.269, using the retained ATLAS J₃ model. This proves the local-action
inputs to `LocalReduction`, not the table's ambient normalizer conclusions.
The sole hypothesis is the permitted order of the fixed Sylow candidate.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal Theory.GroupTheory
open LocalActions
set_option Elab.async false

namespace LocalActions

@[expose] public def affineAction (k : Fin 7) : Fin 16 → Fin 16 :=
  linearImage (affineBasisImage k)

@[expose] public def thompsonAction (k : Fin 8) : Fin 16 → Fin 16 :=
  linearImage (thompsonBasisImage k)

public theorem affine_image (hS : Nat.card sylowCandidate = 128) (k : Fin 7) (i : Fin 16) :
    (MulAut.conj (affineGenerator k)) (elementaryElement i) =
      elementaryElement (affineAction k i) := by
  apply image_elementaryElement hS (MulAut.conj (affineGenerator k)).toMonoidHom 15 (affineBasisImage k)
  · exact fun j _ => affine_basis_image k j
  · exact (by decide +kernel : ∀ i : Fin 16, supported 15 i) i

public theorem thompson_image (hS : Nat.card sylowCandidate = 128)
    (k : Fin 8) (i : Fin 16) (hi : supported 5 i) :
    (MulAut.conj (thompsonNormalizerGenerator k)) (elementaryElement i) =
      elementaryElement (thompsonAction k i) :=
  image_elementaryElement hS (MulAut.conj (thompsonNormalizerGenerator k)).toMonoidHom
    5 (thompsonBasisImage k) (thompson_basis_image k) i hi

private theorem affine_supported (k : Fin 7) (i : Fin 16) (_hi : supported 15 i) :
    supported 15 (affineAction k i) :=
  (by decide +kernel : ∀ i : Fin 16, supported 15 i) _

private theorem thompson_supported (k : Fin 8) (i : Fin 16) (hi : supported 5 i) :
    supported 5 (thompsonAction k i) :=
  (by decide +kernel : ∀ k i, supported 5 i → supported 5 (thompsonAction k i)) k i hi

@[expose] public def affineOrbitWord : Fin 16 → List (Fin 7)
  | 1 => []
  | 2 => [5]
  | 3 => [5, 6, 5, 4]
  | 4 => [4, 4, 5, 4]
  | 5 => [4, 5]
  | 6 => [4]
  | 7 => [6, 4]
  | 8 => [4, 6, 4]
  | 9 => [5, 6, 4]
  | 10 => [5, 4, 6, 4]
  | 11 => [5, 4]
  | 12 => [4, 5, 4]
  | 13 => [6, 6]
  | 14 => [6]
  | 15 => [6, 5, 4]
  | _ => []

@[expose] public def thompsonOrbitWord : Fin 16 → List (Fin 8)
  | 1 => []
  | 4 => [6, 7]
  | 5 => [7]
  | _ => []

end LocalActions

/-- The affine local candidate normalizes the fixed elementary group E. -/
public theorem localFamily_one_le_normalizer (hS : Nat.card sylowCandidate = 128) :
    localFamily 1 ≤ normalizer (elementaryCandidate : Set Model) := by
  change closure (Set.range affineGenerator) ≤ _
  apply (closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  rw [← elementarySpan_full hS]
  exact normalizes_span hS _ 15 (affineBasisImage k)
    (fun j _ => affine_basis_image k j) (affine_supported k)

/-- The Thompson local candidate normalizes the fixed four-group U. -/
public theorem localFamily_two_le_normalizer (hS : Nat.card sylowCandidate = 128) :
    localFamily 2 ≤ normalizer (elementaryRepresentative 2 : Set Model) := by
  change closure (Set.range thompsonNormalizerGenerator) ≤ _
  apply (closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  rw [← elementarySpan_representative hS 2]
  exact normalizes_span hS _ 5 (thompsonBasisImage k)
    (thompson_basis_image k) (thompson_supported k)

/-- The fixed affine candidate is transitive on the fifteen nonidentity points of E. -/
public theorem localFamily_one_transitive (hS : Nat.card sylowCandidate = 128)
    (x : Model) (hx : x ∈ elementaryCandidate) (hx1 : x ≠ 1) :
    ∃ m ∈ localFamily 1, (MulAut.conj m) a = x := by
  obtain ⟨i, rfl⟩ := (mem_elementaryCandidate_iff hS x).mp hx
  have hi : i ≠ 0 := by
    rintro rfl
    exact hx1 elementaryElement_zero
  refine ⟨evalWord affineGenerator (affineOrbitWord i),
    word_mem _ _ affineGenerator_mem _, ?_⟩
  have h := (word_image affineGenerator 15 affineAction
    (fun k i _ => affine_image hS k i) affine_supported (affineOrbitWord i) 1
      (by decide)).2
  have ht : ∀ i : Fin 16, i ≠ 0 → (affineOrbitWord i).foldr affineAction 1 = i := by
    decide +kernel
  rw [ht i hi] at h
  simpa only [show elementaryElement 1 = a from
    (elementaryElement_basis 0).trans elementaryGenerator_zero] using h

/-- The fixed Thompson candidate is transitive on the three nonidentity points of U. -/
public theorem localFamily_two_transitive (hS : Nat.card sylowCandidate = 128)
    (x : Model) (hx : x ∈ elementaryRepresentative 2) (hx1 : x ≠ 1) :
    ∃ m ∈ localFamily 2, (MulAut.conj m) a = x := by
  obtain ⟨i, hi, rfl⟩ := (mem_elementaryRepresentative_iff hS 2 x).mp hx
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hx1 elementaryElement_zero
  refine ⟨evalWord thompsonNormalizerGenerator (thompsonOrbitWord i),
    word_mem _ _ thompsonNormalizerGenerator_mem _, ?_⟩
  have h := (word_image thompsonNormalizerGenerator 5 thompsonAction
    (thompson_image hS) thompson_supported (thompsonOrbitWord i) 1 (by decide)).2
  have ht : ∀ i : Fin 16, supported 5 i → i ≠ 0 →
      (thompsonOrbitWord i).foldr thompsonAction 1 = i := by decide +kernel
  rw [ht i hi hi0] at h
  simpa only [show elementaryElement 1 = a from
    (elementaryElement_basis 0).trans elementaryGenerator_zero] using h

/-- The specified transporter; the original affine generators and word are retained. -/
@[expose] public def rankThreeTransporter : Model :=
  evalWord affineGenerator [5, 5, 5, 6, 5, 5]

public theorem rankThreeTransporter_mem_normalizer (hS : Nat.card sylowCandidate = 128) :
    rankThreeTransporter ∈ normalizer (elementaryCandidate : Set Model) :=
  localFamily_one_le_normalizer hS (word_mem _ _ affineGenerator_mem _)

/-- The four basis images of the actual fixed model word. -/
public theorem rankThreeTransporter_basis_image (hS : Nat.card sylowCandidate = 128)
    (j : Fin 4) :
    (MulAut.conj rankThreeTransporter) (elementaryGenerator j) =
      elementaryElement (![4, 6, 5, 8] j) := by
  have hj : supported 15 (basisMask j) :=
    (by decide +kernel : ∀ i : Fin 16, supported 15 i) _
  have h := (word_image affineGenerator 15 affineAction
    (fun k i _ => affine_image hS k i) affine_supported
    [5, 5, 5, 6, 5, 5] (basisMask j) hj).2
  have ht : ∀ j : Fin 4,
      ([5, 5, 5, 6, 5, 5] : List (Fin 7)).foldr affineAction (basisMask j) =
        ![4, 6, 5, 8] j := by decide +kernel
  rw [ht, elementaryElement_basis] at h
  exact h

/-- The transporter carries B into the rank-three representative D. -/
public theorem rankThreeTransporter_map_le (hS : Nat.card sylowCandidate = 128) :
    (elementaryRepresentative 1).map (MulAut.conj rankThreeTransporter).toMonoidHom ≤
      elementaryRepresentative 3 := by
  apply map_le_iff_le_comap.mpr
  rw [← elementarySpan_representative hS 1]
  apply elementarySpan_le
  intro j hj
  change (MulAut.conj rankThreeTransporter) (elementaryGenerator j) ∈ elementaryRepresentative 3
  rw [rankThreeTransporter_basis_image hS]
  apply (mem_elementaryRepresentative_iff hS 3 _).mpr
  refine ⟨![4, 6, 5, 8] j, ?_, rfl⟩
  fin_cases j <;> first | decide | contradiction

/-- The complete transporter input consumed by the ambient centralizer reduction. -/
public theorem rankThree_transporter (hS : Nat.card sylowCandidate = 128) :
    ∃ g : Model, g ∈ normalizer (elementaryCandidate : Set Model) ∧
      (elementaryRepresentative 1).map (MulAut.conj g).toMonoidHom ≤
        elementaryRepresentative 3 :=
  ⟨rankThreeTransporter, rankThreeTransporter_mem_normalizer hS,
    rankThreeTransporter_map_le hS⟩

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations
