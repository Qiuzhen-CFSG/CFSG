module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Action
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour
public import Theory.GroupTheory.NormalizerCentralizerLift

/-!
# A literal max4 plane and its full automizer

The words numbered 0, 1, 2, 5 in the certified max4 eight form a plane.
Every automorphism of this plane is realized by an actual max4 word: its
images of indices 1 and 2, followed by index 3, form a basis of the eight,
and the existing ordered-basis table supplies the word. Thus an upper bound
on the FULL ambient centralizer of this plane gives an upper bound on its
full normalizer. The normalizer is strictly smaller than max4, because the
latter has no normal subgroup of order four.

Only the centralizer bound and the literal conjugacy to kernel candidate 2
remain in the final application. No maximality or irreducibility is assumed.
Source context: Aschbacher--Smith A.3.12, printed pp.47--48;
Kleidman--Wilson (1988), pp.484--510. All words retain the ATLAS max4 embedding.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear
open Janko4.LocalStructure.SymmetricLinear.NormalEight
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightAction
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

/-- Indices in the existing eight-word table, with exactly its original numbering. -/
def planeIndex (i : Fin 4) : Fin 8 := ![0, 1, 2, 5] i

private def planeProduct (i j : Fin 4) : Fin 4 :=
  ⟨(i.val ^^^ j.val) % 4, Nat.mod_lt _ (by decide)⟩

private lemma planeIndex_product : ∀ i j,
    planeIndex (planeProduct i j) = productIndex (planeIndex i) (planeIndex j) := by
  decide +kernel

/-- The plane as a subgroup of the actual max4 carrier. -/
def localPlane : Subgroup max4Subgroup where
  carrier := Set.range (fun i : Fin 4 => element (planeIndex i))
  one_mem' := ⟨0, element_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    refine ⟨planeProduct i j, ?_⟩
    change element (planeIndex (planeProduct i j)) = _
    rw [planeIndex_product, element_mul]
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i, eq_inv_of_mul_eq_one_left (element_sq _)⟩

/-- The plane with its literal ambient inclusion; this is the centralizer input. -/
def max4Plane : Subgroup Model := localPlane.map max4Subgroup.subtype

private def localElement (i : Fin 4) : localPlane :=
  ⟨element (planeIndex i), ⟨i, rfl⟩⟩

private lemma localElement_injective : Function.Injective localElement := by
  intro i j h
  have hi : Function.Injective planeIndex := by decide +kernel
  exact hi (element_injective (congrArg Subtype.val h))

private lemma localElement_surjective : Function.Surjective localElement := by
  rintro ⟨u, ⟨i, rfl⟩⟩
  exact ⟨i, rfl⟩

/-- Four distinct literal words, without relying on an abstract model order. -/
theorem localPlane_card : Nat.card localPlane = 4 :=
  (Nat.card_congr (Equiv.ofBijective localElement
    ⟨localElement_injective, localElement_surjective⟩).symm).trans (Nat.card_fin 4)

theorem max4Plane_card : Nat.card max4Plane = 4 :=
  (card_map_of_injective max4Subgroup.subtype_injective).trans localPlane_card

private def ambientElement (i : Fin 4) : max4Plane :=
  ⟨(element (planeIndex i) : Model), mem_map_of_mem _ (show element (planeIndex i) ∈ localPlane from ⟨i, rfl⟩)⟩

private lemma ambientElement_injective : Function.Injective ambientElement := by
  intro i j h
  apply localElement_injective
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : max4Plane => (z : Model)) h

private lemma ambientElement_surjective : Function.Surjective ambientElement := by
  rintro ⟨u, ⟨v, ⟨i, rfl⟩, rfl⟩⟩
  exact ⟨i, rfl⟩

private lemma ambientElement_zero : ambientElement 0 = 1 := by
  apply Subtype.ext
  exact congrArg (fun z : max4Subgroup => (z : Model)) element_zero

private lemma ambientElement_three : ambientElement 3 = ambientElement 1 * ambientElement 2 := by
  apply Subtype.ext
  exact congrArg (fun z : max4Subgroup => (z : Model)) (element_mul 1 2).symm

private def wordElement : List Bool → max4Subgroup
  | [] => 1
  | b :: w => (if b then y else x) * wordElement w

private lemma wordElement_conj (w : List Bool) (i : Fin 8) :
    (wordElement w)⁻¹ * element i * wordElement w = element (wordAction w i) := by
  induction w generalizing i with
  | nil => simp [wordElement, wordAction]
  | cons b w ih =>
    cases b <;> simp only [wordElement, wordAction, Bool.false_eq_true, if_false,
      if_true, mul_inv_rev]
    · calc
        _ = (wordElement w)⁻¹ * (x⁻¹ * element i * x) * wordElement w := by group
        _ = _ := by rw [element_conj_x, ih]
    · calc
        _ = (wordElement w)⁻¹ * (y⁻¹ * element i * y) * wordElement w := by group
        _ = _ := by rw [element_conj_y, ih]

/-- Each automorphism of the literal plane is induced by an actual max4 word. -/
theorem max4Plane_realizes_automorphism (f : MulAut max4Plane) :
    ∃ g : max4Subgroup, ∀ u : max4Plane,
      (f u : Model) = (g : Model)⁻¹ * (u : Model) * (g : Model) := by
  obtain ⟨i, hi⟩ := ambientElement_surjective (f (ambientElement 1))
  obtain ⟨j, hj⟩ := ambientElement_surjective (f (ambientElement 2))
  have hi0 : i ≠ 0 := by
    intro he
    rw [he, ambientElement_zero, ← map_one f, ← ambientElement_zero] at hi
    exact (by decide : (0 : Fin 4) ≠ 1) (ambientElement_injective (f.injective hi))
  have hj0 : j ≠ 0 := by
    intro he
    rw [he, ambientElement_zero, ← map_one f, ← ambientElement_zero] at hj
    exact (by decide : (0 : Fin 4) ≠ 2) (ambientElement_injective (f.injective hj))
  have hji : j ≠ i := by
    intro he
    rw [he, hi] at hj
    exact (by decide : (1 : Fin 4) ≠ 2) (ambientElement_injective (f.injective hj))
  have hb : IsBasis (planeIndex i) (planeIndex j) 3 := by
    have h : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → j ≠ i →
        IsBasis (planeIndex i) (planeIndex j) 3 := by decide +kernel
    exact h i j hi0 hj0 hji
  let w := wordFor (planeIndex i) (planeIndex j) 3
  obtain ⟨h1, h2, _⟩ := wordFor_spec _ _ _ hb
  have h1' : (f (ambientElement 1) : Model) =
      (wordElement w : Model)⁻¹ * (ambientElement 1 : Model) * (wordElement w : Model) := by
    rw [← hi]
    exact (congrArg (fun z : max4Subgroup => (z : Model))
      ((wordElement_conj w 1).trans (congrArg element h1))).symm
  have h2' : (f (ambientElement 2) : Model) =
      (wordElement w : Model)⁻¹ * (ambientElement 2 : Model) * (wordElement w : Model) := by
    rw [← hj]
    exact (congrArg (fun z : max4Subgroup => (z : Model))
      ((wordElement_conj w 2).trans (congrArg element h2))).symm
  refine ⟨wordElement w, ?_⟩
  intro u
  obtain ⟨k, rfl⟩ := ambientElement_surjective u
  fin_cases k
  · change (f (ambientElement 0) : Model) =
      (wordElement w : Model)⁻¹ * (ambientElement 0 : Model) * (wordElement w : Model)
    rw [ambientElement_zero, map_one]
    simp only [Subgroup.coe_one, mul_one, inv_mul_cancel]
  · exact h1'
  · exact h2'
  · change (f (ambientElement 3) : Model) =
      (wordElement w : Model)⁻¹ * (ambientElement 3 : Model) * (wordElement w : Model)
    rw [ambientElement_three, map_mul]
    change (f (ambientElement 1) : Model) * (f (ambientElement 2) : Model) = _
    rw [h1', h2']
    change _ = (wordElement w : Model)⁻¹ *
      ((ambientElement 1 : Model) * (ambientElement 2 : Model)) * (wordElement w : Model)
    group

/-- Surjectivity uses the full automorphism group of the actual embedded plane. -/
theorem max4Plane_action_surjective : Function.Surjective (max4Plane.normalizerMonoidHom.comp
    (max4Subgroup.subgroupOf (normalizer (max4Plane : Set Model))).subtype) := by
  intro f
  obtain ⟨g, hg⟩ := max4Plane_realizes_automorphism f
  have hn : (g : Model)⁻¹ ∈ normalizer (max4Plane : Set Model) := by
    rw [mem_normalizer_iff]
    intro u
    simp only [inv_inv]
    constructor
    · intro hu
      exact (hg ⟨u, hu⟩) ▸ (f ⟨u, hu⟩).property
    · intro hu
      obtain ⟨v, hv⟩ := f.surjective ⟨(g : Model)⁻¹ * u * g, hu⟩
      have he := congrArg (fun z : max4Plane => (z : Model)) hv
      rw [hg v] at he
      have he' : (v : Model) = u := mul_left_cancel (mul_right_cancel he)
      exact he' ▸ v.property
  refine ⟨⟨⟨(g : Model)⁻¹, hn⟩, max4Subgroup.inv_mem g.property⟩, ?_⟩
  ext u
  change (g : Model)⁻¹ * (u : Model) * ((g : Model)⁻¹)⁻¹ = (f u : Model)
  rw [inv_inv, hg u]

/-- Only full-centralizer containment remains for the literal plane normalizer. -/
theorem max4Plane_normalizer_lt_of_centralizer
    (hC : centralizer (max4Plane : Set Model) ≤ max4Subgroup) :
    normalizer (max4Plane : Set Model) < max4Subgroup := by
  refine lt_of_le_not_ge
    (normalizer_le_of_centralizer_le_of_surjective _ _ hC max4Plane_action_surjective) ?_
  intro h
  have hn : (max4Plane.subgroupOf max4Subgroup).Normal :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le localPlane)).mpr h
  have he : max4Plane.subgroupOf max4Subgroup = localPlane := by
    exact comap_map_eq_self_of_injective max4Subgroup.subtype_injective localPlane
  rw [he] at hn
  let := hn
  exact max4_normal_card_ne_four localPlane localPlane_card

/-- Literal conjugacy transports the strict proper overgroup to kernel candidate 2.
The centralizer premise concerns the entire ambient model. -/
theorem candidate_two_obstruction_of_max4Plane
    (hC : centralizer (max4Plane : Set Model) ≤ max4Subgroup)
    (hconj : ∃ k : Model, max4Plane.map (MulAut.conj k).toMonoidHom = candidate 2) :
    ∃ H : Subgroup Model,
      normalizer (candidate (exceptionalIndex 0) : Set Model) < H ∧ H < ⊤ := by
  obtain ⟨k, hk⟩ := hconj
  refine ⟨max4Subgroup.map (MulAut.conj k).toMonoidHom, ?_, ?_⟩
  · change normalizer (candidate 2 : Set Model) < _
    rw [← hk, ← map_equiv_normalizer_eq]
    exact (map_lt_map_iff_of_injective (MulAut.conj k).injective).mpr
      (max4Plane_normalizer_lt_of_centralizer hC)
  · apply lt_top_iff_ne_top.mpr
    intro he
    have hm : max4Subgroup = ⊤ := by
      apply (map_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective)
      rw [map_top_of_surjective _ (MulAut.conj k).surjective]
      exact he
    exact literal_max4_ne_top hm

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
