module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Fusion.Matrices
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Coordinates

/-!
# Faithful finite coordinates on the literal Sylow

The coordinate word map is injective and respects the verified multiplication
law. Its 64 values lie in the explicit order-64 Sylow, so they exhaust that
literal subgroup. Each eight-element coordinate list defines a genuine
ambient subgroup of order eight. This retains the full actors and the actual
inner-matrix and graph elements used by the parent reselection theorem.

Source: Aschbacher--Smith E.1.14(7), printed p.214, and the coordinate
construction in `OuterReselection.Coordinates`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Matrix Pointwise IsMulCommutative
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Fusion
open FiveSourceAudit
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The literal ambient element represented by a coordinate. -/
@[expose] noncomputable def word (a : C) : Model :=
  innerSL (mat a.1) * if a.2 then graphElement else 1

theorem word_one : word ce = 1 := by
  simp [word, ce, mat_one]
theorem word_mul (a b : C) : word (cmul a b) = word a * word b := by
  obtain ⟨⟨d,e⟩,f⟩ := a
  obtain ⟨⟨d',e'⟩,f'⟩ := b
  cases f <;> cases f'
  · simp only [word, cmul, twist, Bool.false_xor, Bool.false_eq_true, ↓reduceIte, mul_one]
    rw [mat_mul (d,e) (d',e'), map_mul]
  · simp only [word, cmul, twist, Bool.false_xor, Bool.false_eq_true, ↓reduceIte, mul_one]
    rw [mat_mul (d,e) (d',e'), map_mul, mul_assoc]
  · change innerSL (mat (d + sw e (-d'), e ^^ e')) * graphElement =
      (innerSL (mat (d,e)) * graphElement) * (innerSL (mat (d',e')) * 1)
    rw [mat_mul (d,e) (-d',e'), map_mul, mul_one, mul_assoc, mul_assoc,
      graph_innerSL, ← mat_graph (d',e')]
  · have hs : graphElement * graphElement = 1 := by
      exact Subtype.ext (Matrix.PSL3.OuterSolvable.graph_sq (ZMod 5))
    change innerSL (mat (d + sw e (-d'), e ^^ e')) * 1 =
      (innerSL (mat (d,e)) * graphElement) * (innerSL (mat (d',e')) * graphElement)
    rw [mat_mul (d,e) (-d',e'), map_mul, mul_one]
    rw [mul_assoc, ← mul_assoc graphElement, graph_innerSL, ← mat_graph (d',e'),
      mul_assoc _ graphElement, hs, mul_one]

theorem word_inj : Function.Injective word := by
  intro a b h
  obtain ⟨a,c⟩ := a
  obtain ⟨b,d⟩ := b
  have ha : innerSL (mat a) ∈ FiveSourceAudit.inner := by rw [← innerSL_range]; exact ⟨_,rfl⟩
  have hb : innerSL (mat b) ∈ FiveSourceAudit.inner := by rw [← innerSL_range]; exact ⟨_,rfl⟩
  cases c <;> cases d
  · simp only [word, Bool.false_eq_true, ↓reduceIte, mul_one] at h
    exact congrArg (fun l => (l,false)) (mat_inj (innerSL_injective h))
  · simp only [word, Bool.false_eq_true, ↓reduceIte, mul_one] at h
    have ht := FiveSourceAudit.inner.mul_mem (FiveSourceAudit.inner.inv_mem hb) (h ▸ ha)
    simp only [inv_mul_cancel_left] at ht
    exact (graphElement_not_mem_inner ht).elim
  · simp only [word, Bool.false_eq_true, ↓reduceIte, mul_one] at h
    have ht := FiveSourceAudit.inner.mul_mem (FiveSourceAudit.inner.inv_mem ha) (h.symm ▸ hb)
    simp only [inv_mul_cancel_left] at ht
    exact (graphElement_not_mem_inner ht).elim
  · simp only [word, ↓reduceIte] at h
    exact congrArg (fun l => (l,true)) (mat_inj (innerSL_injective (mul_right_cancel h)))

theorem word_mem (a : C) : word a ∈ standardSylow := by
  change innerSL (mat a.1) * (if a.2 then graphElement else 1) ∈ standardSylow
  apply standardSylow.mul_mem
  · change innerSL (torusSL (ZMod 5) (u ^ a.1.1.1.val, u ^ a.1.1.2.val) *
      (if a.1.2 then signedSwap else 1)) ∈ standardSylow
    rw [map_mul]
    apply standardSylow.mul_mem (diagonal_mem_standardSylow _)
    split
    · exact signedSwap_mem_standardSylow
    · simp
  · split
    · exact graph_mem_standardSylow
    · exact standardSylow.one_mem

theorem word_surj : ∀ g ∈ standardSylow, ∃ a : C, word a = g := by
  let f : C → (standardSylow : Subgroup Model) := fun a => ⟨word a, word_mem a⟩
  have hf : Function.Injective f := fun a b h => word_inj (congrArg Subtype.val h)
  have hc : Nat.card (standardSylow : Subgroup Model) ≤ Nat.card C := by
    rw [standardSylow_coe, card_standardTwoGroup]
    simp [C, L, D]
  intro g hg
  obtain ⟨a,ha⟩ := (hf.bijective_of_nat_card_le hc).2 ⟨g,hg⟩
  exact ⟨a, congrArg Subtype.val ha⟩

/-- An entire listed eight-group in the actual graph extension. -/
@[expose] noncomputable def candidate (i : Fin 8) : Subgroup Model where
  carrier := {g | ∃ a ∈ codes i, word a = g}
  one_mem' := ⟨ce, codes_one i, word_one⟩
  mul_mem' := by
    rintro _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    exact ⟨cmul a b, codes_mul i a ha b hb, word_mul a b⟩
  inv_mem' := by
    rintro _ ⟨a,ha,rfl⟩
    have hs : word a * word a = 1 := by
      rw [← word_mul, codes_sq i a ha, word_one]
    exact ⟨a,ha,(inv_eq_of_mul_eq_one_left hs).symm⟩

theorem mem_candidate (i : Fin 8) (g : Model) :
    g ∈ candidate i ↔ ∃ a ∈ codes i, word a = g := Iff.rfl

theorem card_candidate (i : Fin 8) : Nat.card (candidate i) = 8 := by
  let f : (codes i) → candidate i := fun a => ⟨word a, a, a.property, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (word_inj (congrArg Subtype.val h))
    · rintro ⟨g,a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_finsetCard, codes_card]

theorem candidate_le_standardSylow (i : Fin 8) :
    candidate i ≤ (standardSylow : Subgroup Model) := by
  rintro _ ⟨a,_,rfl⟩
  exact word_mem a

/-- The first distinguished list is exactly the original whole actor. -/
theorem candidate_five : candidate 5 = actor := by
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [actor, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · refine ⟨(((2,0),false),false), by decide +kernel, ?_⟩
      have hm : mat ((2,0),false) = Matrix.SL3.standardInvolution (ZMod 5) := by decide +kernel
      simp [word, hm]
    · refine ⟨(((0,2),false),false), by decide +kernel, ?_⟩
      have hm : mat ((0,2),false) = secondDiagonal := by decide +kernel
      simp [word, hm]
    · refine ⟨(((0,0),false),true), by decide +kernel, ?_⟩
      simp [word, mat_one]
  · rw [card_candidate, card_actor]

/-- The second distinguished list is exactly the published representative. -/
theorem candidate_four : candidate 4 = representative := by
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [representative, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · refine ⟨(((2,0),false),false), by decide +kernel, ?_⟩
      have hm : mat ((2,0),false) = Matrix.SL3.standardInvolution (ZMod 5) := by decide +kernel
      simp [word, hm]
    · refine ⟨(((0,2),false),false), by decide +kernel, ?_⟩
      have hm : mat ((0,2),false) = secondDiagonal := by decide +kernel
      simp [word, hm, centralElement]
    · refine ⟨(((1,0),false),true), by decide +kernel, ?_⟩
      have hm : mat ((1,0),false) = twistDiagonal := by decide +kernel
      simp [word, hm, twistedGraph]
  · rw [card_candidate, card_representative]

private theorem inverse_transpose_inv (g : SL(3, ZMod 5)) :
    (Matrix.SpecialLinearGroup.transpose g⁻¹)⁻¹ = Matrix.SpecialLinearGroup.transpose g := by
  have h := (Matrix.PSL3.OuterSolvable.graphSL (ZMod 5)).map_inv g
  change (Matrix.SpecialLinearGroup.transpose g⁻¹)⁻¹ =
    ((Matrix.SpecialLinearGroup.transpose g)⁻¹)⁻¹ at h
  simpa only [inv_inv] using h

private theorem conjugate_word (g : SL(3, ZMod 5)) (a : C) :
    MulAut.conj (innerSL g) (word a) =
      innerSL (g * mat a.1 *
        (if a.2 then Matrix.SpecialLinearGroup.transpose g else g⁻¹)) *
        (if a.2 then graphElement else 1) := by
  obtain ⟨l,c⟩ := a
  cases c
  · simp only [MulAut.conj_apply, word, Bool.false_eq_true, ↓reduceIte,
      mul_one, map_mul, map_inv]
  · have ht := graph_innerSL g⁻¹
    rw [inverse_transpose_inv g] at ht
    simp only [MulAut.conj_apply, word, ↓reduceIte, map_mul]
    rw [← innerSL.map_inv g]
    simp only [mul_assoc, ht]
    simp only [map_inv, inv_mul_cancel_left]

/-- The explicit matrix witnesses give actual ambient conjugation equations
for every whole candidate subgroup. -/
theorem candidate_conjugate (i : Fin 8) :
    (candidate i).map (MulAut.conj (innerSL (witness i))).toMonoidHom =
      candidate (target i) := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨a,ha,rfl⟩,rfl⟩
    obtain ⟨b,hb,hbit,hm⟩ := witness_certificate i a ha
    refine ⟨b,hb,?_⟩
    change word b = MulAut.conj (innerSL (witness i)) (word a)
    rw [conjugate_word, hm]
    simp only [word, hbit]
  · rw [card_candidate, card_map_of_injective (MulAut.conj _).injective, card_candidate]

@[expose] noncomputable def inputCodes (A : Subgroup Model) : Finset C := by
  classical
  exact Finset.univ.filter (fun a => word a ∈ A)

theorem mem_inputCodes (A : Subgroup Model) (a : C) :
    a ∈ inputCodes A ↔ word a ∈ A := by
  classical
  simp [inputCodes]

theorem card_inputCodes (A : Subgroup Model) (hA : A ≤ (standardSylow : Subgroup Model)) :
    (inputCodes A).card = Nat.card A := by
  let f : inputCodes A → A := fun a => ⟨word a, (mem_inputCodes A a).mp a.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (word_inj (congrArg Subtype.val h))
    · intro g
      obtain ⟨a,ha⟩ := word_surj g (hA g.property)
      refine ⟨⟨a, (mem_inputCodes A a).mpr (ha.symm ▸ g.property)⟩, ?_⟩
      exact Subtype.ext ha
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_finsetCard]

/-- Application of the finite census to the exact literal subgroup, using
faithfulness and exhaustion of the fixed Sylow. -/
theorem candidate_of_census (hcensus : Census) (A : Subgroup Model)
    (hA : IsElementaryAbelian 2 A) (hAS : A ≤ (standardSylow : Subgroup Model))
    (hcard : Nat.card A = 8) : ∃ i, A = candidate i := by
  let _ := hA
  have hsquare (a : C) (ha : a ∈ inputCodes A) : cmul a a = ce := by
    apply word_inj
    rw [word_mul, word_one]
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) ⟨word a, (mem_inputCodes A a).mp ha⟩
    exact congrArg Subtype.val h
  have hcomm (a : C) (ha : a ∈ inputCodes A) (b : C) (hb : b ∈ inputCodes A) :
      cmul a b = cmul b a := by
    apply word_inj
    rw [word_mul, word_mul]
    exact congrArg Subtype.val (mul_comm (⟨word a,(mem_inputCodes A a).mp ha⟩ : A)
      ⟨word b,(mem_inputCodes A b).mp hb⟩)
  obtain ⟨i,hi⟩ := hcensus (inputCodes A) ((card_inputCodes A hAS).trans hcard)
    hsquare hcomm
  refine ⟨i, ?_⟩
  ext g
  constructor
  · intro hg
    obtain ⟨a,ha⟩ := word_surj g (hAS hg)
    refine ⟨a, ?_, ha⟩
    rw [← hi, mem_inputCodes, ha]
    exact hg
  · rintro ⟨a,ha,rfl⟩
    rw [← hi, mem_inputCodes] at ha
    exact ha

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Fusion
