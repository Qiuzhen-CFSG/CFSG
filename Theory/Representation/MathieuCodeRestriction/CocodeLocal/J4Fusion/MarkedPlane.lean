module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.PairNormalizer

/-!
# A concrete Todd pair plane through the second involution

The classes of {0,1}, {0,2}, and {1,2} are the three nonzero elements of a
four-element subspace. Their word relation and injective pair parametrization
construct the source pair plane, rather than adding its existence as a premise.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), proof of (6.3), p.602.
-/

@[expose] public section
namespace MathieuCode.J4Fusion
open Subgroup Sporadic.Mathieu

private def A : PointPair := ⟨{0,1},by decide⟩
private def B : PointPair := ⟨{0,2},by decide⟩
private def C : PointPair := ⟨{1,2},by decide⟩

private theorem triangle_sum : pairVector A + pairVector B = pairVector C := by
  change codeInCore.mkQ _ + codeInCore.mkQ _ = codeInCore.mkQ _
  rw [←map_add]
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  funext i
  change wordOfSet A.val i + wordOfSet B.val i = wordOfSet C.val i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;>
    simp_all [wordOfSet,A,B,C]

/-- The actual coordinate triangle through the selected pair {0,1}. -/
noncomputable def markedPairPlane : Submodule (ZMod 2) Cocode :=
  Submodule.span (ZMod 2) {pairVector ⟨{0,1},by decide⟩,pairVector ⟨{0,2},by decide⟩}

private theorem markedPairPlane_elements (v : Cocode) :
    v ∈ markedPairPlane ↔ v=0 ∨ v=pairVector A ∨ v=pairVector B ∨ v=pairVector C := by
  change v ∈ Submodule.span (ZMod 2) {pairVector A,pairVector B} ↔ _
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a,b,rfl⟩
    have bits (x : ZMod 2) : x=0 ∨ x=1 := by revert x; decide
    rcases bits a with rfl | rfl <;> rcases bits b with rfl | rfl
    · simp only [zero_smul,add_zero,true_or]
    · simp only [zero_smul,one_smul,zero_add,true_or,or_true]
    · simp only [zero_smul,one_smul,add_zero,true_or,or_true]
    · simp only [one_smul,triangle_sum,or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0,0,by simp⟩
    · exact ⟨1,0,by simp⟩
    · exact ⟨0,1,by simp⟩
    · exact ⟨1,1,by simpa using triangle_sum⟩

theorem markedPairPlane_mem : pairVector ⟨{0,1},by decide⟩ ∈ markedPairPlane :=
  (markedPairPlane_elements _).mpr (Or.inr (Or.inl rfl))

theorem markedPairPlane_pairs (v : Cocode) (hv : v ∈ markedPairPlane) (hne : v≠0) :
    ∃ P : PointPair, v=pairVector P := by
  rcases (markedPairPlane_elements v).mp hv with he | he | he | he
  · exact (hne he).elim
  · exact ⟨A,he⟩
  · exact ⟨B,he⟩
  · exact ⟨C,he⟩

theorem markedPairPlane_card : Nat.card markedPairPlane = 4 := by
  classical
  let s : Finset Cocode := {0,pairVector A,pairVector B,pairVector C}
  let e : markedPairPlane ≃ s := {
    toFun := fun v => ⟨v.val,by simpa only [s,Finset.mem_insert,Finset.mem_singleton] using
      (markedPairPlane_elements v).mp v.property⟩
    invFun := fun v => ⟨v.val,(markedPairPlane_elements v).mpr (by
      simpa only [s,Finset.mem_insert,Finset.mem_singleton] using v.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]
  have hAB : pairVector A ≠ pairVector B := fun he =>
    (by decide : A ≠ B) (pairVector_injective he)
  have hAC : pairVector A ≠ pairVector C := fun he =>
    (by decide : A ≠ C) (pairVector_injective he)
  have hBC : pairVector B ≠ pairVector C := fun he =>
    (by decide : B ≠ C) (pairVector_injective he)
  simp [s,(pairVector_ne_zero A).symm,(pairVector_ne_zero B).symm,
    (pairVector_ne_zero C).symm,hAB,hAC,hBC]

end MathieuCode.J4Fusion
