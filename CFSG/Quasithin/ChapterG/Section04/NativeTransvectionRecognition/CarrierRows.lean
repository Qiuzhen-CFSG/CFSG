module
public import CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition.OddModels
public import CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition.BenderModels
public import CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition.LinearModels
public import CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition.G2Models
public import CFSG.Quasithin.ChapterG.Section04.OneCentralizer.Sporadic
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Assembling the proved native degree-four carrier rows

The actual faithful symplectic action excludes the linear and G₂ rows.
One literal involution with a two-group centralizer excludes the unitary,
odd ternary and sporadic rows. The alternating and odd linear reductions
retain A₅ and A₆ explicitly; the binary derived symplectic row is also
converted to its actual A₆ carrier. The original Theorem C parameters and
quotient matrix carriers are retained for PSL₂, Suzuki and PSp₄.

The remaining three exceptional families are displayed as an exact separate
output until their independent local proofs are applied. This theorem does
not assert the degree-four module recognition or a coefficient embedding.
Source: Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
open ChapterA.Section02 ClassificationModels Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Field F] [CharP F 2]

/-- The native carrier rows, retaining the binary A₆ endpoint separately. -/
def IsNativeDegreeFourCarrier (H : Type*) [Group H] : Prop :=
  Nonempty (H ≃* alternatingGroup (Fin 5)) ∨
  Nonempty (H ≃* alternatingGroup (Fin 6)) ∨
  (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSL H 2 (2^f)) ∨
  (∃ m : ℕ, 1≤m ∧ Nonempty (H ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
  (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSp H 2 (2^f))

/-- The three exact independent exceptional rows still requiring inspection. -/
def IsExceptionalDegreeFourCarrier (H : Type*) [Group H] : Prop :=
  (∃ f : ℕ, 1≤f ∧ Triality.Standard.IsTrialityGroupAt (2^f) H) ∨
  (∃ m : ℕ, 1≤m ∧ Nonempty (H ≃* ReeF4.Model m)) ∨
  Nonempty (H ≃* Tits.ParrottGroup)

/-- Assemble all completed Theorem C rows on the literal representation. -/
theorem native_or_exceptional_of_theoremC
    (hns : ¬Group.IsSolvable H) (hm : IsTheoremCModel H)
    (t : H) (ht : orderOf t=2) (hc : IsPGroup 2 (centralizer ({t} : Set H)))
    (j : H →* Sp F) (hj : Function.Injective j) :
    IsNativeDegreeFourCarrier H ∨ IsExceptionalDegreeFourCarrier H := by
  cases hm with
  | alternating n hn iso =>
    obtain ⟨e⟩ := iso
    rcases NativeAlternating.alternating_model_five_or_six hns hn e j hj with h|h
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
  | odd hm =>
    rcases theoremCOdd_alternating_five_or_six hns hm t ht hc j hj with h|h
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
  | bender hm =>
    rcases bender_linear_or_suzuki hm t ht hc with h|h
    · exact .inl (.inr (.inr (.inl h)))
    · exact .inl (.inr (.inr (.inr (.inl h))))
  | linear_binary n hn iso => exact (not_binary_linear_model hn j hj iso).elim
  | sporadic hm => exact (hm.not_isPGroup_centralizer t ht hc).elim
  | rank_two f hm =>
    cases hm with
    | linear hf iso => exact (not_binary_linear_three_model hf j hj iso).elim
    | symplectic hf iso => exact .inl (.inr (.inr (.inr (.inr ⟨f,hf,iso⟩))))
    | g2 hf iso => exact (not_binary_g2_model (by omega) j hj iso).elim
    | triality hf iso => exact .inr (.inl ⟨f,hf,iso⟩)
    | ree_f4 m hm _ iso => exact .inr (.inr (.inl ⟨m,hm,iso⟩))
    | symplectic_derived _ iso =>
      exact .inl (.inr (.inl (iso.map fun e => e.trans Binary.projectiveDerivedEquivAlternatingSix)))
    | g2_derived _ iso => exact (not_binary_derived_g2_model j hj iso).elim
    | tits _ iso => exact .inr (.inr (.inr iso))

/-- Restrict the ambient c₂ centralizer to the original matrix subgroup. -/
theorem subgroup_native_or_exceptional_of_one_isC2 [Finite F] {n : ℕ}
    (hF : Nat.card F=2^n) (N : Subgroup (Sp F))
    (hns : ¬Group.IsSolvable N) (hm : IsTheoremCModel N)
    (i : N) (hi : InvolutionTypes.IsC2 (i : Sp F)) :
    IsNativeDegreeFourCarrier N ∨ IsExceptionalDegreeFourCarrier N := by
  have hp := TwoConjugate.isPGroup_centralizer_of_isC2 hF (i : Sp F) hi
  have he : centralizer ({i} : Set N) =
      (centralizer ({(i : Sp F)} : Set (Sp F))).comap N.subtype := by
    ext x
    rw [mem_centralizer_singleton_iff, mem_comap,
      mem_centralizer_singleton_iff, ←Subtype.coe_inj]
    rfl
  have hpN : IsPGroup 2 (centralizer ({i} : Set N)) := by
    rw [he]
    exact hp.comap_subtype
  exact native_or_exceptional_of_theoremC hns hm i
    ((orderOf_coe i).symm.trans hi.1) hpN N.subtype N.subtype_injective
end CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
