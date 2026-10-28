module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiLocal
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms

/-!
# Suzuki panel regularity, including parameter zero

The actual matrix group Sz(2) is centerless and every automorphism is
inner. Its outer index is therefore one. The original-factor odd-outer
criterion proves the same (2B) containment as at positive parameters,
using the unchanged factor embedding and full Borel. The root order is
already the order of the original quotient Sylow, including m = 0.
The pullback is the original parabolic two-core, not the whole panel
kernel. No original perfectness is assumed.

Source: Fong--Seitz I (2B), pp.7--9; AS F.1.1--3, pp.259--260.
The concrete Sz(2) automorphism calculation is the checked five-by-four
model in Theory.SpecificGroups.Suzuki.SmallAutomorphisms. Local cover
recognition is supplied by SuzukiAllLocalIdentification; global row
selection and marked rank-two recognition remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)]
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)

include e h hT in
/-- Parameter zero satisfies (2B), using its actual centerless complete group. -/
theorem suzuki_zero_remainder_le_kernel
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  apply remainder_le_kernel_of_factor_odd_outer Q e h split i T hT
  · apply eq_bot_iff.mpr
    intro z hz
    have hz' := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center (SuzukiMatrixGroup 0) at hz'
    rw [suzukiZero_center_eq_bot, mem_bot] at hz'
    exact μ.injective (hz'.trans μ.map_one.symm)
  · change Odd (Nat.card (MulAut.Outer ((L i) ⧸ pCore 2 (L i))))
    rw [Nat.card_congr (MulAut.outerCongr μ).toEquiv]
    change Odd (MulAut.conj : SuzukiMatrixGroup 0 →* MulAut (SuzukiMatrixGroup 0)).range.index
    have hs : Function.Surjective (MulAut.conj : SuzukiMatrixGroup 0 →* MulAut (SuzukiMatrixGroup 0)) := by
      intro a
      obtain ⟨g,hg⟩ := suzukiZero_automorphism_inner a
      exact ⟨g,hg.symm⟩
    rw [MonoidHom.range_eq_top.mpr hs, index_top]
    decide
  · exact suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT μ

include e h hT in
/-- All Suzuki parameters, without original-factor perfectness. -/
theorem suzuki_remainder_le_kernel_all {m : ℕ}
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  cases m with
  | zero => exact suzuki_zero_remainder_le_kernel Q e h split i T hT μ
  | succ m => exact suzuki_remainder_le_kernel Q e h split i T hT (Nat.succ_pos m) μ

include e h hT in
/-- The SAME endpoint map identifies the remainder with the original two-core. -/
theorem suzuki_remainder_comap_all {m : ℕ}
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i) :=
  remainder_comap_of_containment Q e split i
    (suzuki_remainder_le_kernel_all Q e h split i T hT μ)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
