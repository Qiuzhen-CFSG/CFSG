module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.LinearUnitaryPrime
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularFactorCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularUnitaryCover

/-!
# Original-factor application of the octagon separating prime

The original linear and unitary quotient maps are transported to the same
marked octagon.  The regular local cover supplies the actual projective
unitary action, so the separating-prime witness is a statement about the
literal source quotient rather than an isolated model pair.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h split in
/-- The separating prime and its unitary fixed-root action for the original
linear/unitary factors. -/
theorem original_octagon_separating_prime_unitary_fixed
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (hb : 2 ≤ b) (hlarge : 2*b < a)
    (hlinear : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = (2^b)^2)
    (hconj : ∀ x : F, J.conj x = x^(2^b))
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃*
        ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ r : ℕ, ∃ t : X ⧸ Q.D,
      r.Prime ∧ r ∣ 2^a - 1 ∧ ¬ r ∣ 2^(2*b) - 1 ∧
      t ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i ∧
      orderOf t = r ∧
      ∀ w, t ∈ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) := by
  obtain ⟨E, hEfield, hEfin, hEcard, ⟨μ⟩⟩ := hlinear
  letI : Field E := hEfield
  letI : Finite E := hEfin
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEcard)
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hKi := linear_remainder_le_kernel Q e h split i T hT μ
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
    rw [simpleRoot_card_linear Q e h split i T hT μ]
    exact ((Nat.card_congr (linearSylowEquiv i T μ).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i T μ)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μ hz
    change μ z ∈ center PSL(2,E) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact μ.injective (hh.trans μ.map_one.symm)
  let μlocal := (regularFactorLocalEquiv Q e h split i T hT hKi hc hz).trans μ
  let := h.finite_local j
  obtain ⟨Tj,hTj⟩ := h.sylow j
  rcases hfactor with ⟨⟨μj⟩⟩ | ⟨⟨μj⟩⟩
  · have hKj := specialUnitary_remainder_le_kernel Q e h split j Tj hTj J hb hcard hconj μj
    obtain ⟨ν,π,hπ,hπν⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj j hKj
      (Or.inl ⟨μj⟩)
    exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure.octagon_separating_prime_unitary_fixed
      Q split hm i j hij hKi hKj μlocal ν J hb hEcard hcard hconj hlarge
      (UnitarySource.actorReflection Q split i)
  · have hKj := projectiveUnitary_remainder_le_kernel Q e h split j Tj hTj J hb hcard hconj μj
    obtain ⟨ν,π,hπ,hπν⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj j hKj
      (Or.inr ⟨μj⟩)
    exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure.octagon_separating_prime_unitary_fixed
      Q split hm i j hij hKi hKj μlocal ν J hb hEcard hcard hconj hlarge
      (UnitarySource.actorReflection Q split i)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
