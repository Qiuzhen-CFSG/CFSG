module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineSubgroup

/-!
# The source middle-root intersections and seven-b bounds

The original factor markings supply the exact order of X, the middle
unitary root and its Frattini subgroup. Relative index counting gives
|W| <= 2^(7b) whenever W intersects that root only in its Frattini group.
This applies to every elementary abelian subgroup and to the center of X.

The actual full Cartan has only three invariant subgroups in the middle
root: 1, its Frattini subgroup and the whole root. For b=1 the already
proved cubic fixed-root identity excludes an invariant cyclic four-group.
Consequently every Cartan-invariant W in X of order greater than 2^(7b)
contains the whole middle root. All inputs are obtained from the original
PSL2 and SU3/PSU3 factors, with both orientations and the literal full-Borel
amalgam marking retained.

Source: Fong--Seitz I (6F), printed p.47, the invariant-subgroup paragraph.
The sharp projective representation bound, the proof that the candidate
proper invariant subgroup is elementary, and lower-central persistence
remain required before the terminal exclusion and seven-row assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
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
include e h split

/-- The source intersection alternatives and size bounds, with all root,
Cartan and degree-one inputs discharged from the original factors. -/
theorem original_linear_unitary_nine_subgroup_control
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    let K := unitaryNineSubgroup Q split i j
    let C := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
    let M := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
    Nat.card (center K) ≤ 2^(7*b) ∧
      (∀ W : Subgroup (X ⧸ Q.D), W ≤ K → C ⊓ W ≤ M → Nat.card W ≤ 2^(7*b)) ∧
      (∀ W : Subgroup (X ⧸ Q.D), W ≤ K → IsElementaryAbelian 2 W → Nat.card W ≤ 2^(7*b)) ∧
      (∀ W : Subgroup (X ⧸ Q.D), W ≤ C →
        Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) → W=⊥ ∨ W=M ∨ W=C) ∧
      (∀ W : Subgroup (X ⧸ Q.D), W ≤ K →
        Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) →
        2^(7*b) < Nat.card W → C ≤ W) := by
  have hfixed := (original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj).2
  obtain ⟨_,hab⟩ := original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb hi hj
  obtain ⟨E,hEfield,hEfin,hEcard,⟨ν⟩⟩ := hi
  let : Field E := hEfield
  let : Finite E := hEfin
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEcard)
  have hE2 : 2 < Nat.card E := by
    rw [hEcard,hab]
    exact (by decide : 2 < 2^2).trans_le
      (Nat.pow_le_pow_right (by decide) (show 2 ≤ 2*b by omega))
  have hregular := marked_octagon_regularity_of_linear_quotient Q e h split hE2 hm i ν
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hri : Nat.card (simpleRoot Q split i)=2^(2*b) := by
    rw [simpleRoot_card_linear Q e h split i Ti hTi ν,hEcard,hab]
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
      let K := unitaryNineSubgroup Q split i j
      let C := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
      let M := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
      Nat.card (center K) ≤ 2^(7*b) ∧
        (∀ W : Subgroup (X ⧸ Q.D), W ≤ K → C ⊓ W ≤ M → Nat.card W ≤ 2^(7*b)) ∧
        (∀ W : Subgroup (X ⧸ Q.D), W ≤ K → IsElementaryAbelian 2 W → Nat.card W ≤ 2^(7*b)) ∧
        (∀ W : Subgroup (X ⧸ Q.D), W ≤ C →
          Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) → W=⊥ ∨ W=M ∨ W=C) ∧
        (∀ W : Subgroup (X ⧸ Q.D), W ≤ K →
          Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) →
          2^(7*b) < Nat.card W → C ≤ W) := by
      obtain ⟨μ,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj
        j (hregular j).1 hmodel.symm
      have hrj : Nat.card (simpleRoot Q split j)=(2^b)^3 := by
        rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
        · exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj μ
        · exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj μ
      have hC : Nat.card (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i))=2^(3*b) := by
        rw [rootAt,card_rightConjugate,hrj,←pow_mul,Nat.mul_comm b 3]
      have hK := unitaryNineSubgroup_card Q split J hb hcard hconj hm i j hij (hregular j).1 μ hri hrj
      have hM := unitary_rootFrattini_card Q split J hb hcard hconj j (hregular j).1 μ
        (Q.simple i*Q.simple j*Q.simple i)
      have hfix := (hfixed (Q.simple i*Q.simple j*Q.simple i)).2.1.le
      exact ⟨unitaryNineSubgroup_center_card_le Q split J hb hcard hconj hm i j hij
          (hregular j).1 μ hri hrj,
        unitaryNineSubgroup_card_le_of_middle_intersection Q split i j hK hC hM,
        unitaryNineSubgroup_elementary_card_le Q split J hb hcard hconj hm i j hij
          (hregular j).1 μ hri hrj,
        unitary_rootAt_cartan_subgroup_trichotomy Q split J hb hcard hconj j (hregular j).1 μ hrj _ hfix,
        unitaryNineSubgroup_large_contains_middle_all Q split J hb hcard hconj hm i j hij
          (hregular j).1 μ hri hrj hfix⟩
  rcases hj with ⟨F,hF,hfin,J,hcard,hconj,μ⟩ | ⟨F,hF,hfin,J,hcard,hconj,μ⟩
  · exact applyModel J hcard hconj (Or.inl μ)
  · exact applyModel J hcard hconj (Or.inr μ)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
