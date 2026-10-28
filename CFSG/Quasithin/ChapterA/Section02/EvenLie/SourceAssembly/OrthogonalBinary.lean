module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.OrthogonalSimple
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.RankTwoCovers
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.OrthogonalSections.Source.BinaryD4
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.OrthogonalSections.Source.Minus
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison
public import Theory.SpecificGroups.ClassicalOrthogonal.PlusFieldTransport

/-!
# The binary orthogonal source branches and full plus-type Case I

The actual coefficient-field equivalences place arbitrary field-two model
witnesses on the literal binary carriers. Their proper parabolic sections
bound plus rank by four and minus rank by three; the independent-inverter
D4 lift lowers the plus bound to three even through the original odd center.
The remaining plus group is the genuine A8 carrier via its deleted action.
This proves full plus-type Case I and binary plus Case II. The rank-two minus
alias is the exact quadratic-extension PSL2 model, also in Case II.
Source: Aschbacher--Smith A.2.18, printed p.40; GLS3 §2.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G]

private theorem binary_field_charTwo {F : Type} [Field F] [Finite F]
    (hc : Nat.card F = 2) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ 1 by simpa only [Nat.card_eq_fintype_card, pow_one] using hc)

/-- The exact binary plus model, transporting its original coefficient field. -/
theorem binary_plus_equiv {r : ℕ} (iso : ClassicalGroup.IsPOmegaPlus G r 2) :
    Nonempty (G ≃* ClassicalOrthogonal.POmegaPlus r (ZMod 2)) := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  let : CharP F 2 := binary_field_charTwo hc
  exact ⟨e.trans (ClassicalOrthogonal.PlusFieldTransport.projectiveEquiv
    (Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo F hc) r)⟩

/-- The exact binary minus model, transporting its independently chosen anisotropic plane. -/
theorem binary_minus_equiv {r : ℕ} (iso : ClassicalGroup.IsPOmegaMinus G r 2) :
    Nonempty (G ≃* ClassicalGroup.POmegaMinus r (ZMod 2)) := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  let : CharP F 2 := binary_field_charTwo hc
  exact ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison.minusProjectiveFieldEquiv
    (Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo F hc) r)⟩

/-- The perfect nontrivial binary rank-three plus carrier is literally A8. -/
theorem binary_plus_three_alternating [Group.IsPerfect G] [Nontrivial G]
    (iso : ClassicalGroup.IsPOmegaPlus G 3 2) :
    Nonempty (G ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := binary_plus_equiv iso
  let : Group.IsPerfect (ClassicalOrthogonal.POmegaPlus 3 (ZMod 2)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Nontrivial (ClassicalOrthogonal.POmegaPlus 3 (ZMod 2)) := e.injective.nontrivial
  exact ⟨e.trans ClassicalOrthogonal.BinaryD3Comparison.projectiveEquivAlternating⟩

/-- The rank-two minus alias retains its actual quadratic-extension field. -/
theorem orthogonalMinus_two_linear {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPOmegaMinus G 2 (2 ^ a)) :
    ClassicalGroup.IsPSL G 2 (2 ^ (2 * a)) := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  exact ⟨GaloisField 2 (2 * a), inferInstance, inferInstance,
    GaloisField.card 2 (2 * a) (by omega),
    ⟨e.trans (ClassicalOrthogonal.TheoremDRootNormalizer.minusTwoEquivPSL F ha hc)⟩⟩

variable [Finite G] {K : GroupClass.{u}}

/-- The binary plus rank bound is valid for the original group and literal central quotient. -/
theorem binary_plus_model_rank_le_three (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G) (ho : Odd (Nat.card (center G)))
    {r : ℕ} (iso : ClassicalGroup.IsPOmegaPlus (G ⧸ center G) r 2) : r ≤ 3 := by
  obtain ⟨e⟩ := binary_plus_equiv iso
  exact OrthogonalSections.binary_plus_odd_center_quotient_rank_le_three ih hG hK ho e

/-- The binary minus parabolic restriction uses the original proper-section induction. -/
theorem binary_minus_model_rank_le_three (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {r : ℕ} (iso : ClassicalGroup.IsPOmegaMinus (G ⧸ center G) r 2) : r ≤ 3 := by
  obtain ⟨e⟩ := binary_minus_equiv iso
  exact OrthogonalSections.binary_minus_center_quotient_rank_le_three ih hG hK e

/-- Every simple-range plus model is resolved in the original Case I, for all even fields. -/
theorem caseI_orthogonalPlus [IsSimpleGroup G] (ih : TheoremAOnProperSections K G)
    (hna : ¬ IsMulCommutative G) (hG : IsQuasithin G) (hK : IsKGroup K G)
    {r a : ℕ} (ha : 0 < a) (hp : KnownSimple.OrthogonalPlusParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPOmegaPlus G r (2 ^ a)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  by_cases ha1 : a = 1
  · have hi : ClassicalGroup.IsPOmegaPlus G r 2 := by simpa [ha1] using iso
    have hz : center G = ⊥ := by
      rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · exact (hna (center_eq_top_iff.mp ht)).elim
    let ec : (G ⧸ center G) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    have hr := binary_plus_model_rank_le_three ih hG hK
      (by simp [hz]) (hi.of_mulEquiv ec)
    have hr3 : r = 3 := by have := hp.2; omega
    subst r
    let : Group.IsPerfect G := ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (commutator G) inferInstance).resolve_left
        (fun he => hna ((commutator_eq_bot_iff G).mp he))⟩
    have hc : IsTheoremCModel G := .alternating 8 (by decide) (binary_plus_three_alternating hi)
    exact ⟨hc.toTheoremBModel, fun _ => hc⟩
  · exact (caseI_not_orthogonalPlus_nonbinary hG (by omega) hp.2 iso).elim

/-- The complete plus-type Case I contradicts the literal simultaneous minimum. -/
theorem not_minimalCounterexample_orthogonalPlus [IsSimpleGroup G]
    (h : MinimalCounterexample K G) {r a : ℕ} (ha : 0 < a)
    (hp : KnownSimple.OrthogonalPlusParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPOmegaPlus G r (2 ^ a)) : False := by
  obtain ⟨hna, hqt, hk, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_orthogonalPlus h.2.theoremA hna hqt hk ha hp iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

variable [IsQuasisimple G] {S : Type u} [Group S] [Finite S] {p : ℕ}

/-- Every binary plus central quotient is excluded in Case II without a prime-core premise. -/
theorem caseII_orthogonalPlus_binary_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {r : ℕ} (hr : 3 ≤ r) (iso : ClassicalGroup.IsPOmegaPlus (G ⧸ center G) r 2) : False := by
  have hb := binary_plus_model_rank_le_three ih h.1 h.2.1 (center_odd_of_source h ih) iso
  have he : r = 3 := by omega
  subst r
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  obtain ⟨e⟩ := binary_plus_three_alternating iso
  exact caseII_alternating_of_source h ih (by decide : 5 ≤ 8) e

/-- The full rank-two minus central-quotient alias is already excluded by binary PSL2. -/
theorem caseII_orthogonalMinus_two_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPOmegaMinus (G ⧸ center G) 2 (2 ^ a)) : False :=
  caseII_linear_two_of_source h ih (by omega) (orthogonalMinus_two_linear ha iso)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
