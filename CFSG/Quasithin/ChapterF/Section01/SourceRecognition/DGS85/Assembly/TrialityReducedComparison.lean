module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearHexagonRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityNative

/-!
# Reduced Triality comparison from the actual marked split quotient

The unequal original linear factors supply the completed Triality source
relations through the existing marked hexagon construction. This adapter
changes the intersection-overlap convention to the literal reduced amalgam
used by DGS85, and then aligns the Fin 2 endpoint orientation with the native
Bool Triality model. Both endpoint maps and the full reduced Borel remain in
the resulting isomorphism.

Source: Fong--Seitz I (6E)(b), pp.43--45; DGS Theorem D, p.224;
DGS85 (15.2), pp.226--228.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.TrialityReducedComparison
open FongSeitzBinary OriginalExtension SuzukiContainment
open Chapter6.Source.RankOneGeneric

/-- Convert the location of the larger-field arm endpoint to the native
orientation of the left endpoint. -/
def nativeOrientation (j : Fin 2) : Bool := decide (j = 1)

@[simp] theorem nativeOrientation_zero : nativeOrientation (0 : Fin 2) = false := by
  simp [nativeOrientation]

@[simp] theorem nativeOrientation_one : nativeOrientation (1 : Fin 2) = true := by
  simp [nativeOrientation]

/-- The same full Borel and both parabolics in the presentation and native
orientation conventions. -/
def flagToNative (m : ℕ) (hm : 0 < m) (j : Fin 2) :
    Iso (TrialityPresentation.flagAmalgam m hm j)
      (TrialityNative.amalgam m hm (nativeOrientation j)) := by
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => Fin.elim0 k) k) j
  all_goals
    exact
      { left := MulEquiv.refl _
        middle := MulEquiv.refl _
        right := MulEquiv.refl _
        left_commutes := fun _ => rfl
        right_commutes := fun _ => rfl }


private def intersectionToReduced {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S) :
    Iso (ofSubgroups (parabolic L (reducedSylow L S) 0)
      (parabolic L (reducedSylow L S) 0 ⊓ parabolic L (reducedSylow L S) 1)
      (parabolic L (reducedSylow L S) 1) inf_le_left inf_le_right)
      (reducedAmalgam L S) :=
  NativeRestoration.subgroupCongrIso _ _ _ _ rfl
    (lemma_F_1_3_6 (reduced_hypothesis h)) rfl

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (h : HypothesisF11 L S) (Q : MarkedQuotient P)
  (mark : Iso (reducedAmalgam L S) Q.standardAmalgam)
  (split : SplitData Q.tits) (hrot : rotationOrder Q = 6)

include h Q mark split hrot in
/-- Unequal original linear factors force the cubic degree and construct the
literal reduced native comparison, including degree one and nonperfect factors. -/
theorem reduced_comparison
    {E F : Type*} [Field E] [Finite E] [CharP E 2]
    [Field F] [Finite F] [CharP F 2]
    (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,F))
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    b = 3*a ∧ Nonempty (Iso (reducedAmalgam L S)
      (TrialityNative.amalgam a ha (nativeOrientation j))) := by
  obtain ⟨hc,⟨e⟩⟩ := LinearHexagon.marked_unequal_linear_triality Q
    ((intersectionToReduced h).trans mark) (reduced_hypothesis h) split
    hrot i j hij μi μj ha hab hE hF
  exact ⟨hc,⟨((intersectionToReduced h).symm.trans e).trans (flagToNative a ha j)⟩⟩

include h Q mark split hrot in
/-- Apply the same recognition directly to the original finite-field quotient
assertions; no local permutation marking is an additional input. -/
theorem reduced_comparison_of_factor_types
    (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hsmall : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hlarge : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    b = 3*a ∧ Nonempty (Iso (reducedAmalgam L S)
      (TrialityNative.amalgam a ha (nativeOrientation j))) := by
  obtain ⟨E,hE,hfinE,hcardE,⟨μi⟩⟩ := hsmall
  obtain ⟨F,hF,hfinF,hcardF,⟨μj⟩⟩ := hlarge
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  let : NeZero a := ⟨ha.ne'⟩
  let : NeZero b := ⟨(ha.trans hab).ne'⟩
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardE)
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardF)
  exact reduced_comparison h Q mark split hrot i j hij μi μj ha hab hcardE hcardF


end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.TrialityReducedComparison
