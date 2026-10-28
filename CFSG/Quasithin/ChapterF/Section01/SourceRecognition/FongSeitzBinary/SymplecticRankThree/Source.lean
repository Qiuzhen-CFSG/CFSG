module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.CosetAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal

/-!
# Original and geometric C₂ incidence applications

The original F.1.1 endpoint markings supply local characteristic two and
hence faithful coset actions on the same finite quotient. The elementary
Higman construction applies to its actual orbital action and actual canonical
root U₂^{s₁}. The source orbit counts and fixation of the closed neighbor orbit
remain explicit, and no projective reconstruction or model map is assumed.

The full-group normal-subgroup argument combines four equal root orders
with normal generation of the same U. Its hypotheses do not require both
original factors to be perfect, so they preserve the binary branch.

The independently marked numerator may be an infinite universal completion;
no map down to the separately generated original source group is asserted.
Both original and geometric endpoint markings use this interface.

Source: Fong–Seitz I (6A)(a), pp.36–38; II (7C), p.193 and (8A), p.197;
Higman (1964), Theorem 2(i); Aschbacher–Smith F.1.1, pp.259–260.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.GroupAction.SymplecticRankThree
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

include e

/-- F.1.1 gives faithful coset actions through the same original/geometric
endpoint marking, without requiring either factor to be perfect. -/
theorem marked_coset_faithful (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2) :
    FaithfulSMul (X ⧸ Q.D) (C2RankThree.Points Q i) :=
  C2RankThree.faithful Q split i (MarkedLocal.parabolic_core_selfCentralizing Q e h i)

/-- The same marked quotient supplies the incidence geometry in condition (i).
The remaining explicit hypotheses are literal source orbit counts and root
fixation, not projective reconstruction or a model-group homomorphism. -/
theorem marked_condition_i_lines (h : HypothesisF11 L S) (split : SplitData Q.tits)
    {q : ℕ} (hq : 2 ≤ q)
    (b c : C2RankThree.Points Q 1) (hab : C2RankThree.rightCosetPoint Q 1 1 ≠ b)
    (t : X ⧸ Q.D) (hta : t • C2RankThree.rightCosetPoint Q 1 1 = b)
    (htb : t • b = C2RankThree.rightCosetPoint Q 1 1)
    (hcov : MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1)) c =
      (insert (C2RankThree.rightCosetPoint Q 1 1)
        (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1)) b))ᶜ)
    (hdegree : Nat.card (C2RankThree.Points Q 1) = q^3+q^2+q+1)
    (hsubdegree : Nat.card
      (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1)) b) = q*(q+1))
    (hq1 : Nat.card (simpleRoot Q split 1) = q)
    (hfix : ∀ u ∈ C2RankThree.kernelRoot Q split,
      ∀ c ∈ insert (C2RankThree.rightCosetPoint Q 1 1)
        (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1)) b), u • c = c) :
    ∃ D : PolarityDesign (C2RankThree.Points Q 1) q,
      (∀ x y, D.incident x y ↔ y = x ∨
        (MulAction.SwappedOrbital.graph (C2RankThree.rightCosetPoint Q 1 1) b hab t hta htb).Adj x y) ∧
      D.block (C2RankThree.rightCosetPoint Q 1 1) = insert (C2RankThree.rightCosetPoint Q 1 1)
        (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1)) b) ∧
      (∀ x y, x ≠ y → (D.line x y).ncard = q+1) :=
  C2RankThree.rank_three_lines_of_root_fixes Q split hq
    (MarkedLocal.parabolic_core_selfCentralizing Q e h 1)
    b c hab t hta htb hcov hdegree hsubdegree hq1 hfix

omit e in
/-- The source's full normal generation upgrades the recognized normal
subgroup to the whole quotient as soon as its full q⁴ subgroup is available.
No unknown-group simplicity and no derived-group replacement is used. -/
theorem marked_normal_eq_top (split : SplitData Q.tits) {q : ℕ}
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q)
    (hgen : split.unipotentClosure = ⊤)
    (K V : Subgroup (X ⧸ Q.D)) [K.Normal] (hVK : V ≤ K) (hV : Nat.card V = q^4) : K = ⊤ :=
  C2RankThree.normal_eq_top_of_full_order_subgroup Q split hgen K V hVK
    (hV.trans (C2RankThree.unipotent_card Q split hm hq0 hq1).symm)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
