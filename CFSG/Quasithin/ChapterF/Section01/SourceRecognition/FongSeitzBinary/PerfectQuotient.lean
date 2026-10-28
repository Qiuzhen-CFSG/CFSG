module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UniformRoots

/-!
# Whole-quotient reduction after ordered-root generation

Both perfect original factors contain their actual canonical simple roots.
Normality puts every Weyl conjugate of these roots in O² of the same finite
quotient. If the independent ordered-root theorem generates U from those
conjugates, the established equality Y = O²(Y)U gives Y = O²(Y). The proved
perfect simple-socle theorem then makes this original quotient perfect and
simple, keeping its full B,N pair and both parabolic markings.

The displayed generation premise is deliberately explicit. Its producer is
qt-dgs85-split-root-coordinates; neither the local Cartan theorem nor the
simple-socle theorem alone discharges it. This conditional reduction does
not claim any of the seven Lie rows or a nonperfect source branch.

Source: the minimal reduction left implicit in DGS, Groups and Graphs,
Part II, pp.80–81 and Theorem D, p.224; the elementary proof uses the
canonical simple roots and their original right-conjugation convention.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (hp : ∀ i, Group.IsPerfect (L i))
  (split : SplitData Q.tits)

include e h hp in
/-- Normality transports both proved root containments to all actual Weyl conjugates. -/
theorem weyl_roots_le_twoResidual :
    (⨆ (i : Fin 2) (n : Q.tits.N),
      rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D)) ≤ pResidual 2 (X ⧸ Q.D) := by
  apply iSup_le
  intro i
  apply iSup_le
  intro n x hx
  have hroot := simpleRoot_le_twoResidual Q e h hp split i hx
  change (n : X ⧸ Q.D) * x * (n : X ⧸ Q.D)⁻¹ ∈ pResidual 2 (X ⧸ Q.D) at hroot
  have hc := (inferInstance : (pResidual 2 (X ⧸ Q.D)).Normal).conj_mem _ hroot
    (n : X ⧸ Q.D)⁻¹
  simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hc

include e h hp in
/-- Ordered-root generation is the sole additional premise in this
whole-quotient reduction. The roots and all conjugating lifts are the actual ones. -/
theorem twoResidual_eq_top_of_weyl_roots
    (hroots : split.U ≤ ⨆ (i : Fin 2) (n : Q.tits.N),
      rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D)) :
    pResidual 2 (X ⧸ Q.D) = ⊤ := by
  have hgen := factors_generate Q e h
  rw [sylow_range Q e h split, ← (perfect_residual Q e h hp split).1] at hgen
  apply top_unique
  rw [← hgen]
  exact sup_le le_rfl (hroots.trans (weyl_roots_le_twoResidual Q e h hp split))

include e h hp in
/-- The same finite quotient is perfect once its actual roots generate U. -/
theorem isPerfect_of_weyl_roots
    (hroots : split.U ≤ ⨆ (i : Fin 2) (n : Q.tits.N),
      rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D)) :
    Group.IsPerfect (X ⧸ Q.D) := by
  let := (perfect_residual Q e h hp split).2
  let f := (MulEquiv.subgroupCongr (twoResidual_eq_top_of_weyl_roots Q e h hp split hroots)).trans
    Subgroup.topEquiv
  exact Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective

include e h hp in
/-- Combine the proved simple socle and the whole-quotient reduction.
This is conditional on the independent root-generation theorem. -/
theorem isSimple_of_weyl_roots
    (hroots : split.U ≤ ⨆ (i : Fin 2) (n : Q.tits.N),
      rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D)) :
    IsSimpleGroup (X ⧸ Q.D) := by
  let := twoResidual_isSimple Q e h hp split
  let f := (MulEquiv.subgroupCongr (twoResidual_eq_top_of_weyl_roots Q e h hp split hroots)).trans
    Subgroup.topEquiv
  exact f.symm.isSimpleGroup

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The conditional reduction for the literal quotient of the original
source carrier, with the same q and both original endpoint inclusions. -/
theorem quotient_isSimple_of_weyl_roots (h : HypothesisF11 L S)
    (hp : ∀ i, Group.IsPerfect (L i)) (Q : SourceQuotient L S)
    (split : SplitData Q.tits)
    (hroots : split.U ≤ ⨆ (i : Fin 2) (n : Q.tits.N),
      rightConjugate (simpleRoot Q split i) (n : (generated L S) ⧸ Q.D)) :
    IsSimpleGroup ((generated L S) ⧸ Q.D) :=
  MarkedLocal.isSimple_of_weyl_roots Q (originalMarkedIso Q) h hp split hroots

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
