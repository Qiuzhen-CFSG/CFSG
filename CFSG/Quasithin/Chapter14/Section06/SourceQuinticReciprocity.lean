module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCritical
public import CFSG.Quasithin.ChapterF.Section09.QuinticCoreEscape

/-!
# Reciprocal critical endpoints in the original quintic source

The original source supplies the odd critical radius at least three,
elementary closure U, and quotient H/O₂(H) equal to D₁₀ or Sz(2).
The quintic displacement argument now proves U^g is outside O₂(H) for
the same critical endpoint g. F.9.17 supplies a reverse endpoint whose
single conjugator restores every H-normalized label, including U and
O₂(H). Every geometric premise is discharged from the source hypotheses.

Source: Aschbacher--Smith14.2.21 and14.6.12(2), printed pp.988 and1031;
F.9.13--17, printed pp.322--324. This is a critical-pair input to the
remaining asymmetric marked amalgam recognition, not endpoint recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- The original quintic source has a reciprocal critical endpoint.
Its single reverse conjugator restores every original H-normalized label. -/
theorem source_quintic_critical_reciprocity
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let E : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let h : E.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
    3 ≤ h.b ∧ Odd h.b ∧
      ∃ i : h.CriticalEndpoint,
        ¬ i.conjugate E.UH ≤ E.QH ∧
        ∃ j : h.CriticalEndpoint, ∀ A : Subgroup G,
          H ≤ normalizer (A : Set G) →
          (i.conjugate A).map (MulAut.conj j.representative).toMonoidHom = A := by
  let E : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : E.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
  obtain ⟨hb,ho,⟨i⟩⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab H hH.1
  obtain ⟨he,_⟩ := Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi
  let : IsElementaryAbelian 2 E.UH := he
  have hm := Section02.SolvableAmalgam.source_index_five_models
    hG T hempty hM hu hmany hcard e H hH.1 hi
  have hn := ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint.not_le_core_of_quintic
    h hm rfl i hb
  exact ⟨hb,ho,i,hn,i.reverse_labels hb hn⟩

end CFSG.Quasithin.Chapter14.Section06
