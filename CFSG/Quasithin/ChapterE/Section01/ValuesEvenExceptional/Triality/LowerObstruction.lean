module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.CoreIntersection
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.WeakClosure
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.LargeIntersection

/-!
# Triality lower-obstruction reduction

The actual cubic-root actor and its automorphism orbit supply an elementary
family in every normal triality extension. Literal E-case quotient ranks
give a large intersection with Q = O₂(K)∩L, where O₂(K) is first embedded
in G. The active source clause prevents the whole actor from lying in Q.

The theorem below isolates two geometric obligations. One puts the
weak-closure normalizer in the central parabolic overgroup. The other
controls normalizers of two-subgroups meeting an actor in more than q²
elements. Its actor-normalizer alternative contradicts the active E-case,
leaving all E_(3f-1)-members in that same proper parabolic overgroup.

These two obligations are explicit hypotheses, not proved source results.
`HeadCounterexample.head_normalizer_criterion_counterexample` refutes the
proposed universal model version of the second obligation for this literal
head family, including at f = 1. The conditional interface below is retained;
the source lower obstruction needs a different family or additional genuine
source hypotheses. The unconditional existential for E.1.14(2) is unfinished.
Source: Aschbacher--Smith E.1.2, E.1.5 and E.1.14(2), printed pp.210,214,
citing Aschbacher, GF(2)-representations of finite groups, Lemma 4.7.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G] [Finite G]

/-- Conditional assembly from the two explicit geometric inputs. In particular,
the normality used to exclude the first alternative is relative to K. -/
theorem exists_obstruction_of_head_geometry (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) {f : ℕ} {hf : 0 < f} (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf))
    (hweak : normalizer (weakClosure (T : Subgroup G) (ambientHeadFamily L e) : Set G) ≤
      parabolicOvergroup L T e .central)
    (hgeometry : ∀ A ∈ ambientHeadFamily L e, A ≤ (T : Subgroup G) →
      ∀ Q : Subgroup G, Q ≤ (T : Subgroup G) ⊓ L → IsPGroup 2 Q →
        A ≤ normalizer (Q : Set G) →
        tau (T : Subgroup G) A ≤ normalizer (Q : Set G) →
        2 ^ (2 * f) < Nat.card (Q ⊓ A : Subgroup G) → ¬ A ≤ Q →
        normalizer (Q : Set G) ≤ normalizer (A : Set G) ∨
          normalizer (Q : Set G) ≤ parabolicOvergroup L T e .central) :
    ∃ (Ω : Set (Subgroup G)) (M : Subgroup G),
      IsElementaryFamily Ω ∧ M ≠ ⊤ ∧
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M ∧
      ∀ A ∈ Ω, A ≤ (T : Subgroup G) → ∀ K,
        IsEMemberAt (3 * f - 1) (T : Subgroup G) A K → K ≤ M := by
  refine ⟨ambientHeadFamily L e, parabolicOvergroup L T e .central,
    ambientHeadFamily_elementary L e, parabolicOvergroup_ne_top L T e he .central,
    hweak, ?_⟩
  intro A hA hAT K hK
  let Q := ((pCore 2 K).map K.subtype) ⊓ L
  obtain ⟨hQT, hKN, hlarge, hnot⟩ := head_member_core_intersection L T e hA hK
  have hQtwo : IsPGroup 2 Q := (pCore_isPGroup.map K.subtype).to_inf_left
  have hτ : tau (T : Subgroup G) A ≤ normalizer (Q : Set G) :=
    (hK.1.2.2.2.1.trans inf_le_right).trans hKN
  rcases hgeometry A hA hAT Q hQT hQtwo (hK.1.2.2.1.trans hKN) hτ hlarge hnot with h | h
  · exfalso
    let _ := hK.1.1
    let _ : (A.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer (hKN.trans h)
    apply ValuesEvenClassical.Sp4Lower.member_not_le_core hK.1
    exact le_sSup ⟨inferInstance, (IsElementaryAbelian.isPGroup 2 A).comap_subtype⟩
  · exact hKN.trans h

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
