module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.OriginalCompletionAt
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalConstituentRows
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.Sections

/-!
# Original degree-four natural-module reduction at the same Sylow

The seven original chosen-module rows leave the full natural four-space
or the deleted eight-point central quotient. The latter marking transports
through the original chosen-space inclusion and its fixed-space quotient
to the precise orthogonal source hypothesis, which is impossible. The
surviving natural marking therefore uses the unchanged V, its original
conjugation action, and the literal projection L → L/O₂(L).

The existing two-row sieve is purely a consequence of the supplied seven
rows and the actual A₈ quotient; it assumes no natural-module reduction.
Source: Aschbacher--Smith 12.6.34, printed p.838.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Section02 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem orthogonal_marking_of_deleted (D : ChosenModule T L V) :
    letI := D.elementary
    letI := D.actionCentralizer_normal
    ActionEquiv D.faithfulCentralAction (alternatingNatural 8) →
      Nonempty (OrthogonalMarking L V D.normalizes) := by
  let := D.elementary
  let := D.actionCentralizer_normal
  intro a
  let E₀ : D.space ≃+ Additive V := {
    toFun w := Additive.ofMul (D.spaceEquiv (Multiplicative.ofAdd w))
    invFun v := (D.spaceEquiv.symm v.toMul).toAdd
    left_inv w := congrArg Multiplicative.toAdd
      (D.spaceEquiv.symm_apply_apply (Multiplicative.ofAdd w))
    right_inv v := congrArg Additive.ofMul (D.spaceEquiv.apply_symm_apply v.toMul)
    map_add' v w := congrArg Additive.ofMul
      (D.spaceEquiv.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  let E : D.space ≃ₗ[ZMod 2] Additive V := E₀.toLinearEquiv (ZMod.map_smul E₀)
  have hE (l : L) (w : D.space) :
      E (D.chosenAction l w) = seedRepresentation L V D.normalizes l (E w) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) : G) =
      (l : G) * (D.spaceEquiv (Multiplicative.ofAdd w) : G) * (l : G)⁻¹
    rw [D.spaceEquiv_apply,D.spaceEquiv_apply]
    rfl
  let C := (BinaryOffender.fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype
  have hC : C.map E.toLinearMap = (fixedSeed L V D.normalizes).toSubmodule := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      change ∀ l : L, seedRepresentation L V D.normalizes l (E w) = E w
      intro l
      rw [←hE]
      apply congrArg E
      apply Subtype.ext
      exact hw ((subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l)
    · intro hv
      refine ⟨E.symm v,?_,E.apply_symm_apply v⟩
      intro l
      have hl : D.chosenAction (subgroupOfEquivOfLe le_sup_left l) (E.symm v) = E.symm v := by
        apply E.injective
        rw [hE,E.apply_symm_apply]
        exact hv _
      exact congrArg Subtype.val hl
  let Q : D.chosenCentralQuotient ≃ₗ[ZMod 2] Vhat L V D.normalizes :=
    Submodule.Quotient.equiv C (fixedSeed L V D.normalizes).toSubmodule E hC
  let b := (QuotientGroup.quotientMulEquivOfEq (conjugation_ker L V D.normalizes)).trans
    a.groupEquiv
  refine ⟨⟨b,Q.symm.trans a.linearEquiv,?_⟩⟩
  intro l v
  obtain ⟨w,rfl⟩ := Q.surjective v
  induction w using Submodule.Quotient.induction_on with
  | _ w =>
    have hQ : (fixedSeed L V D.normalizes).quotientRepresentation l
        (Q (Submodule.Quotient.mk w)) =
        Q (D.chosenCentralAction l (Submodule.Quotient.mk w)) := by
      change Submodule.Quotient.mk (seedRepresentation L V D.normalizes l (E w)) =
        Submodule.Quotient.mk (E (D.chosenAction l w))
      rw [hE]
    simp only [LinearEquiv.trans_apply,hQ,Q.symm_apply_apply]
    exact a.intertwines (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l)
      (Submodule.Quotient.mk w)

/-- Source 12.6.34 on the original chosen module, using only the same-G,T
structural and module statements and their original multiple-overgroup guard. -/
theorem original_degree_four_natural_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hp : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Section09.NaturalModule D 4 := by
  let := D.elementary
  let := D.actionCentralizer_normal
  have hrows := Section09.NaturalSource.Components.chosen_eight_natural_or_deleted D
      (ChapterA.Section03.SourceEmbeddings.AlternatingEight.modelEquiv hp)
      (modules L V h D)
  change Section09.NaturalModule D 4 ∨
    Nonempty (ActionEquiv D.faithfulCentralAction (alternatingNatural 8)) at hrows
  rcases hrows with hn | ha
  · exact hn
  · obtain ⟨a⟩ := ha
    obtain ⟨m⟩ := orthogonal_marking_of_deleted D a
    let S : SourceHypothesis KnownSimple.IsKnownSimple T L V := ⟨h,D,⟨m⟩⟩
    exact (S.original_orthogonal_impossible_at m structural modules hmany).elim

end CFSG.Quasithin.Chapter12.Section06
