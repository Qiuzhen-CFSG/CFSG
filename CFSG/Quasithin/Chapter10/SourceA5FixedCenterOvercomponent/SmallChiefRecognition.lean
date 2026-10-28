module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.HeadAction
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.JankoOneExclusion
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Covers
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion

/-!
# Small chief actions and the literal A₅ embedding shortlist

The marked involution excludes the prime and order-twenty-five PSL₂ rows;
the cubic source theorem excludes J₁. These exclusions use the equivalence
of simple central quotients, so they preserve every central kernel between
the original head and the faithful actor. The surviving head is A₇ or its
triple cover. The faithful actor itself is A₇, since the genuine triple cover
has no faithful irreducible binary action of cubic ratio at most two.

The local embedding shortlist is an explicit input. In particular its
`IsAlternatingCover` row means a triple cover; this theorem does not infer
that the original head is centerless from its trivial two-core.
Source: Aschbacher–Smith 10.2.1, p.743, with A.3.14, B.4.5 and K.1/K.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {H A V : Type*} [Group H] [Finite H] [IsQuasisimple H]
  [Group A] [Finite A] [IsQuasisimple A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private def fittingEquiv : generalizedFitting A ≃* A :=
  (MulEquiv.subgroupCongr generalizedFitting_eq_top_of_quasisimple).trans topEquiv

private def fittingCentralEquiv :
    (generalizedFitting A ⧸ center (generalizedFitting A)) ≃* (A ⧸ center A) := by
  let : IsQuasisimple (generalizedFitting A) :=
    generalizedFitting_isQuasisimple_of_quasisimple
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  let d := fittingEquiv (A := A)
  exact IsQuasisimple.centralQuotientEquiv d.toMonoidHom d.surjective

omit [Finite H] in
private def simpleCentralEquiv [IsSimpleGroup H] : (H ⧸ center H) ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq center_eq_bot_of_simple_perfect).trans
    QuotientGroup.quotientBot

omit [Finite H] [Group A] [Finite A] [IsQuasisimple A] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] in
private theorem pslTwo_central_model {q : ℕ} (hq : 4 ≤ q)
    (hm : ClassicalGroup.IsPSL H 2 q) : ClassicalGroup.IsPSL (H ⧸ center H) 2 q := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    (by simpa only [hF] using hq)
  let : IsSimpleGroup H := e.isSimpleGroup
  exact ⟨F,inferInstance,inferInstance,hF,⟨simpleCentralEquiv.trans e⟩⟩

omit [Finite H] in
/-- The nonalternating rows are excluded on the actual faithful actor, retaining
only an equivalence of simple central quotients with the original head. -/
theorem head_seven_or_three_cover_of_small_chief
    (ρ : Representation (ZMod 2) A V)
    (h : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting A))
    (t : A) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2)
    (ec : (H ⧸ center H) ≃* (A ⧸ center A))
    (hlist : IsAlternating H 7 ∨ IsAlternatingCover H 7 ∨
      Nonempty (H ≃* Janko1.Model) ∨ ClassicalGroup.IsPSL H 2 25 ∨
      ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL H 2 p) :
    IsAlternating H 7 ∨ IsAlternatingCover H 7 := by
  let d := (fittingCentralEquiv (A := A)).trans ec.symm
  rcases hlist with h7 | h37 | hJ | h25 | ⟨p,hp,hm⟩
  · exact Or.inl h7
  · exact Or.inr h37
  · exfalso
    obtain ⟨eJ⟩ := hJ
    let : IsSimpleGroup H := eJ.isSimpleGroup
    let hJ : ChapterK.SporadicCatalogue.SourceHypotheses ρ := {
      sqtk := h.sqtk, quasisimple := h.quasisimple, faithful := h.faithful,
      irreducible := h.irreducible, cubic_le_two := h.smallCubic }
    exact ChapterK.SporadicCatalogue.sourceExclusion_j1 ρ hJ
      ⟨d.trans (simpleCentralEquiv.trans eJ)⟩
  · exfalso
    exact ChapterB.SmallRatioClassification.pslTwo_twentyFive_excluded_of_small_involution
      h ((pslTwo_central_model (by decide) h25).of_mulEquiv d) t ht hr
  · exfalso
    have hp4 : 4 ≤ p := by
      have hp2 := hp.1.two_le
      have hpne2 : p ≠ 2 := by intro he; subst p; norm_num [A312ExceptionalPrime] at hp
      have hpne3 : p ≠ 3 := by intro he; subst p; norm_num [A312ExceptionalPrime] at hp
      omega
    have hmodel : ClassicalGroup.IsPSL
        (generalizedFitting A ⧸ center (generalizedFitting A)) 2 (p ^ 1) := by
      simpa only [pow_one] using (pslTwo_central_model hp4 hm).of_mulEquiv d
    rcases ChapterB.SmallRatioClassification.odd_pslTwo_parameters_of_small_involution
      h t ht hr hp.1 hp.2.1 (Or.inl rfl) (by simpa only [pow_one] using hp4) hmodel
      with h5 | h7 | h3
    · have he := hp.2.2.1
      norm_num [h5.1] at he
    · have he := hp.2.2.1
      norm_num [h7.1] at he
    · omega

/-- A faithful small chief actor with simple central quotient A₇ is A₇ itself.
This assertion concerns the faithful actor, not a group mapping centrally onto it. -/
theorem actor_seven_of_small_chief_central_quotient
    (ρ : Representation (ZMod 2) A V)
    (h : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting A))
    (e : (A ⧸ center A) ≃* alternatingGroup (Fin 7)) :
    Nonempty (A ≃* alternatingGroup (Fin 7)) := by
  let : IsQuasisimple (generalizedFitting A) := h.quasisimple
  let eF := (fittingCentralEquiv (A := A)).trans e
  rcases ChapterK.Alternating.seven_cover_alternatives ρ (generalizedFitting A)
      h.faithful h.irreducible eF with ha7 | ha37
  · obtain ⟨e7⟩ := ha7
    exact ⟨(fittingEquiv (A := A)).symm.trans e7⟩
  · obtain ⟨_,⟨e37⟩⟩ := ha37
    exfalso
    let ha : ChapterK.Alternating.Input ρ KnownSimple.IsKnownSimple (generalizedFitting A) := {
      sqtk := h.sqtk, fitting := rfl, quasisimple := h.quasisimple,
      faithful := h.faithful, irreducible := h.irreducible,
      cubic_bound := h.smallCubic, quotient := Or.inr ⟨eF⟩ }
    exact ChapterK.Alternating.tripleSevenExclusion ρ KnownSimple.IsKnownSimple
      (generalizedFitting A) ha e37

omit [Finite H] in
/-- The literal shortlist determines the faithful actor and leaves exactly the
possible central triple cover in the original head. -/
theorem head_and_actor_seven_of_small_chief
    (ρ : Representation (ZMod 2) A V)
    (h : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting A))
    (t : A) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2)
    (ec : (H ⧸ center H) ≃* (A ⧸ center A))
    (hlist : IsAlternating H 7 ∨ IsAlternatingCover H 7 ∨
      Nonempty (H ≃* Janko1.Model) ∨ ClassicalGroup.IsPSL H 2 25 ∨
      ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL H 2 p) :
    (IsAlternating H 7 ∨ IsAlternatingCover H 7) ∧
      Nonempty (A ≃* alternatingGroup (Fin 7)) := by
  have hh := head_seven_or_three_cover_of_small_chief ρ h t ht hr ec hlist
  refine ⟨hh,?_⟩
  rcases hh with h7 | h37
  · obtain ⟨e7⟩ := h7
    let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup H := e7.isSimpleGroup
    exact actor_seven_of_small_chief_central_quotient ρ h
      (ec.symm.trans (simpleCentralEquiv.trans e7))
  · exact actor_seven_of_small_chief_central_quotient ρ h (ec.symm.trans h37.2.2.some)

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
