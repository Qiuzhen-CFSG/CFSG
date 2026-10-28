module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.Source
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction

public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank

/-!
# The doubled-natural branch on the original moved subgroup

The coordinates on U extend to any actual moved section for the reduced
component inside its offender actor. They intertwine the original component
image with the section representation, retaining the quotient map from L.

In the doubled-natural B.5.1 row, the component's three-rank forces odd
field degree and its two-rank forces degree one. Transporting both copies
through the same field and component isomorphisms constructs a genuine
LinearThreeMarking on U. The other reducible B.5.1 rows have three-rank at
least two, so they cannot occur.

The final source consumer produces that complete marking or retains all
clauses of the irreducible row and the two product alternatives. It does
not yet complete 13.1.10. The only earlier source premise is L=[L,J(T)],
whose discharge belongs to `qt-d-1317-supplements`.
Source: Aschbacher--Smith, 13.1.10, printed pp.871--872; B.5.1 and B.5.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem movedCoordinates_reducedComponent
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (a : NormalizerReducedAction.componentImage L) (u : normalizerMoved L) :
    (movedCoordinates L ((reducedImageEquivMovedImage h hmany hL hn a :
        MulAut (normalizerMoved L)) u)).toAdd.val =
      reducedRepresentation L a (movedCoordinates L u).toAdd.val := by
  have ha : (a : NormalizerReducedAction.Star L) ∈
      (NormalizerReducedAction.componentMap L).range :=
    (NormalizerReducedAction.componentMap_range L).symm ▸ a.property
  obtain ⟨l, hl⟩ := ha
  have he : a = ⟨NormalizerReducedAction.componentMap L l,
      NormalizerReducedAction.componentMap_range L ▸ ⟨l,rfl⟩⟩ := Subtype.ext hl.symm
  rw [he, reducedImageEquivMovedImage_component]
  exact movedCoordinates_component L l u

def sectionCoordinates
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    {H : Subgroup (NormalizerReducedAction.Star L)}
    (hCH : NormalizerReducedAction.componentImage L ≤ H)
    (s : MovedSection ((reducedRepresentation L).comp H.subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf H)) :
    Additive (normalizerMoved L) ≃ₗ[ZMod 2] s.space.toSubmodule := by
  let c := (movedCoordinates L).toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let lc : Additive (normalizerMoved L) ≃ₗ[ZMod 2]
      moved (reducedRepresentation L) (NormalizerReducedAction.componentImage L) :=
    c.toLinearEquiv (fun a v => ZMod.map_smul c a v)
  have he : s.space.toSubmodule =
      moved (reducedRepresentation L) (NormalizerReducedAction.componentImage L) := by
    rw [s.space_eq, moved_comp_map, map_subgroupOf_eq_of_le hCH]
  exact lc.trans (LinearEquiv.ofEq _ _ he.symm)

omit [Finite G] in
theorem sectionCoordinates_val
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    {H : Subgroup (NormalizerReducedAction.Star L)}
    (hCH : NormalizerReducedAction.componentImage L ≤ H)
    (s : MovedSection ((reducedRepresentation L).comp H.subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf H))
    (u : Additive (normalizerMoved L)) :
    (sectionCoordinates hCH s u).val = (movedCoordinates L u.toMul).toAdd.val := by
  rfl

def componentSectionEquiv
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {H : Subgroup (NormalizerReducedAction.Star L)}
    (hCH : NormalizerReducedAction.componentImage L ≤ H)
    (s : MovedSection ((reducedRepresentation L).comp H.subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf H)) :
    ActionEquiv (componentRepresentation (L := L))
      (s.space.toRepresentation.comp
        ((NormalizerReducedAction.componentImage L).subgroupOf H).subtype) := by
  let e := reducedImageEquivMovedImage h hmany hL hn
  refine ⟨e.symm.trans (subgroupOfEquivOfLe hCH).symm, sectionCoordinates hCH s, ?_⟩
  intro a u
  apply Subtype.ext
  change (movedCoordinates L ((a : MulAut (normalizerMoved L)) u.toMul)).toAdd.val =
    reducedRepresentation L (e.symm a) (movedCoordinates L u.toMul).toAdd.val
  simpa only [e, MulEquiv.apply_symm_apply] using
    movedCoordinates_reducedComponent h hmany hL hn (e.symm a) u.toMul

private theorem linearThree_degree_one {D : Type*} [Group D] [Finite D]
    (F : BinaryField) (e : D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (hr2 : primeRank 2 D = 2) (hr3 : primeRank 3 D = 1) : F.degree = 1 := by
  have ho : Odd F.degree := by
    by_contra hn
    have hh := Theory.SpecificGroups.SignedThreeCubicRank.linear_special F.card_eq
      (Nat.not_odd_iff_even.mp hn)
    rw [primeRank_equiv 3 e] at hr3
    omega
  let ep := e.trans
    (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv F.card_eq ho)
  have hh := Matrix.PSL3Even.two_rank F.Carrier F.degree_pos F.card_eq
  rw [primeRank_equiv 2 ep] at hr2
  omega

private theorem no_large_binary_linear {D : Type*} [Group D] [Finite D]
    {d : ℕ} (hd : 4 ≤ d)
    (e : D ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2))
    (hr3 : primeRank 3 D = 1) : False := by
  have hh := Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank hd
  rw [primeRank_equiv 3 e] at hr3
  omega

/-- The doubled B.5.1 row constructs the literal two-copy marking on U. -/
def doubleThreeMarking
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (s : MovedSection
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (F : BinaryField)
    (a : ActionEquiv (s.space.toRepresentation.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))).subtype)
      (repeated (linearNatural F 3) 2)) : LinearThreeMarking T L := by
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h hmany hL hn)
  have hr : primeRank 2 ((NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L))) = 2 ∧
      primeRank 3 ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))) = 1 := by
    obtain ⟨p,hp,hp3,hm⟩ := moved_component_pslTwo h hmany hL hn
    exact prime_model_ranks hp hp3 (hm.of_mulEquiv e)
  have hF := linearThree_degree_one F a.groupEquiv hr.1 hr.2
  let c := componentSectionEquiv h hmany hL hn hj s
  let b := ExtensionConsequences.degreeOneRepeatedEquiv F hF 3 2
  let d : ActionEquiv (componentRepresentation (L := L))
      (repeated (linearNatural BinaryField.two 3) 2) := {
    groupEquiv := c.groupEquiv.trans (a.groupEquiv.trans b.groupEquiv)
    linearEquiv := c.linearEquiv.trans (a.linearEquiv.trans b.linearEquiv)
    intertwines g v := by
      change b.linearEquiv (a.linearEquiv (c.linearEquiv (componentRepresentation g v))) = _
      rw [c.intertwines, a.intertwines, b.intertwines]
      rfl }
  refine ⟨CommonMarking.of_source h hmany hL hn hmove, ?_, 2, by decide, by decide, ⟨d⟩⟩
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨d.groupEquiv.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm⟩⟩

/-- All the irreducible B.5.1 branch clauses, at an abstract section boundary. -/
def IrreducibleSectionCase {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    (s : MovedSection ρ K) : Prop :=
  IsIrrPlus ρ K s.space.toSubmodule ∧ Function.Injective s.action ∧
    IsIrreducible (s.action.comp K.subtype) ∧
    ProjectiveLine.IrreducibleActionCase s.action K (offenderSubgroup s.action) ∧
    (K = ⊤ ∨ (∀ S : Sylow 2 D, K ⊔ (S : Subgroup D) = ⊤) ∧
      OuterNaturalAction s.action)

/-- The entire original B.5.1 conclusion is retained alongside its
irreducible branch clauses. -/
def IrreducibleReducedCase (L : Subgroup G) : Prop :=
  ∃ d : ProjectiveLine.QuasisimpleSourceConclusion
    ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
    ((NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L))),
    IrreducibleSectionCase d.sectionData

/-- Expose the retained clauses without exposing the implementation of the predicate. -/
theorem irreducibleSectionCase_iff {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    (s : MovedSection ρ K) :
    IrreducibleSectionCase s ↔
      IsIrrPlus ρ K s.space.toSubmodule ∧ Function.Injective s.action ∧
        IsIrreducible (s.action.comp K.subtype) ∧
        ProjectiveLine.IrreducibleActionCase s.action K (offenderSubgroup s.action) ∧
        (K = ⊤ ∨ (∀ S : Sylow 2 D, K ⊔ (S : Subgroup D) = ⊤) ∧
          OuterNaturalAction s.action) := Iff.rfl

omit [Finite G] in
/-- The irreducible alternative retains the original source section and its clauses. -/
theorem irreducibleReducedCase_iff (L : Subgroup G) :
    IrreducibleReducedCase L ↔
      ∃ d : ProjectiveLine.QuasisimpleSourceConclusion
        ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
        ((NormalizerReducedAction.componentImage L).subgroupOf
          (offenderSubgroup (reducedRepresentation L))),
        IrreducibleSectionCase d.sectionData := Iff.rfl

/-- Only the irreducible row remains after constructing the doubled marking. -/
theorem quasisimple_marked_or_irreducible
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : ProjectiveLine.QuasisimpleSourceConclusion
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L)))) :
    Nonempty (LinearThreeMarking T L) ∨ IrreducibleReducedCase L := by
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h hmany hL hn)
  obtain ⟨p,hp,hp3,hm⟩ := moved_component_pslTwo h hmany hL hn
  have hr3 := (prime_model_ranks hp hp3 (hm.of_mulEquiv e)).2
  cases d.clause_one with
  | irreducible hi hf hir hs he =>
    exact Or.inr ⟨d,hi,hf,hir,hs,he⟩
  | doubleThree F hw a ho hq =>
    exact Or.inl ⟨doubleThreeMarking h hmany hL hn hmove d.sectionData F a⟩
  | naturalDual n hn hw a =>
    obtain ⟨a⟩ := a
    exact (no_large_binary_linear (by omega) a.groupEquiv hr3).elim
  | repeatedNatural n r hn hp hb hw a =>
    obtain ⟨a⟩ := a
    exact (no_large_binary_linear (by omega) a.groupEquiv hr3).elim

/-- Apply the preceding construction to the actual classification alternative.
The doubled-natural case is now a complete four-way output; only irreducible
and product cases remain to construct. -/
theorem reducedOffender_marked_or_remaining
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    Nonempty (FourWayMarking.{u,u} T L) ∨ IrreducibleReducedCase L ∨
      Nonempty (SourceTwoFactorCase ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype)) ∨
      Nonempty (HyperplaneCase ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype)) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).1
  rcases reducedOffender_component_cases h hmany hL hn hmove with hd | hd
  · obtain ⟨d⟩ := hd
    rcases quasisimple_marked_or_irreducible h hmany hL hn hmove d with hm | hi
    · obtain ⟨m⟩ := hm
      exact Or.inl ⟨.linearThree m⟩
    · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hd)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
