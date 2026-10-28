module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.ChiefActions
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Cubic
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Five
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.FiveResidual
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.FiveBorel
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallCoreAction
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefDisplacement
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefG2Exclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefShortExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Quintic
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Track
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.KernelGeometry
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.CenteredElementary

/-!
# Two-chief exclusions for the small cubic and Omega actions

Both distinct faithful chief planes force the elementary H-orbit span to
have order at least sixteen. The cubic first factor gives an actual
exceptional marked amalgam. H contains a central involution, so the model
bound forces its normal elementary orbit span to have order at most eight.
This excludes the single S₃ quotient for the marked cubic action and all
Omega rows, including proper supports and extraspecial residuals.

The actual H-star consumers now reduce these rows to S₃ wr C₂ or S₅.
The two faithful S₅ chief factors also exclude the concrete mixed Borel
models at H ∩ M. Under any prescribed S₅ marking, that overlap maps to
S₄ and its residual intersection to A₄. The actual graph has degrees
(3 or 5, 5), with quintic radius-one kernel equal to the embedded O₂(H).
Both natural chief actions use this same quotient map and graph kernel.
The SQTK equalities make the core move the whole elementary span, despite
its trivial action on each chief factor. The whole-span centralizer is
strictly smaller than O₂(H), and the span is properly contained in that
nonabelian core. In the S₅ branch this strengthens the core and actual
radius-one graph-kernel lower bound to 512.
Both original natural S₅ factors remain faithful
noncentral chief factors after intersection with O²(H), with their actual
A₅ actions and intrinsic core kernels. Their disjoint intervals give
order at least 256 for U_H ∩ O²(H) and for the core of the embedded
rank-one factor. Both factors also contribute to its actual core commutator
layer, excluding the natural L₂(4) and A₅ block alternatives. The original
elementary span also excludes the first G₂ local and its central two-covers
at that same embedded residual. Moreover, both intervals remain moved by
the residual, which excludes every short structure on it, including the
orthogonal block rows with a possible central fixed layer. The marked-five S₃ pair has full overlap T, and its
centered H endpoint excludes the concrete Ree and Tits cubic endpoints.
The literal YT has index five, centralizes V precisely through O₂(YT), and
supplies the F.7 graph with the original seed V and an odd track at least three.
Its full H-span lies in the cubic radius-two kernel and its nontrivial
central seed survives in the radius-four kernel. Odd parity supplies a
literal conjugate in T escaping O₂(H), with conjugator in ⟨YT,H⟩.
The S₅ exclusions, marked-five S₃ exclusion, and marked-five wreath
exclusion remain with qt-e-152-small-parabolic. No quintic recognition
conclusion is assumed here. SmallSourcePrior retains only the earlier
source assumptions permitted by the original family contract.

Source: Aschbacher--Smith 15.1.12 and 15.2.6--8, pp.1090,1109--1110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- Two distinct faithful chief planes exclude the single S₃ quotient when
15.2.6 supplies a cubic first factor. Both factors are used through the
order-sixteen lower bound on the literal elementary orbit span. -/
theorem SmallResidualWitness.not_symmetricThree_of_cubic
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hfirst : Nonempty (((Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
      pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) := by
  intro he
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  let : U.Normal := normal_subgroupOf_of_le_normalizer (conjugateSpan_normalized H V)
  have hb := ChapterF.SourceAssembly.exceptional_centered_normal_elementary_card_le_eight
    (hw.cubic_symmetricThree_amalgam hH he hfirst) (h.HStar_central_involution hH) U
  rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv] at hb
  have hl := h.symmetricThree_span_card hprior hH he
  omega

/-- The marked cubic row discharges the S₃ exclusion in original 15.2.8. -/
theorem ChosenSmallSource.HStar_not_symmetricThree_of_marked_cubic
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 3 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :=
  (h.smallResidualWitness_of_marked_cubic hd).1.not_symmetricThree_of_cubic hprior hH
    (h.marked_cubic_residual_selection hd).2.2.1

/-- Every Omega support discharges the S₃ exclusion, with its actual selected
subgroup Y₁ and the maximal-overgroup comparison proved. -/
theorem ChosenSmallSource.HStar_not_symmetricThree_of_omega
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨Y₁,hle,hp,hne,hn,hm,hcentral,hquot⟩ := h.omega_rank_one_selection ho
  have hw := (h.smallResidualWitness_of_moved_selection (h.maximal_overgroups_of_omega ho)
    hle hp hne hn hm (Or.inl hquot) hcentral).1
  exact hw.not_symmetricThree_of_cubic hprior hH hquot

/-- In the marked cubic row only the single S₅ exclusion remains before the
actual S₃-wreath quotient. Its quintic recognition stays with the source owner. -/
theorem ChosenSmallSource.HStar_quotient_cubic_reduced
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 3 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) :=
  (h.HStar_quotient_of_marked_cubic hd hH).resolve_left
    (h.HStar_not_symmetricThree_of_marked_cubic hprior hd hH)

/-- The same two remaining alternatives for all Omega rows, including proper
chosen supports and extraspecial residuals. -/
theorem ChosenSmallSource.HStar_quotient_omega_reduced
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) :=
  (h.HStar_quotient_of_source_omega ho hH).resolve_left
    (h.HStar_not_symmetricThree_of_omega hprior ho hH)

end CFSG.Quasithin.Chapter15.Section02
