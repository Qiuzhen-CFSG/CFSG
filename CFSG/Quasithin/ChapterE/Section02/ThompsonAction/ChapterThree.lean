module

public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Solvable
public import CFSG.Quasithin.Chapter3.Section01.E23Input

/-!
# The literal Chapter 3 consumer of the first E.2.3 branches

Apply the reduced-module preliminaries to the original omega-center orbit
in the qrc configuration. In the solvable H branch, its original centralizer
quotient has exactly one or two transitive natural Thompson factors.
The source SQTK hypothesis supplies the factor bound; no quotient rank
premise or module/factor witness is passed by this consumer.

Source: Aschbacher–Smith, 3.1.7 and E.2.3, printed pp.575–576 and 216–217
(1 March 2004 manuscript). The final Baumann Sylow and A5 alternatives
remain independent E.2.3 obligations.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.e23_thompson_and_centralizer
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    let S := T.subtype h.right_mem.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    pResidual 2 H ≤ elementaryAbelianMaxJ (⊤ : Subgroup H) ∧
      (S : Subgroup H) ⊓ centralizer (U : Set H) = pCore 2 H := by
  obtain ⟨_, _, hp, hU, hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  exact ⟨(ChapterE.ThompsonAction.residual_le_thompson _ hp _ hU hj).1,
    (ChapterE.ThompsonAction.reduced_centralizer_sylow _ hp _ hU hj).1⟩

/-- The actual omega-orbit in 3.1.7 has one or two natural Thompson factors in the solvable branch. -/
theorem QrcHypotheses.e23_solvable_factors
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype)
    (hsolv : Group.IsSolvable H) :
    let S := T.subtype h.right_mem.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let hU := h.sylowOmega_reduced (hG.evenCharacteristic T)
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      (d.count = 1 ∨ d.count = 2) ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup H)).map q = offenderSubgroup ρ ∧
      (∀ i j, ∃ t : S,
        (d.factor i).map (MulAut.conj (q t)).toMonoidHom = d.factor j) := by
  obtain ⟨hsq, _, hp, hU, hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  let := hsolv
  exact ChapterE.ThompsonAction.source_solvable_factors _ hp _ hU hj
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) inferInstance

end CFSG.Quasithin.Chapter3
