module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSource
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Perfectness
public import Theory.GroupTheory.CoveringComparisonKernelCard
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.UnitaryFourCover
/-!
# The original PSU₅(4) central-quotient case

The comparison from the universal PSU5 cover to the natural SU5 cover has
two-group kernel by the completed odd-primary calculations. The original
source group's trivial two-core makes this comparison descend to a covering
SU5 → G. The natural scalar kernel has prime order five, and the nontrivial
source center forces that covering to be injective. Thus G is the actual
special-unitary model, already excluded by its involution-centralizer rank.

Source: Aschbacher--Smith A.2.10, A.2.18 and I.1.4(4), printed pp.35, 40, 408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S]
  [IsQuasisimple G] {K : GroupClass.{u}} {p : ℕ}

/-- The actual nontrivial odd central cover of PSU5(4) is the excluded SU5(4) model. -/
theorem caseII_unitary_five_four_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : ClassicalGroup.IsPSU (G ⧸ center G) 5 4) : False := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := iso
  have hcard' : Nat.card F = 16 := by simpa using hcard
  let Q := ProjectiveSpecialUnitaryMatrixGroup J
  let g := centralQuotientCover e
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : IsSimpleGroup Q := e.symm.isSimpleGroup
  let : IsQuasisimple Q := IsQuasisimple.of_surjective g.toMonoidHom g.surjective
  let : Group.IsPerfect J.specialSubgroup := fiveFour_isPerfect J hcard' hconj
  let : IsQuasisimple J.specialSubgroup := natural_isQuasisimple J
  let f := naturalCover J
  let c := universalQuasisimpleCover Q
  let a := (universalQuasisimpleCover_isUniversal Q).lift f
  have ha : f.comp a = c := (universalQuasisimpleCover_isUniversal Q).lift_fac f
  have hak : IsPGroup 2 a.toMonoidHom.ker :=
    FiveFourClosure.kernel_isTwoGroup_four J hcard' hconj (ofCovering a)
  obtain ⟨k,hk⟩ := (universalQuasisimpleCover_isUniversal Q).exists_covering_of_pGroup_kernel
    a f ha hak g.toCovering (lemma_A_2_10 h ih)
  have hf5 : Nat.card f.toMonoidHom.ker = 5 := by
    change Nat.card (Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel.project J).ker = 5
    rw [Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel.card_project_kernel J hconj hcard]
    decide
  have hg : Nat.card g.toMonoidHom.ker = Nat.card (center G) := by
    rw [centralQuotientCover_ker]
  have hn : 1 < Nat.card (center G) := by
    have hn := h.center_ne_bot ih
    have hp := Nat.card_pos (α := center G)
    by_contra hh
    exact hn ((center G).eq_bot_of_card_eq (by omega))
  have he := kernel_card_eq_mul_of_surjective_factor f.toMonoidHom g.toMonoidHom
    k.toMonoidHom g.surjective k.surjective (congrArg Covering.toMonoidHom hk)
  rw [hf5,hg] at he
  have hd : Nat.card (center G) ∣ 5 := by rw [he]; exact dvd_mul_left _ _
  have hz : Nat.card (center G) = 5 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with hz | hz
    · omega
    · exact hz
  rw [hz] at he
  have hki : Function.Injective k.toMonoidHom := k.toMonoidHom.ker_eq_bot_iff.mp
    (k.toMonoidHom.ker.eq_bot_of_card_eq (by omega))
  let ek : J.specialSubgroup ≃* G := MulEquiv.ofBijective k.toMonoidHom ⟨hki,k.surjective⟩
  exact caseII_special_unitary_five h (by decide : 0 < 2)
    ⟨F,hF,hfin,J,by simpa using hcard',by simpa using hconj,⟨ek.symm⟩⟩

end CFSG.Quasithin.ChapterA.Section02.EvenLie
