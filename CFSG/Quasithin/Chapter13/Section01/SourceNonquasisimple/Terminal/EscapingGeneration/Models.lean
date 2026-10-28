module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Refinement.Source
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.BinaryExtension
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.BinaryUpper
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.SolvableKernel
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCoreSupplement
public import Theory.GroupTheory.GeneralizedFitting.RadicalTwoExtension
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement

/-!
# The five small source quotients and E-generation

For a normal factor B supplemented by a Sylow two-subgroup, its image
modulo the ambient two-core is the generalized Fitting subgroup and is
literally isomorphic to B/O₂(B). Of the five alternatives in 13.1.2(3),
all except A₅ give E-generation at one by the proved binary model theorems.
For the central cover of A₆, quotienting by the solvable radical gives the
actual A₆ socle; generation then lifts through the solvable kernel.

The earlier five-model classification itself remains with qt-d-1317-source
and its Chapter12 producers. No numerical generation bound is used to
infer attainment.

Source: Aschbacher--Smith 13.1.2(3), printed p.866, and the first paragraph
of the terminal proof of 13.1.7 on p.876, using E.1.13--14 on p.214.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal
open ChapterE Supplements.Escape
variable {G : Type*} [Group G] [Finite G]

private theorem generated_of_six (e : generalizedFitting G ≃* alternatingGroup (Fin 6))
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    IsEGenerated 1 G := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (generalizedFitting G) := e.isSimpleGroup
  exact ValuesEvenClassical.RankTwoUpper.SymplecticFour.isEGenerated_binary_extension
    (by simp : Nat.card (ZMod 2) = 2)
    (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm) T hgen

private theorem generated_of_six_cover (B : Subgroup G) [B.Normal] [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* alternatingGroup (Fin 6))
    (hq : IsPGroup 2 (G ⧸ B)) : IsEGenerated 1 G := by
  let : Group.IsSolvable (center B) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hr : solvableRadical B = center B := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical (center B) inferInstance inferInstance)
  let er : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hr).trans e
  let : IsSimpleGroup (B ⧸ solvableRadical B) := er.isSimpleGroup
  let : Group.IsPerfect (B ⧸ solvableRadical B) := inferInstance
  have ha : ¬ IsMulCommutative (B ⧸ solvableRadical B) :=
    Group.IsPerfect.not_isMulCommutative _
  let E := (radicalTwoExtensionFittingEquiv B ha hq).trans er
  let S : Sylow 2 (G ⧸ solvableRadical G) := Classical.choice inferInstance
  exact IsEGenerated.of_solvableRadical_quotient (by decide)
    (generated_of_six E S (radicalTwoExtension_fitting_sup_sylow B ha hq S))

private theorem generated_of_linearThree {K : GroupClass} (hG : IsSQTK K G)
    (hm : ClassicalGroup.IsPSL (generalizedFitting G) 3 2)
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    IsEGenerated 1 G := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (generalizedFitting G) := e.isSimpleGroup
  exact ValuesEvenClassical.RankTwoUpper.LinearThree.isEGenerated_of_source
    hG e T (by decide : 0 < 1) (by simpa using hF) hgen

/-- The four non-A₅ alternatives give actual E₁-generation of a two-extension. -/
theorem fiveQuotients_generation {K : GroupClass} (hG : IsSQTK K G)
    [IsQuasisimple (generalizedFitting G)]
    (hm : FiveQuotients (generalizedFitting G))
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    Nonempty (generalizedFitting G ≃* alternatingGroup (Fin 5)) ∨ IsEGenerated 1 G := by
  rcases hm with h5 | h3 | h6 | hc6 | hg
  · exact Or.inl h5
  · exact Or.inr (generated_of_linearThree hG h3 T hgen)
  · exact Or.inr (generated_of_six (Classical.choice h6) T hgen)
  · right
    have hq : IsPGroup 2 (G ⧸ generalizedFitting G) :=
      isPGroup_quotient_of_sup_eq_top (G := G) (p := 2)
        (generalizedFitting G) (T : Subgroup G) T.isPGroup' hgen
    obtain ⟨e⟩ := hc6.2.2
    exact generated_of_six_cover (G := G) (generalizedFitting G) e hq
  · exact Or.inr (ExceptionalValues.G2.isEGenerated_one_of_binary_socle
      (by simp : Nat.card (ZMod 2) = 2) (generalizedFitting G) T
      (Classical.choice hg) hgen)

/-- Transport the literal five-model list, including the central quotient. -/
theorem fiveQuotients_of_equiv {Q R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (h : FiveQuotients R) : FiveQuotients Q := by
  rcases h with h5 | h3 | h6 | hc6 | hg
  · obtain ⟨a⟩ := h5
    exact Or.inl ⟨e.trans a⟩
  · obtain ⟨F,_,_,hF,⟨a⟩⟩ := h3
    exact Or.inr (Or.inl ⟨F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩)
  · obtain ⟨a⟩ := h6
    exact Or.inr (Or.inr (Or.inl ⟨e.trans a⟩))
  · obtain ⟨hq,hcard,⟨a⟩⟩ := hc6
    let := hq
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨IsQuasisimple.of_mulEquiv e.symm,?_,?_⟩)))
    · exact (Nat.card_congr (centerCongr e).toEquiv).trans hcard
    · refine ⟨(QuotientGroup.congr _ _ e ?_).trans a⟩
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro y hy
        exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩
  · obtain ⟨a⟩ := hg
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans a⟩)))

/-- Apply the five-model sieve to the literal quotient of a normal factor. -/
theorem a5_or_generation_of_fiveQuotients {K : GroupClass} (hG : IsSQTK K G)
    (B : Subgroup G) [B.Normal] [IsQuasisimple (B ⧸ pCore 2 B)]
    (hm : FiveQuotients (B ⧸ pCore 2 B))
    (T : Sylow 2 G) (hgen : B ⊔ (T : Subgroup G) = ⊤) :
    Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) ∨ IsEGenerated 1 G := by
  let Q := G ⧸ pCore 2 G
  let q : G →* Q := QuotientGroup.mk' (pCore 2 G)
  have hF := generalizedFitting_coreQuotient_eq_of_two_supplement B T T.isPGroup' hgen
  let E : generalizedFitting Q ≃* B ⧸ pCore 2 B :=
    (MulEquiv.subgroupCongr hF).trans (coreQuotientEquivImage 2 B).symm
  let : IsQuasisimple (generalizedFitting Q) := IsQuasisimple.of_mulEquiv E.symm
  have hQ : IsSQTK K Q := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let S : Sylow 2 Q := T.mapSurjective (QuotientGroup.mk'_surjective _)
  have hFS : generalizedFitting Q ⊔ (S : Subgroup Q) = ⊤ := by
    rw [hF]
    change B.map q ⊔ (T : Subgroup G).map q = ⊤
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  rcases fiveQuotients_generation hQ (fiveQuotients_of_equiv E hm) S hFS with he | he
  · obtain ⟨e⟩ := he
    exact Or.inl ⟨E.symm.trans e⟩
  · exact Or.inr (IsEGenerated.of_normal_two_subgroup (pCore 2 G) pCore_isPGroup he)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal
