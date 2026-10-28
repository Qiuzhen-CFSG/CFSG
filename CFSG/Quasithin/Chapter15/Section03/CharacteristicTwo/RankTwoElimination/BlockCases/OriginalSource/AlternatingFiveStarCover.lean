module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Quotients
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Alternating.Reduction

/-!
# The actual A₅ star quotient and the component core

For the literal C.2.7 map L/O₂(L) → L*, an A₅ model for L* makes the
perfect central kernel a quotient of the universal A₅ covering kernel.
That kernel has order two. The comparison kernel therefore lies in the
two-core of L/O₂(L), which is trivial, so the same A₅ model describes the
component core. No identification with the earlier plus action is used.

This supplies the quotient premise of the original 15.3.18–19 rank-one
argument for the raw symmetric-five row. Source: Aschbacher–Smith,
combined manuscript (1 March 2004), 15.3.16–19, printed pp.1126–1127,
and I.1.3, printed p.407.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G]

/-- The actual core-to-star map has trivial kernel when its target is A₅. -/
theorem coreToStar_injective_of_alternatingFive_star
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (e : starImage c.L d.R c.L ≃* alternatingGroup (Fin 5)) :
    Function.Injective (coreToStar hR) := by
  let _ : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let _ : Nontrivial (starImage c.L d.R c.L) := e.symm.injective.nontrivial
  have hne : starImage c.L d.R c.L ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  let f := coreStarCover hR c.core_quotient_quasisimple hne
  let g : PerfectCentralCovering.Cover (c.L ⧸ pCore 2 c.L)
      (alternatingGroup (Fin 5)) :=
    { toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
      surjective := e.surjective.comp f.surjective
      isPerfect := f.isPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact f.ker_le_center }
  let _ : IsQuasisimple (alternatingGroup (Fin 5)) :=
    GLS3.Chapter5.SchurPresentation.alternatingGroup_isQuasisimple 0
  let _ : IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
  have hd := GLS3.Chapter5.Covering.coveringKernel_card_dvd_of_universal
    (GLS3.Chapter5.SchurPresentation.alternatingFreeCentralCovering 0)
    (GLS3.Chapter5.SchurPresentation.alternatingFreeCentralCovering_isUniversal 0)
    g.toCovering
  rw [GLS3.Chapter5.SchurPresentation.natCard_ker_alternatingFreeCentralCovering_zero_eq_two]
    at hd
  change Nat.card g.toMonoidHom.ker ∣ 2 at hd
  have hk : IsPGroup 2 (coreToStar hR).ker := by
    have h : IsPGroup 2 g.toMonoidHom.ker :=
      IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hd)
    change IsPGroup 2 (e.toMonoidHom.comp f.toMonoidHom).ker at h
    rwa [MonoidHom.ker_comp_of_injective _ _ e.injective] at h
  apply (MonoidHom.ker_eq_bot_iff _).mp
  have hle : (coreToStar hR).ker ≤ pCore 2 (c.L ⧸ pCore 2 c.L) :=
    le_sSup ⟨inferInstance, hk⟩
  exact eq_bot_iff.mpr (hle.trans
    (pCore_quotient_pCore_eq_bot (G := c.L) 2).le)

/-- An A₅ model of the actual star image gives the same component-core model. -/
theorem core_quotient_alternatingFive_of_star
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (e : starImage c.L d.R c.L ≃* alternatingGroup (Fin 5)) :
    Nonempty ((c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 5)) :=
  ⟨(MulEquiv.ofBijective (coreToStar hR)
      ⟨coreToStar_injective_of_alternatingFive_star d c hR e,
        coreToStar_surjective hR⟩).trans e⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
