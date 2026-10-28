module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesPreparation
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedCubicNormality
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.SpecificGroups.G2Even.BinaryTwoLocalSolvable
public import Theory.SpecificGroups.AlternatingSix.TwoLocalSolvable

/-!
# Finite star rows with solvable two-local normalizers

The actual radical has nontrivial two-group image in the automorphism group
of the component's central quotient. Its normalizer contains a nontrivial
perfect image of the original local group. Two-local solvability in Aut(A₆)
and Aut(G₂(2)′) therefore excludes the A₆, 3.A₆ and G₂(2)′ star rows.

The central-cover equivalence is the literal C.2.7 quotient map. In particular,
the triple-cover argument needs only its central quotient, and does not identify
the chosen module V with the full source module W. These exclusions discharge
three finite cases in the rank-one block assembly, whose remaining C.4.1 rows
are owned by qt-d-1222-rankone-uniqueness-block.
Source: Aschbacher–Smith C.4.5 and the proof of C.4.1, pp.152–153, applied in
4.3.7, pp.615–616.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem false_of_soluble_two_local_central_model
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    {A : Type*} [Group A] (e : coreCentralQuotient c.K ≃* A)
    (hs : ∀ R : Subgroup (MulAut A), R ≠ ⊥ → IsPGroup 2 R →
      Group.IsSolvable (normalizer (R : Set (MulAut A)))) : False := by
  let Q := coreCentralQuotient c.K
  let R := coreCentralActorImage c.K ((c.I.pCoreIn 2).subgroupOf c.H)
  let a := MulAut.congr e
  have hR : R ≠ ⊥ := c.c28.constrained_radical_action_nontrivial c.K c.component
    c.quotient c.block_source_outside hf
  have hp : IsPGroup 2 R := (isPGroup_pCoreIn 2 c.I).comap_subtype.comap_subtype.map _
  have hsol := hs (R.map a.toMonoidHom)
    (fun he => hR ((R.map_eq_bot_iff_of_injective a.injective).mp he)) (hp.map _)
  rw [← map_equiv_normalizer_eq R a] at hsol
  let : Group.IsSolvable ((normalizer (R : Set (MulAut Q))).map a.toMonoidHom) := hsol
  apply c.block_radical_action_normalizer_not_solvable
  let f := (normalizer (R : Set (MulAut Q))).equivMapOfInjective a.toMonoidHom a.injective
  exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective

/-- The binary derived G₂ row contradicts the actual radical action. -/
theorem SourceConfiguration.block_star_not_g2DerivedTwo
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) : False := by
  let ec := (coreCentralQuotientCongr
    (c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective)).trans
    (Section04Constrained.source_simple_equiv (c.block_source_input hf) e
      Theory.SpecificGroups.g2_derived_two_center_eq_bot)
  exact false_of_soluble_two_local_central_model c hf ec
    Atlas.G2.binaryDerived_aut_two_normalizer_solvable

/-- The ordinary A₆ star row is impossible in the source configuration. -/
theorem SourceConfiguration.block_star_not_alternatingSix
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
      alternatingGroup (Fin 6)) : False := by
  let ec := (coreCentralQuotientCongr
    (c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective)).trans
    (Section04Constrained.source_simple_equiv (c.block_source_input hf) e
      (alternatingGroup.center_eq_bot (by simp)))
  exact false_of_soluble_two_local_central_model c hf ec
    AlternatingSix.ShadowLocal.two_normalizer_solvable

/-- This central-quotient obstruction discharges the 3.A₆ star row, regardless
of the order of its center. -/
theorem SourceConfiguration.block_star_central_not_alternatingSix
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ⧸
      center (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) ≃*
        alternatingGroup (Fin 6)) : False := by
  let ec := (c.c28.constrained_star_central_equiv c.K c.component c.quotient
    c.block_source_outside hf).trans e
  exact false_of_soluble_two_local_central_model c hf ec
    AlternatingSix.ShadowLocal.two_normalizer_solvable

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
