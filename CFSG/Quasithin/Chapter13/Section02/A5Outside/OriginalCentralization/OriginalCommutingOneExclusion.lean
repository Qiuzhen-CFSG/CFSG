module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalStructure
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Transport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonsolvableFieldDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReversedElementaryConsumers
-- Internal continuation of the existing unitary-factor calculation. Its private
-- matrix-center and binary-solvability proofs do not enter either public type.
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The commuting distance-one branch at the original A5 factor

The forward critical orientation forces the original field-four exponent to
be at least four. In the reverse orientation, the genuine source theorem
constructs a reduced unitary-four comparison with the point endpoint on the
left. Its native two-core lies in the solvable residual, so the same endpoint
map identifies the original L with the point residual. That residual
centralizes its core center, contrary to the original faithful local type.

The argument uses the actual F.1.1 pair and the selected right factor's
perfectness and nontriviality. It requires neither bare-L uniqueness nor a
prepared pair, and leaves the other commuting distances separate.
Source: DGS (11.7)--(11.8), pp.174--177; Aschbacher--Smith F.1.12(I)(6)
and 5.2.4--6, pp.263--264,649--651.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterF.Source Chapter6.Source.RankOneGeneric.Global
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Reduction
open ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension SuzukiContainment A5PairCatalogue
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L R S V V₁ V₂ V₃ : Subgroup G}

/-- The original faithful left factor cannot be the point endpoint of a
reduced unitary-four comparison. The right quotient is arbitrary. -/
theorem original_context_not_reduced_unitary_point_of_left
    (d : Context T L V V₁ V₂ V₃)
    (h : HypothesisF11 ![L,R] S)
    (m : ℕ) (hm : 1 ≤ m)
    (c : Iso (reducedAmalgam ![L,R] S) (UnitaryFourNative.amalgam m hm true)) : False := by
  let P := parabolic ![L,R] (reducedSylow ![L,R] S) 0
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  let eP : P ≃* pointParabolic m hm := c.left
  have hnsol : ¬ Group.IsSolvable L := Chapter1.mem_L_not_isSolvable
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
      d.hypothesis.local_component).1
  have hmgt : 1 < m := by
    by_contra hh
    have he : m = 1 := by omega
    subst m
    let := UnitaryFactors.binary_point_solvable
    let f : L →* pointParabolic 1 hm := eP.toMonoidHom.comp (inclusion hLP)
    exact hnsol (Group.isSolvable_of_isSolvable_injective
      (f := f) (eP.injective.comp (inclusion_injective _)))
  have hcore : pCore 2 (pointParabolic m hm) ≤ solvableResidual (pointParabolic m hm) := by
    apply (map_le_map_iff_of_injective (pointParabolic m hm).subtype_injective).mp
    rw [PointLocal.pointParabolic_solvableResidual m hm hmgt,
      PointLocal.pointParabolic_twoCore]
    exact map_subtype_le _
  let f : L →* ProjectiveGroup m hm := (pointParabolic m hm).subtype.comp
    (eP.toMonoidHom.comp (inclusion hLP))
  have hf : Function.Injective f := (pointParabolic m hm).subtype_injective.comp
    (eP.injective.comp (inclusion_injective _))
  have hmark := local_marking_of_reduced_equiv h 0 d.quotient eP hcore
  change (L.subgroupOf P).map eP.toMonoidHom = solvableResidual (pointParabolic m hm)
    at hmark
  have hr : f.range = PointLocal.ProjectiveLocal m hm := by
    dsimp only [f]
    rw [MonoidHom.range_comp,MonoidHom.range_comp,inclusion_range,hmark]
    exact PointLocal.pointParabolic_solvableResidual m hm hmgt
  let e := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  have hfaith := (Chapter12.Section02.RankOneModule.faithfulMaximalFamily_of_hypothesis
    (Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient)).2
  exact faithful_not_core_center_central hfaith e
    (UnitaryFactors.point_core_center_central m hm)

/-- The complete commuting distance-one branch is impossible for an
original A5 left context and a nontrivial perfect selected right factor. -/
theorem original_context_commuting_bOne_impossible
    (d : Context T L V V₁ V₂ V₃)
    (h : HypothesisF11 ![L,R] S) (hp : Group.IsPerfect R) (hne : R ≠ ⊥)
    (hb : b (reducedFamily ![L,R] S) = 1)
    (hcomm : ⁅Z (reducedFamily ![L,R] S) (base (reducedFamily ![L,R] S) false),
      Z (reducedFamily ![L,R] S) (base (reducedFamily ![L,R] S) true)⁆ = ⊥) : False := by
  have hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^2) := by
    refine ⟨GaloisField 2 2,inferInstance,inferInstance,
      GaloisField.card 2 2 (by decide),?_⟩
    obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    exact ⟨d.quotient.trans e.symm⟩
  have hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic ![L,R] S i) := by
    have hn : ∀ i : Fin 2, ¬ Group.IsSolvable (![L,R] i) := by
      intro i
      fin_cases i
      · exact Chapter1.mem_L_not_isSolvable
          ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
            d.hypothesis.local_component).1
      · let := hp
        let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hne
        exact Group.IsPerfect.not_isSolvable R
    intro i hs
    let := hs
    exact hn i (Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show ![L,R] i ≤ parabolic ![L,R] S i from
        le_sup_left.trans le_sup_left)) (inclusion_injective _))
  rcases original_critical_base_edge_or_reverse h hb with hc | hc
  · obtain ⟨m,hm,he⟩ := original_nonsolvable_commuting_one_field_degree h hc hb hcomm
      hns (by decide : 0 < 2) hpsl
    omega
  · obtain ⟨m,hm,⟨e⟩⟩ := ReversedElementary.reversed_linear_reduced_comparison
      L R S h hc hb hcomm (by decide : 1 < 2) hpsl
    exact original_context_not_reduced_unitary_point_of_left d h m hm e

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
