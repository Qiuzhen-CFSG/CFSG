module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleBaumann
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleWholeNatural
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ThompsonImage
/-!
# The literal whole-module quotient in the quasisimple linear source

The original moved natural section has no strong offenders. The actual
FF action therefore supplies the sharp Sylow supplement and the original
U is the sum of [U,O²(G)] and C_U(O²(G)). Its quotient by that fixed space
is naturally the same rank-two linear module. All original offenders lie
in the marked linear component, so the offender group equals that component
and the literal image of the global Thompson subgroup.

Source: Aschbacher–Smith E.2.3(1)–(2), printed pp.216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
theorem quasisimple_linear_whole_source
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2) :
    let α := NormalElementaryQuotient.representation U q hq hker
    let Y := offenderSubgroup α
    let σ := α.comp Y.subtype
    (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q = Y ∧
      generalizedFitting Y = ⊤ ∧
      (NormalElementaryQuotient.commutatorSpace U (pResidual 2 G) ⊔
        fixedSpace α ((pResidual 2 G).map q) = ⊤) ∧
      IsLinearNatural (fixedQuotientRepresentation σ (generalizedFitting Y)) F 2 := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let A := generalizedFitting Y
  let := offenderSubgroup_normal α
  let := hqs
  let : IsSimpleGroup (A ⧸ center A) := hqs.simple
  let : Nontrivial A := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center A))
  obtain ⟨e⟩ := hnatural
  have hF := perfect_linear_two_field_large F e.groupEquiv
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  have hL := (source_quasisimple_fitting_eq_residual (T.mapSurjective hq) hp Y
    (offender_generation (T.mapSurjective hq) hp α hff hcore).2 hqs).1
  have hX : A.map Y.subtype = (pResidual 2 G).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact hL

  let σ := α.comp Y.subtype
  have hffσ : IsFFModule σ := by
    obtain ⟨B,hB⟩ := (isFFModule_iff_exists_bestOffender α).mp hff
    exact ⟨B.subgroupOf Y,(hB.isOffender α).subgroupOf α (hB.le_offenderSubgroup α)⟩
  have hself : centralizer (A : Set Y) ≤ A := centralizer_generalizedFitting_le Y
  have hwhole := moved_sup_fixed_of_natural_section σ hffσ A hself s F hF e
  have hnatural := whole_quotient_natural_of_moved_section σ hffσ A hself s F hF e
  have hAtop : A = ⊤ := by
    have hall := offenderSubgroup_le_natural_layer_of_moved_section σ A hself s F hF e
    rw [offenderSubgroup_restrict_eq_top α] at hall
    exact top_unique hall
  have hres : (pResidual 2 G).map q = Y := by
    rw [←hX,hAtop,←MonoidHom.range_eq_map,range_subtype]
  have hJglobal : (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q = Y := by
    apply le_antisymm (global_thompson_image_le_offender T U q hq hker
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)))
    change Y ≤ _
    rw [←hres]
    exact map_mono (residual_le_thompson T hP U hU hJ).1
  refine ⟨hJglobal,hAtop,?_,hnatural⟩
  rw [←s.space_eq] at hwhole
  rw [source_moved_space_eq U q hq hker Y A s (pResidual 2 G) hX,
    fixedSpace_comp_map,hX,←NormalElementaryQuotient.commutatorSpace_eq U q hq hker] at hwhole
  exact hwhole
end CFSG.Quasithin.ChapterE.ThompsonAction
