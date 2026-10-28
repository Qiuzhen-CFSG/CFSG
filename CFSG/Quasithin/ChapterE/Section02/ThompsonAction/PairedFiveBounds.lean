module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveBaumann
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.NoStrong
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.ResidualGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.FrattiniSource

/-!
# Residual and dimension transport on the original paired source

The offender residual equals the ambient residual under the genuine
minimal-parabolic and reduced-module hypotheses. The same marked quotient
then identifies it with the actual alternating product. Every source fixed
codimension is computed through the original subtype and product maps.

Source: Aschbacher--Smith B.6.9(4), B.6.10 and E.2.3(3).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
variable
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))

include hP hU hJ in
theorem source_symmetric_residual :
    (pResidual 2 G).map q = (pResidual 2 (FiveCentralExtension.Sym × FiveCentralExtension.Sym)).map
      ((offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype.comp
        c.action.groupEquiv.symm.toMonoidHom) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  rw [map_pResidual_of_surjective 2 q hq,←map_map,
    map_pResidual_of_surjective 2 c.action.groupEquiv.symm.toMonoidHom c.action.groupEquiv.symm.surjective]
  exact (offender_residual_eq (T.mapSurjective hq) hp α hff hcore).symm

omit [Finite H] in
theorem source_symmetric_fixedCodim (A : Subgroup (FiveCentralExtension.Sym × FiveCentralExtension.Sym)) :
    fixedCodim (NormalElementaryQuotient.representation U q hq hker)
      (A.map ((offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype.comp
        c.action.groupEquiv.symm.toMonoidHom)) = fixedCodim FivePair.action A := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  have hc := c.symmetric_fixedCodim (A.map c.action.groupEquiv.symm.toMonoidHom)
  have hm : (A.map c.action.groupEquiv.symm.toMonoidHom).map c.action.groupEquiv.toMonoidHom = A :=
    c.action.groupEquiv.mapSubgroup.apply_symm_apply A
  rw [hm] at hc
  change Module.finrank (ZMod 2) (Additive U ⧸ fixedSpace (α.comp Y.subtype) _) = _ at hc
  rw [fixedSpace_comp_map] at hc
  rw [←map_map]
  exact hc

end CFSG.Quasithin.ChapterE.ThompsonAction
