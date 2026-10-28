module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SymmetricBlockSource
/-!
# The original single symmetric-five block consumer

The genuine whole-module S5 source supplies the natural quotient and fixed
kernel. The existing component lift supplies the literal p-residual A5
component. Applying the characteristic Baumann source to that same quotient
retains the original module and Thompson commutator.

Source: Aschbacher–Smith E.2.3(4), C.1.24(a), pp.130–131,217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterC ChapterC.RankOne.FiveBlockSource ChapterC.RankOne.ChiProduct.SelectedRankOne Chapter1.Section02
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

theorem quasisimple_five_block_of_no_characteristic_baumann
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk))))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (hf : generalizedFitting G = pCore 2 G)
    (hno : ∀ D : Subgroup (baumann (T : Subgroup G)), D.Characteristic →
      (D.map (baumann (T : Subgroup G)).subtype).Normal → D = ⊥) :
    IsBlock (pResidual 2 G) ∧ IsAlternatingBlock (pResidual 2 G) 5 ∧
      pResidual 2 G = ⁅pResidual 2 G,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype = ⁅U,pResidual 2 G⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype ≤ U := by
  obtain ⟨p,hp,hpk,f,hf',he,hfk⟩ := quasisimple_five_whole_quotient
    T hP U hU hJ q hq hk hqs s e
  have him : (pResidual 2 G).map p = alternatingGroup (Fin 5) := by
    rw [map_pResidual_of_surjective 2 p hp,Equiv.Perm.twoResidual_eq_alternating]
  have hfix : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U p hp hpk g v = v := by
    intro v hv g hg
    have hh : v ∈ fixedSpace (NormalElementaryQuotient.representation U p hp hpk)
        ((pResidual 2 G).map p) := hfk ▸ hv
    exact hh ⟨g,him.symm ▸ hg⟩
  exact covered_five_block_of_no_characteristic_baumann h36 hG T hP U hU hJ
    p hp hpk f hf' he hfix hf hno

end CFSG.Quasithin.ChapterE.ThompsonAction
