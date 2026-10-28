module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFive
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedSource
/-!
# The nonsolvable E.2.3 Sylow alternatives on the original group

The genuine earlier classification gives a quasisimple action or the actual
pair of natural factors. The first case is completely dispatched, including
the symmetric-five index-two extension. The linear pair gives the original
Baumann Sylow subgroup. The remaining symmetric-five pair retains the same
quotient, both original factors and their prescribed-Sylow exchange for the
separate paired C.1.24 argument.

Source: Aschbacher--Smith E.2.3 and 3.1.7, pp.216--217 and575--576.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

/-- The actual Sylow conclusion, including the single symmetric-five extension. -/
abbrev SourceSylowAlternative (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) : Prop :=
  Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
    (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∨
  ∃ S₁ : Subgroup G,
    IsSylowSubgroupIn S₁ (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
    baumann (T : Subgroup G) ≤ S₁ ∧
    ((baumann (T : Subgroup G)).subgroupOf S₁).index = 2 ∧
    S₁ ≤ conjugateSpanBy (baumann (T : Subgroup G))
      (pResidual 2 G ⊓ minimalParabolicMax T hP)

/-- The remaining actual pair, with its same quotient action and original Sylow exchange. -/
abbrev SymmetricFivePairSource (T : Sylow 2 G)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) : Prop :=
  let α := NormalElementaryQuotient.representation U q hq hker
  letI := offenderSubgroup_normal α
  ∃ d : SourceTwoFactorCase (α.comp (offenderSubgroup α).subtype),
    ∃ t : T.mapSurjective hq,
      d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
      d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first ∧
      Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))

/-- All nonsolvable source rows are discharged except the same marked symmetric-five pair. -/
theorem nonsolvable_sylow_or_paired_five
    {K : GroupClass.{u}} (earlier : AdequateClassificationInput.{u,u} K)
    (hG : IsSQTK K G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hs : ¬ Group.IsSolvable G) :
    SourceSylowAlternative T hP ∨ SymmetricFivePairSource T U q hq hker := by
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  rcases nonsolvable_rankOne_factors_or_quasisimple earlier hG T hP U q hq hker hcore hs hJ with
    ⟨hqs,hc⟩ | ⟨d,_,_⟩
  · obtain ⟨c⟩ := hc
    exact Or.inl (quasisimple_source_sylow_or_extension T hP U hU hJ q hq hker hqs c)
  · rcases pair_baumann_or_symmetric_five T hP U hU hJ q hq hker d with hlin | hfive
    · exact Or.inl (Or.inl hlin.1)
    · exact Or.inr ⟨d,hfive⟩
end CFSG.Quasithin.ChapterE.ThompsonAction
