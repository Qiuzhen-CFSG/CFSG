module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Cubic
public import Theory.GroupTheory.SymmetricThreePairResidualCubic
public import CFSG.Quasithin.ChapterG.Section10.Reducible.PairAction
public import CFSG.Quasithin.ChapterG.Section10.FittingSource
public import Theory.Representation.BinaryPlaneCubic

/-!
# The solvable larger-center branch reaches the actual orthogonal four-space

The nontrivial normal two-perfect residual cannot embed in S₃×S₃: such an
embedding supplies a normal cubic inside it, contrary to the source cubic
exclusion. This eliminates the reducible terminal action and binary degree
two. The actual numerical bound d≤2m therefore gives m≥2. The proved G.9
source classification yields its literal CaseFour, preserving the original
quotient representation and its action. The final coprime splitting
contradiction in the full orthogonal case is a separate source obligation.

Source: Aschbacher--Smith 14.3.14--15, printed pp.994--995.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {V : Subgroup G} {L M : Subgroup G}
section Selected
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hZ : F.ZU ≠ F.Vi 1)
include hG hempty hM hu hmany hcard e hnot F d hne g hgP hgH hyp hZ

/-- The larger-center source branch admits no faithful embedding in S₃×S₃. -/
theorem no_pair_embedding_of_center_ne_point
    (f : F.TerminalHdot →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hf : Function.Injective f) : False := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨hKH,hHK,_,hK⟩ := rankTwo_center_residual_geometry h F d hne g hgP hgH hyp hZ
  let N := centerConjugateResidual F g
  let NH := N.subgroupOf F.H
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let : NH.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  let : (F.terminalDot N).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hp : IsPPerfect 2 (F.terminalDot N) := by
    have hh : IsPPerfect 2 NH := (isPPerfect_embedded_pResidual 2 (centerConjugateSpan F g)).of_surjective
      (subgroupOfEquivOfLe hKH).symm.toMonoidHom (subgroupOfEquivOfLe hKH).symm.surjective
    exact hh.of_surjective (q.subgroupMap NH) (q.subgroupMap_surjective NH)
  obtain ⟨C,hCn,hCc,hCN⟩ := Theory.GroupTheory.SymmetricThreePair.exists_normal_cubic_le_of_twoPerfect
    f hf (F.terminalDot N) hK hp
  let := hCn
  exact no_normal_cubic_in_center_residual hG T hempty hM hu hmany hcard e hnot F d hne g hgP hgH C hCc hCN

/-- Original 14.3.15 excludes the reducible action in the larger-center branch. -/
theorem irreducible_of_center_ne_point : Representation.IsIrreducible F.terminalRepresentation := by
  by_contra hred
  obtain ⟨f,hf⟩ := hyp.reducible_symmetricThree_pair hred
  exact no_pair_embedding_of_center_ne_point hG T hempty hM hu hmany hcard e hnot F d hne g hgP hgH hyp hZ f hf

/-- The actual larger-center branch cannot have binary degree two. -/
theorem dimension_ne_two_of_center_ne_point : finrank (ZMod 2) (Additive F.Uhat) ≠ 2 := by
  intro hd
  let f := Representation.BinaryPlane.symmetricThreeHom F.terminalRepresentation hd
  have hf := Representation.BinaryPlane.symmetricThreeHom_injective F.terminalRepresentation hyp.faithful hd
  let j := f.prod (1 : F.TerminalHdot →* Equiv.Perm (Fin 3))
  have hj : Function.Injective j := fun a b he => hf (congrArg Prod.fst he)
  exact no_pair_embedding_of_center_ne_point hG T hempty hM hu hmany hcard e hnot F d hne g hgP hgH hyp hZ j hj

/-- Source numerical geometry now gives rank at least two without a model premise. -/
theorem actor_rank_two_le_of_center_ne_point :
    2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  have hb := rankTwo_dimension_le_twice_actor_of_center_ne_point
    (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) F g d hne hgP hgH hyp hZ
  have hd := hyp.two_le_dimension
  have hne := dimension_ne_two_of_center_ne_point hG T hempty hM hu hmany hcard e hnot F d hne g hgP hgH hyp hZ
  omega

/-- The solvable larger-center branch has the literal degree-four orthogonal
realization from G.9, on the original dotted action. -/
theorem orthogonal_case_of_center_ne_point
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot))
    (hs : Group.IsSolvable F.TerminalHdot) :
    ChapterG.Section09.FittingRecognition.CaseFour F.terminalRepresentation
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
  have hr := actor_rank_two_le_of_center_ne_point hG T hempty hM hu hmany hcard e hnot F d hne g hgP hgH hyp hZ
  have hX : F.terminalDot (F.X g) ≠ ⊥ := by
    intro hb
    have he : Subsingleton (F.terminalDot (F.X g)) := hb ▸ inferInstance
    let := he
    have hz : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 0 := Module.finrank_zero_of_subsingleton
    omega
  exact hyp.orthogonal_case_of_rank_bound cover hs
    (irreducible_of_center_ne_point hG T hempty hM hu hmany hcard e hnot F d hne g hgP hgH hyp hZ)
    hX hr (rankTwo_dimension_le_twice_actor_of_center_ne_point
      (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) F g d hne hgP hgH hyp hZ)
end Selected

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
