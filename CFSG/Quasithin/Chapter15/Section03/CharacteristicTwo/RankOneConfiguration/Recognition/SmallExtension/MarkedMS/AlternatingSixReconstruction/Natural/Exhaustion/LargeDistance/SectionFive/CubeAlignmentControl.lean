module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignment
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignmentModel

/-!
# Alignment/control on the literal replacement cover

Apply the two-cover three-pair calculation through the original symmetric
projection. The small actor's fixed subgroup is identified with the exact
fixed space of its transposition image. Literal subgroup-space transport
identifies all three commutators and the full fixed central attachment,
including the possible constant kernel in the order-thirty-two cover.

The resulting alternatives retain their original actors and quotient maps.
They are intended for the selected endpoint: the control alternative must
still be excluded by its retained nonnormalization witness, and the aligned
alternative is excluded by `CubeAlignment` after the residual rotation.
Neither alternative is silently discarded here, and no trapped-radius or
unconditional large-distance conclusion is asserted.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.7)--(5.8), printed pp.919--920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- The exact alignment/control alternatives on the original marked cover,
with its whole central kernel retained. -/
theorem cube_cover_alignment_or_control (u : S)
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (A P : Subgroup d.overgroup) (hA : A ≤ d.radical) (hP : P ≤ d.radical)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2) :
    ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),P⁆ ≤
      ⁅replacementMoved d,A⁆ ⊔ (replacementMoved d ⊓ center d.overgroup) ∨
    ⁅replacementMoved d,P⁆ ≤
      ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),P⁆ ⊔ ⁅replacementMoved d,A⁆ := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let F := U ⊓ centralizer (A : Set d.overgroup)
  let K := ⁅F,P⁆
  have hKU : K ≤ U := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left U P)
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [centralizer_index_eq_fixedCodim U s.projection s.surjective hker] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  obtain ⟨t,ht,hs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers (A.map s.projection) hnA hnat
  have hF : subgroupSpace U F = fixedSpace (coverAction s) (A.map s.projection) := by
    ext v
    change ((v.toMul : d.overgroup) ∈ U ∧ (v.toMul : d.overgroup) ∈ centralizer (A : Set d.overgroup)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (mem_fixedSpace_image U s.projection s.surjective hker A v).symm
  have hK : subgroupSpace U K = subspaceCommutator (coverAction s)
      (fixedSpace (coverAction s) (A.map s.projection)) (P.map s.projection) := by
    rw [subgroupSpace_commutator U s.projection s.surjective hker F P inf_le_left,hF]
    rfl
  have hU : subgroupSpace U U = ⊤ := by ext v; exact iff_of_true v.toMul.property trivial
  have hC : subgroupSpace U (U ⊓ center d.overgroup) = fixedSpace (coverAction s) ⊤ := by
    ext v
    have hh := mem_fixedSpace_image U s.projection s.surjective hker (⊤ : Subgroup d.overgroup) v
    rw [map_top_of_surjective s.projection s.surjective,coe_top,centralizer_univ] at hh
    change ((v.toMul : d.overgroup) ∈ U ∧ (v.toMul : d.overgroup) ∈ center d.overgroup) ↔ _
    simp only [v.toMul.property,true_and]
    exact hh.symm
  have hwhole (B : Subgroup d.overgroup) : subgroupSpace U ⁅U,B⁆ =
      subspaceCommutator (coverAction s) ⊤ (B.map s.projection) := by
    rw [subgroupSpace_commutator U s.projection s.surjective hker U B le_rfl,hU]
    rfl
  have hh := CubeAlignmentModel.model_dichotomy (coverAction s) (cover_model s)
    u t (P.map s.projection) ((map_mono hP).trans hR) (((map_mono hA).trans hR) ht) hs
  rw [←he,←hK,←hwhole P,←hwhole A,←hC] at hh
  rcases hh with hh | hh
  · left
    rw [←subgroupSpace_sup U (commutator_le_left U A) inf_le_left] at hh
    intro v hv
    exact hh (show Additive.ofMul (⟨v,hKU hv⟩ : U) ∈ subgroupSpace U K from hv)
  · right
    rw [←subgroupSpace_sup U hKU (commutator_le_left U A)] at hh
    intro v hv
    exact hh (show Additive.ofMul (⟨v,(commutator_le_left U P) hv⟩ : U) ∈ subgroupSpace U ⁅U,P⁆ from hv)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
