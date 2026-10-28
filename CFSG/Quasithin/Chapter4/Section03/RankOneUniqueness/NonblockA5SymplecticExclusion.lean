module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5MovedCubic
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5SymplecticAlignment
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NaturalStarFieldDegree
public import Theory.Representation.FirstCohomologySymplecticFour.LargeField
public import Theory.Representation.SymplecticFourOrthogonalCover.ParabolicCubicFixed

/-!
# The natural symplectic moved row excludes the original A₅ module

The original chosen permutation core supplies a nonzero cubic-fixed vector
in the literal source moved space. The same seed and star map identify its
actor with a point or plane residual in Sp₄(4), retaining its whole two-core.
The point residual fixes that core-fixed space, contradicting full movement;
the plane residual's cubic quotient fixes no nonzero vector there.

No block condition, natural-module identification of the original V, or
whole-core classification premise is assumed. The actual moved section and
its Irr-plus natural symplectic marking remain explicit for row assembly.
Source: Aschbacher--Smith C.4.8 and 4.3.8--10, printed pp.154 and616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour Representation.SymplecticFourOrthogonalCover
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

private theorem exists_derived_natural_marking {F : BinaryField} (hF : 2 < Nat.card F.Carrier)
    {D : Type*} [Group D] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (e : ActionEquiv ρ (binarySymplectic F)) :
    ∃ e' : ActionEquiv ρ (binaryNatural (K := F.Carrier)),
      ∀ d, (e'.groupEquiv d).val = e.groupEquiv d := by
  let a : commutator (Sp F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF)).trans
      Subgroup.topEquiv
  refine ⟨⟨e.groupEquiv.trans a.symm,e.linearEquiv,?_⟩,?_⟩
  · intro g v
    change e.linearEquiv (ρ g v) =
      Matrix.mulVec (a.symm (e.groupEquiv g)).val.val (e.linearEquiv v)
    rw [show (a.symm (e.groupEquiv g)).val = e.groupEquiv g from a.apply_symm_apply _]
    exact e.intertwines g v
  · intro g
    exact a.apply_symm_apply _

set_option maxHeartbeats 800000 in
/-- The actual Irr-plus symplectic natural row is incompatible with the
original chosen A₅ permutation core in the unchanged source configuration. -/
theorem not_symplectic_moved_action_of_a5
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (s : MovedSection ((starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2))).subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)))))
    (hi : IsIrrPlus ((starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2))).subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)))) s.space.toSubmodule)
    (F : BinaryField)
    (a : ActionEquiv (s.action.comp
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)))).subtype)
      (binarySymplectic F)) : False := by
  let R := c.I.pCoreIn 2
  let C := starImage (c.K.map c.H.subtype) R (c.K.map c.H.subtype)
  let O := offenderSubgroup (starRepresentation (c.K.map c.H.subtype) R)
  have hCO : C ≤ O := (C27Source.star_moved_section_from_source (c.block_source_input hf)).1
  let eC := subgroupOfEquivOfLe hCO
  let e := eC.symm.trans a.groupEquiv
  have hlarge := C27Source.star_symplectic_degree_gt_one_from_source
    (c.block_source_input hf) F e
  have hn : (L.subgroupOf (c.H ⊓ normalizer (L : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer inf_le_right
  obtain ⟨hF,g,hg⟩ := c.c28.constrained_normal_a5_symplectic_alignment
    hn d.quotient c.K c.component c.quotient c.block_source_outside hf e F.card_eq hlarge
  obtain ⟨aD,haD⟩ := exists_derived_natural_marking (by omega : 2 < Nat.card F.Carrier) a
  let E := eC.symm.trans aD.groupEquiv
  let B := (L.subgroupOf (c.K.map c.H.subtype)).map (E.toMonoidHom.comp (toStarImage (c.K.map c.H.subtype) R))
  let σ := s.coverAction aD
  obtain ⟨A,hA,hm,b,hb,w,hwne,hw,hfix⟩ := a5_source_moved_cubic_fixed_vector d c hf s aD.groupEquiv
  have hmark : (B.map (commutator (Sp F.Carrier)).subtype).map (MulAut.conj g).toMonoidHom =
      (L.subgroupOf (c.K.map c.H.subtype)).map ((e.trans (MulAut.conj g)).toMonoidHom.comp (toStarImage (c.K.map c.H.subtype) R)) := by
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro k
    change MulAut.conj g ((aD.groupEquiv (eC.symm (toStarImage (c.K.map c.H.subtype) R k))).val) =
      MulAut.conj g (a.groupEquiv (eC.symm (toStarImage (c.K.map c.H.subtype) R k)))
    rw [haD]
  have hlocal : (B.map (commutator (Sp F.Carrier)).subtype).map (MulAut.conj g).toMonoidHom =
      pointLocal ∨ (B.map (commutator (Sp F.Carrier)).subtype).map (MulAut.conj g).toMonoidHom =
      planeLocal := by
    rw [hmark]
    exact hg.imp And.right And.right
  have hp := s.coverProjection_isCover hi aD
  apply hwne
  rcases hlocal with hpoint | hplane
  · have hfixed : A ≤ fixedSpace σ B := hA.trans
      (ParabolicCubicFixed.point_fixed_of_core_fixed hF (s.coverProjection aD) hp B g hpoint)
    have hzero : A = ⊥ := hm.symm.trans ((subspaceCommutator_eq_bot_iff σ A B).mpr hfixed)
    simpa only [hzero,Submodule.mem_bot] using hw
  · exact ParabolicCubicFixed.plane_cubic_fixed_eq_zero hF (s.coverProjection aD) hp B g hplane
      A hA hm b hb w hw hfix

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
