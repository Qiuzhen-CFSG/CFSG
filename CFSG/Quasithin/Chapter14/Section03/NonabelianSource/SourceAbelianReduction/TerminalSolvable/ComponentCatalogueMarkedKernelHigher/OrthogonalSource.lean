module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.Reduction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.OrthogonalSourceGeometry
public import Theory.Representation.BinaryOffender.IrreducibleSubspaceExistence

/-!
# The marked higher-multiplicity orthogonal source construction

For the literal marked source with nonfaithful actor on I and higher
multiplicity, every actor stabilizes an actual constituent in I-perp,
disjoint from I and therefore avoiding the original marked vector. The
homogeneous normal restriction and fixed-intertwiner argument construct it
without an additional field or projective-coordinate hypothesis. G.10.14
then gives rank-one displacement on that same constituent. The fixed marked
line is supplied by the previously proved same-vector source alternative.

These theorems discharge StabilizedOrthogonalConstituents in the existing
higher-multiplicity reduction. The independent model-recognition and
QuotientTransvection endgame remain with its consumer.

Source: Aschbacher--Smith, G.11.9(1)-(2), printed p.369, applied in14.3.15.
-/

public noncomputable section
open Module Representation Subgroup Representation.BinaryOffender
open scoped MonoidAlgebra
open CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedHigherOrthogonal
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- G.11.9(1) on the literal marked source, with no coordinate hypothesis. -/
theorem source_stabilizedOrthogonalConstituents
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat)) :
    StabilizedOrthogonalConstituents (F := F) (g := g) (B := B) (v := v) (L := L) (I := I) := by
  intro x hxC
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let : Group.IsPerfect H := s.component.orbit_isPerfect ⊤
  let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
  let : IsIrreducible R.toRepresentation := s.irreducible
  let : IsSemisimpleModule (ZMod 2)[H]
      (Representation.asModule (F.terminalRepresentation.comp H.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple F.terminalRepresentation
      (s.hypothesis.irreducible_of_not_solvable s.nonsolvable) H
  have hxx : (x : F.TerminalHdot) * x = 1 := by
    have he := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (F.terminalDot (F.X g))) x
    exact congrArg Subtype.val (by simpa only [pow_two] using he)
  obtain ⟨J,hJ,hdis,hperp,hxJ⟩ := exists_stable_orthogonal_simple
    F.terminalRepresentation H R s.constituents_sameModule B s.hypothesis.preserves
    s.hypothesis.alternating s.hypothesis.nondegenerate
    (s.constituent_isotropic_of_not_actorFaithful hk) x hxx
    (s.actor_stabilizes x.property) hd
  have hJs : H ≤ subspaceStabilizer F.terminalRepresentation J.toSubmodule := by
    apply le_subspaceStabilizer
    exact fun h hh w hw => J.apply_mem_toSubmodule ⟨h,hh⟩ hw
  have hnfix : ¬ J.toSubmodule ≤ fixedSpace F.terminalRepresentation H := by
    intro hf
    have hzero : J = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      apply le_bot_iff.mp
      exact hf.trans_eq s.fixedSpace_eq_bot
    exact ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot hzero
  obtain ⟨K,hKJ,hK⟩ := exists_isIrrPlus_le_of_not_fixed F.terminalRepresentation H
    J.toSubmodule hJs hnfix
  let hKinv : Subrepresentation (F.terminalRepresentation.comp H.subtype) :=
    ⟨K, fun h w hw => (hK.choose h.property w).mpr hw⟩
  have hKle : hKinv ≤ J := hKJ
  have hKat : IsAtom J := (Subrepresentation.irreducible_iff_isAtom J).mp hJ
  have hKeq : hKinv = J := (hKat.le_iff_eq
    (fun hb => hK.ne_bot F.terminalRepresentation
      (congrArg Subrepresentation.toSubmodule hb))).mp hKle
  have hJIrr : IsIrrPlus F.terminalRepresentation H J.toSubmodule :=
    (congrArg Subrepresentation.toSubmodule hKeq) ▸ hK
  refine ⟨J.toSubmodule,hJIrr,?_,hperp,hxJ⟩
  intro hv
  exact s.hypothesis.point_ne_zero ((Submodule.disjoint_def.mp hdis) v s.point_mem hv)

/-- The complete higher-multiplicity geometric source input: the original
marked line and stabilized orthogonal constituents. -/
theorem source_higher_geometry
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat)) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} ∧
    StabilizedOrthogonalConstituents (F := F) (g := g) (B := B) (v := v) (L := L) (I := I) :=
  ⟨s.source_fixedSpace_eq_point_of_higher_dimension hd,
    s.source_stabilizedOrthogonalConstituents hk hd⟩

/-- G.11.9(2)'s rank-one action on the actual constituent constructed above. -/
theorem source_exists_orthogonal_constituent_rank_one
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat))
    (x : F.terminalDot (F.X g))
    (hxC : (x : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)) :
    ∃ J : Submodule (ZMod 2) (Additive F.Uhat),
      IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) J ∧
      v ∉ J ∧ J ≤ B.orthogonal I ∧
      (x : F.TerminalHdot) ∈ subspaceStabilizer F.terminalRepresentation J ∧
      Module.finrank (ZMod 2)
        (LinearMap.range ((F.terminalRepresentation x - 1).comp J.subtype)) = 1 := by
  obtain ⟨J,hJ,hv,hperp,hxJ⟩ := s.source_stabilizedOrthogonalConstituents hk hd x hxC
  exact ⟨J,hJ,hv,hperp,hxJ,s.orthogonal_constituent_displacement_eq_one hJ hv hperp x hxJ hxC⟩
end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

end
