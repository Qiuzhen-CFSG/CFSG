module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.Triangular
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagRepresentation.Linear

/-!
# The regular natural Spin representation and solvable invariant flags

The regular Spin cover followed by the ordinary linear inclusion realizes the
natural action on the eight-dimensional hyperbolic space. Restriction along a
closed subgroup uses its canonical carrier algebraic group. Lie–Kolchin then
supplies a full invariant flag for each connected solvable closed subgroup.

This is the geometric input to the maximality argument for the concrete
candidates; it asserts no uniqueness for a candidate-invariant flag.
Source: GLS3, 1.11.2 and 1.14.4 (`refs/KGroup/GLS3/Chapter1.tex`), and
Steinberg (6.2)(a) (`refs/KGroup/GLS3/Chapter2St2.tex`).
-/

@[expose] public section
open Theory Theory.AlgebraicGroup
open Theory.AlgebraicGroup.BorelGeometricConjugacy
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.NaturalCoefficients
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags
universe u
variable (k : Type u) [Field k] [IsAlgClosed k]
local instance solvableFlagCarrierAlgebraicGroup (S : ClosedSubgroup (groupVariety k)) : AlgebraicGroup S.carrierVariety :=
  S.carrierAlgebraicGroup

def naturalRepresentation : RationalRepresentation (groupVariety k) (QuadraticSpace k) where
  action := (LinearMap.GeneralLinearGroup.generalLinearEquiv k (QuadraticSpace k)).symm.toMonoidHom.comp
    ((quadraticIsometrySubgroup (quadraticForm k)).subtype.comp (naturalAction k))

lemma naturalRepresentation_apply (g : Points k) (v : QuadraticSpace k) :
    ((naturalRepresentation k).action g : Module.End k (QuadraticSpace k)) v =
      (naturalAction k g).1 v := rfl

lemma naturalRepresentation_isRational : IsRationalRepresentation (naturalRepresentation k) := by
  let f := (cliffordModel k).omega.inclusion.comp (cliffordModel k).spinCover
  refine ⟨(cliffordModel k).basis, f, ?_⟩
  intro g
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (QuadraticSpace k)).injective
  change LinearMap.GeneralLinearGroup.generalLinearEquiv k (QuadraticSpace k)
      (glPointEquivOf k (QuadraticSpace k) (cliffordModel k).basis
        ((cliffordModel k).omega.inclusion.onPoints ((cliffordModel k).spinCover.onPoints g))) = _
  rw [(cliffordModel k).omegaLinear_points]
  simp only [naturalRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  rfl

def subgroupRepresentation (S : ClosedSubgroup (groupVariety k)) :
    RationalRepresentation S.carrierVariety (QuadraticSpace k) where
  action := (naturalRepresentation k).action.comp S.inclusion.onPoints

lemma subgroupRepresentation_isRational (S : ClosedSubgroup (groupVariety k)) :
    IsRationalRepresentation (subgroupRepresentation k S) := by
  obtain ⟨b, f, hf⟩ := naturalRepresentation_isRational k
  exact ⟨b, f.comp S.inclusion, fun g => hf (S.inclusion.onPoints g)⟩

def Preserves (g : Points k) (F : FullFlag k (QuadraticSpace k)) : Prop :=
  ∀ i v, v ∈ F.subspace i → (naturalAction k g).1 v ∈ F.subspace i

lemma exists_invariant_flag (S : ClosedSubgroup (groupVariety k))
    (hc : _root_.IsConnected (S : Set (Points k)))
    (hs : Group.IsSolvable (Variety.Point S.carrierVariety)) :
    ∃ F : FullFlag k (QuadraticSpace k), ∀ g ∈ S, Preserves k g F := by
  have hc' : Variety.IsConnected S.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed
    let : ConnectedSpace {x : Points k // x ∈ (S : Set (Points k))} :=
      Subtype.connectedSpace hc
    let : ConnectedSpace (Variety.Point S.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  obtain ⟨b, hb⟩ :=
    (subgroupRepresentation k S).exists_basis_tTriangular_of_isSolvable_isConnected
      (subgroupRepresentation_isRational k S) hs hc'
  refine ⟨FullFlag.ofBasis b, ?_⟩
  intro g hg
  let x := S.pointEquiv.symm ⟨g, hg⟩
  have he : S.inclusion.onPoints x = g :=
    congrArg Subtype.val (S.pointEquiv.apply_symm_apply ⟨g, hg⟩)
  have h := FullFlag.ofBasis_invariant b _ (hb x)
  change ∀ i v, v ∈ (FullFlag.ofBasis b).subspace i →
    (naturalAction k (S.inclusion.onPoints x)).1 v ∈ (FullFlag.ofBasis b).subspace i at h
  rwa [he] at h

end Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags
