module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.Lang
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.Placement
public import Theory.AlgebraicGroup.Tori.NormalizerConjugacy

/-!
# Semisimple centralizer connectedness from the actual toral case

Place the original semisimple point in the displayed F4 coroot torus.
Conjugation carries its centralizer to the toral point centralizer and
preserves connectedness. The actual closed-subvariety homeomorphism converts
subset connectedness to connectedness of the centralizer variety. Lang
correction then gives fusion on the complete fixed group and on the original
finite Ree model, preserving the coefficient embedding.

Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*, §§3 and 12.5.
The toral connectedness theorem is the independent root-stabilizer source;
no class-count premise is used here.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

omit [CharP F 2] in
private theorem pointCentralizer_conjugate (s c : PointGroup F) :
    pointCentralizer (c * s * c⁻¹) = (pointCentralizer s).conjugate c := by
  apply SetLike.coe_injective
  ext z
  change z ∈ pointCentralizer (c * s * c⁻¹) ↔ z ∈ (pointCentralizer s).conjugate c
  rw [ClosedSubgroup.mem_conjugate_iff]
  change z ∈ Subgroup.centralizer ({c * s * c⁻¹} : Set (PointGroup F)) ↔
    c⁻¹ * z * c ∈ Subgroup.centralizer ({s} : Set (PointGroup F))
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro he
    have h := congrArg (fun x => c⁻¹ * x * c) he
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_inv_cancel, mul_one] using h
  · intro he
    have h := congrArg (fun x => c * x * c⁻¹) he
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_inv_cancel, mul_one] using h

omit [CharP F 2] in
private theorem carrier_connected (S : ClosedSubgroup (F4Chevalley.Carrier (k := F)))
    (hS : _root_.IsConnected (S : Set (PointGroup F))) :
    Variety.IsConnected S.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed
  let : ConnectedSpace {x : PointGroup F // x ∈ (S : Set (PointGroup F))} :=
    Subtype.connectedSpace hS
  let : ConnectedSpace (Variety.Point S.carrierVariety) := e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

open ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements

theorem connected_of_toral_source
    (htoral : ∀ (s : PointGroup F), s ∈ F4Chevalley.splitTorus →
      _root_.IsConnected (pointCentralizer s : Set (PointGroup F)))
    (s : PointGroup F) (hs : IsSemisimpleElement (F4Chevalley.Carrier (k := F)) s) :
    Variety.IsConnected (pointCentralizer s).carrierVariety := by
  obtain ⟨c,t,rfl⟩ := OddClasses.exists_coroot_conjugate s hs
  rw [pointCentralizer_conjugate]
  apply carrier_connected
  apply BorelIntersectionGeometry.conjugate_isConnected
  apply htoral
  exact (TorusCoverage.mem_splitTorus_iff _).mpr ⟨t,rfl⟩
theorem model_connected_of_toral_source
    (htoral : ∀ (s : PointGroup F), s ∈ F4Chevalley.splitTorus →
      _root_.IsConnected (pointCentralizer s : Set (PointGroup F)))
    (m : ℕ) (f : CoefficientField m →+* F) (x : Model m) (hx : ¬ 2 ∣ orderOf x) :
    Variety.IsConnected (pointCentralizer (modelEmbedding f x)).carrierVariety :=
  connected_of_toral_source htoral _ (OddClasses.modelEmbedding_semisimple f x hx)

theorem isConj_model_of_toral_source
    (htoral : ∀ (s : PointGroup F), s ∈ F4Chevalley.splitTorus →
      _root_.IsConnected (pointCentralizer s : Set (PointGroup F)))
    (m : ℕ) (f : CoefficientField m →+* F) (x y : Model m) (hx : ¬ 2 ∣ orderOf x)
    (hxy : IsConj (modelEmbedding f x) (modelEmbedding f y)) : IsConj x y :=
  isConj_model_of_connected_centralizer m f x y (model_connected_of_toral_source htoral m f x hx) hxy

theorem isConj_fixed_of_toral_source
    (htoral : ∀ (s : PointGroup F), s ∈ F4Chevalley.splitTorus →
      _root_.IsConnected (pointCentralizer s : Set (PointGroup F)))
    (m : ℕ) (x y : SourceFixedPoints.fixedGroup (F:=F) m) (hx : ¬ 2 ∣ orderOf x)
    (hxy : IsConj (x : PointGroup F) (y : PointGroup F)) : IsConj x y := by
  let e := SourceFixedPoints.modelEquiv m (coefficientHom F m)
  obtain ⟨a, rfl⟩ := e.surjective x
  have ha : ¬ 2 ∣ orderOf a := by simpa only [e.orderOf_eq] using hx
  exact isConj_fixed_of_connected_centralizer m (e a) y
    (model_connected_of_toral_source htoral m (coefficientHom F m) a ha) hxy

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
