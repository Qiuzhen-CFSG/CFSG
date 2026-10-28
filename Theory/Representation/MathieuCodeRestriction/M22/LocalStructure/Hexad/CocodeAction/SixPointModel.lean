module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel.Quotients
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel.OrthogonalDuality

/-!
# The actual six-coordinate hexad cocode model

Restriction of even words on the source octad identifies its M22 cocode
image with the deleted module on the six coordinates outside the marked
pair. The native inner and outer coordinate images are A6 and S6. Pair
rigidity identifies the relative action kernels, so the native fixed-space
action descends faithfully to the intrinsic stabilizer quotients.

The perfect coordinate pairing identifies this cocode module with the dual
of the pair perpendicular in the natural octad space. The quadratic form
restricts to that perpendicular, where the pair remains nonsingular; it is
not descended through the pair line. Earlier M24 scalar fixed-space and
H.14 restriction facts remain the precise inputs to fixed-space transfer.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399,
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
namespace MathieuCode.Hexad.CocodeAction.SixPointModel

variable {G : Type*} [Group G] {f : G →* m22PairStabilizer} {K : Subgroup G}
variable (h : RestrictionInput f K O)
variable (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
  fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
variable (h6 : Module.finrank (ZMod 2)
  (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6)

/-- The native action restricted to its actual common fixed space. -/
def fixedRepresentation : Representation (ZMod 2) (Stabilizer f)
    (fixedSpace (quotientRepresentation f) K) where
  toFun g := (quotientRepresentation f g.val).restrict
    (fun _ hv => fixedSpace_invariant h hd h6 g hv)
  map_one' := by
    ext v
    exact LinearMap.congr_fun (map_one (quotientRepresentation f)) v.val
  map_mul' g j := by
    ext v
    exact LinearMap.congr_fun (map_mul (quotientRepresentation f) g.val j.val) v.val

@[simp] lemma fixedRepresentation_apply (g : Stabilizer f)
    (v : fixedSpace (quotientRepresentation f) K) :
    (fixedRepresentation h hd h6 g v).val = quotientRepresentation f g.val v.val := rfl

/-- Pair rigidity identifies the entire kernel of the fixed-space action. -/
lemma fixedRepresentation_ker :
    (fixedRepresentation h hd h6).ker = K.subgroupOf (Stabilizer f) := by
  ext g
  change fixedRepresentation h hd h6 g = 1 ↔ g.val ∈ K
  constructor
  · intro hg
    have hm : g.val ∈ subspaceKernel (quotientRepresentation f)
        (fixedSpace (quotientRepresentation f) K) ⊤ :=
      ⟨Subgroup.mem_top _, fun v hv =>
        congrArg Subtype.val (LinearMap.congr_fun hg ⟨v, hv⟩)⟩
    rwa [fixedSpace_pointwiseKernel h.injective h.kernel_image m22Pair_le_sourceOctad] at hm
  · intro hg
    ext v
    exact v.property ⟨g.val, hg⟩

variable (N : Subgroup (Stabilizer f)) [N.Normal]
variable (hN : N = K.subgroupOf (Stabilizer f))

/-- Descent of the actual fixed-space action through its relative intrinsic kernel. -/
def quotientFixedRepresentation : Representation (ZMod 2) (Stabilizer f ⧸ N)
    (fixedSpace (quotientRepresentation f) K) :=
  QuotientGroup.lift N (fixedRepresentation h hd h6)
    (le_of_eq (hN.trans (fixedRepresentation_ker h hd h6).symm))

/-- The actual six-coordinate homomorphism on the same quotient. -/
def quotientCoordinateAction : (Stabilizer f ⧸ N) →* Equiv.Perm H :=
  QuotientGroup.lift N (coordinateAction f)
    (le_of_eq (hN.trans (coordinateAction_ker h.injective h.kernel_image).symm))

@[simp] lemma quotientFixedRepresentation_mk (g : Stabilizer f)
    (v : fixedSpace (quotientRepresentation f) K) :
    (quotientFixedRepresentation h hd h6 N hN (QuotientGroup.mk g) v).val =
      quotientRepresentation f g.val v.val := rfl

@[simp] lemma quotientCoordinateAction_mk (g : Stabilizer f) :
    quotientCoordinateAction h N hN (QuotientGroup.mk g) = coordinateAction f g := rfl

/-- The quotient representation is faithful, with no ambient normality assumption. -/
lemma quotientFixedRepresentation_injective :
    Function.Injective (quotientFixedRepresentation h hd h6 N hN) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  apply (QuotientGroup.eq_one_iff g).mpr
  have hg : g ∈ (fixedRepresentation h hd h6).ker := hq
  rwa [fixedRepresentation_ker h hd h6, ← hN] at hg

/-- Six-coordinate restriction intertwines the descended native action. -/
lemma fixedEquiv_quotient_equivariant (q : Stabilizer f ⧸ N)
    (v : fixedSpace (quotientRepresentation f) K) :
    fixedEquiv h hd h6 (quotientFixedRepresentation h hd h6 N hN q v) =
      BinaryPermutation.deletedRepresentation H (quotientCoordinateAction h N hN q)
        (fixedEquiv h hd h6 v) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact fixedEquiv_equivariant h hd h6 g v

include h hd h6

/-- The fixed space is five-dimensional by its explicit deleted-module equivalence. -/
lemma fixedSpace_finrank_five :
    Module.finrank (ZMod 2) (fixedSpace (quotientRepresentation f) K) = 5 := by
  rw [(fixedEquiv h hd h6).finrank_eq, BinaryPermutation.finrank_deleted, card_H]

end MathieuCode.Hexad.CocodeAction.SixPointModel
