module
public import Theory.Representation.G2BinaryPointFlag
public import Theory.Representation.G2OrthogonalCover.Universal

/-!
# Displacements from the marked three-space in the binary natural module

The split-octonion norm polar form descends to the actual natural six-space.
Its coordinate form makes the marked three-space self-orthogonal. Thus every
actual G₂(2) actor fixing that three-space pointwise has its entire displacement
in the three-space. This applies to both the full group and its derived group.

Source/application: Aschbacher–Smith, Lemma 13.3.18, printed p.895, the
cross-displacement inclusion following pointwise centralization of V₃.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates Atlas.SplitOctonion
open OrthogonalCover

/-- The alternating natural form in the literal six coordinates. -/
noncomputable def pairing : W →ₗ[F] W →ₗ[F] F :=
  (naturalPairing F).compl₁₂ (equiv F).symm.toLinearMap (equiv F).symm.toLinearMap

theorem pairing_apply (v w : W) : pairing v w =
    v 0*w 5+v 5*w 0+v 1*w 4+v 4*w 1+v 2*w 3+v 3*w 2 := by
  simp [pairing,LinearMap.compl₁₂_apply,quotientClass,representative,normPolar]

theorem pairing_invariant (g : Model F) (v w : W) :
    pairing (Restricted.NaturalCoordinates.action F g v)
      (Restricted.NaturalCoordinates.action F g w)=pairing v w := by
  have hi (x y : Natural.Space F) :
      naturalPairing F (Natural.action F g x) (Natural.action F g y)=naturalPairing F x y := by
    obtain ⟨x,rfl⟩ := mk_surjective F x
    obtain ⟨y,rfl⟩ := mk_surjective F y
    simp only [action_mk,naturalPairing_mk,traceZeroAction_val,automorphism_normPolar]
  change naturalPairing F ((equiv F).symm (Restricted.NaturalCoordinates.action F g v))
    ((equiv F).symm (Restricted.NaturalCoordinates.action F g w))=_
  have ht (x : W) : (equiv F).symm (Restricted.NaturalCoordinates.action F g x)=
      Natural.action F g ((equiv F).symm x) := by
    apply (equiv F).injective
    rw [LinearEquiv.apply_symm_apply]
    exact ((repEquiv F).isIntertwining g ((equiv F).symm x)).symm.trans
      (congrArg (Restricted.NaturalCoordinates.action F g) ((equiv F).apply_symm_apply x)).symm
  rw [ht,ht]
  exact hi _ _

/-- The marked three-space is its own orthogonal complement. -/
theorem orthogonal_seed (v : W) : (∀w∈seed,pairing v w=0) ↔ v∈seed := by
  constructor
  · intro h
    have h0 := h (Pi.single 0 1) (by simp)
    have h1 := h (Pi.single 1 1) (by simp)
    have h2 := h (Pi.single 2 1) (by simp)
    simp [pairing_apply] at h0 h1 h2
    exact (mem_seed v).mpr ⟨h2,h1,h0⟩
  · intro hv w hw
    obtain ⟨v3,v4,v5⟩ := (mem_seed v).mp hv
    obtain ⟨w3,w4,w5⟩ := (mem_seed w).mp hw
    simp [pairing_apply,v3,v4,v5,w3,w4,w5]

/-- Fixing V₃ pointwise puts every actual natural displacement in V₃. -/
theorem displacement_mem_seed (g : Model F)
    (hg : ∀w∈seed,Restricted.NaturalCoordinates.action F g w=w) (v : W) :
    Restricted.NaturalCoordinates.action F g v-v∈seed := by
  apply (orthogonal_seed _).mp
  intro w hw
  have hi := pairing_invariant g v w
  rw [hg w hw] at hi
  rw [map_sub,LinearMap.sub_apply,hi,sub_self]
end Atlas.G2.Natural.BinaryPointFlag
