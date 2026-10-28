module

public import Theory.Representation.G2OrthogonalCover.Universal
public import Theory.Representation.G2OrthogonalCover.SylowFlag

/-!
# Sylow geometry in every binary cover of the natural G₂′ module

A map from the trace-zero orthogonal cover commuting with the literal natural
projection can kill only vectors in the scalar radical. Its restrictions to
the singular point and long-root plane are therefore injective. These images
remain complementary to the original central kernel in the corresponding
natural-space preimages, without giving the target kernel a field structure.

The fixed space of the derived group is exactly that kernel. The actual Sylow
fixed space and long-root displacement space transport through the same map,
using the paired conjugations already constructed for every derived Sylow.
The binary dimensions of the surviving complements are obtained by scalar
restriction, so all statements include the genuine G₂(2)′ endpoint.

Source: Aschbacher–Smith, Lemma I.2.3(1)(a),(c) and its quotient argument,
printed p.413 / PDF p.424 of the combined manuscript (1 March 2004).
-/

@[expose] public section
noncomputable section
open Representation Representation.OneCohomology
namespace Atlas.G2.Natural.OrthogonalCover
open SylowFlag
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The actual binary natural module has no nonzero derived-group fixed vector. -/
theorem binaryNatural_fixed_eq_bot : fixed (binaryNatural F) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨x, rfl⟩ := mk_surjective F v
  have hz : ambientCocycle F x.val = 0 := by
    rw [ambientCocycle_traceZero]
    apply Subtype.ext
    funext g
    exact sub_eq_zero.mpr (hv g)
  obtain ⟨a, ha⟩ := (ambientCocycle_eq_zero_iff F x.val).mp hz
  exact (mk_eq_zero_iff F x).mpr ⟨a, ha⟩

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (commutator (Model F)) W}
  (p : σ.IntertwiningMap (binaryNatural F))

/-- In every central natural cover the fixed space is exactly the original kernel. -/
theorem cover_fixed_eq_kernel (hp : IsCover p) : fixed σ = p.toLinearMap.ker := by
  apply le_antisymm _ hp.2.1
  intro w hw
  have hn : p w ∈ fixed (binaryNatural F) := by
    intro g
    rw [← p.isIntertwining, hw g]
  rw [binaryNatural_fixed_eq_bot] at hn
  exact hn

variable (f : (binaryAction F).IntertwiningMap σ)
  (hf : Function.Surjective f) (hover : ∀ x, p (f x) = mk F x)

include hover in
/-- Every compatible quotient kills only vectors in the scalar radical. -/
theorem quotient_kernel_le_scalar : f.toLinearMap.ker ≤ (scalarLine F).restrictScalars (ZMod 2) := by
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero (scalarLine F)).mp
  change mk F x = 0
  rw [← hover, show f x = 0 from hx, map_zero]

include hf hover in
/-- The scalar radical maps onto the literal kernel of the target projection. -/
theorem quotient_scalar_image :
    ((scalarLine F).restrictScalars (ZMod 2)).map f.toLinearMap = p.toLinearMap.ker := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change p (f x) = 0
    rw [hover]
    exact (Submodule.Quotient.mk_eq_zero (scalarLine F)).mpr hx
  · intro w hw
    obtain ⟨x, rfl⟩ := hf w
    refine ⟨x, ?_, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero (scalarLine F)).mp
    change mk F x = 0
    rw [← hover]
    exact hw

include hover in
/-- Subspaces complementary to the radical survive injectively in every cover. -/
theorem quotient_injective_on_complement (C : Submodule F (TraceZero F))
    (hC : Disjoint C (scalarLine F)) :
    Function.Injective (f.toLinearMap.domRestrict (C.restrictScalars (ZMod 2))) := by
  apply LinearMap.injective_domRestrict_iff.mpr
  exact ((Submodule.disjoint_restrictScalars_iff (ZMod 2)).mpr hC).mono_right
    (quotient_kernel_le_scalar F p f hover)

include hover in
/-- Their binary dimensions are unchanged; no field structure is imposed on the target cover. -/
theorem quotient_complement_finrank (C : Submodule F (TraceZero F))
    (hC : Disjoint C (scalarLine F)) :
    Module.finrank (ZMod 2) ((C.restrictScalars (ZMod 2)).map f.toLinearMap) =
      Module.finrank (ZMod 2) F * Module.finrank F C := by
  let : Module.Free F C := Module.Free.of_divisionRing (K := F) (V := C)
  rw [← LinearMap.range_domRestrict]
  rw [LinearMap.finrank_range_of_inj (quotient_injective_on_complement F p f hover C hC)]
  change Module.finrank (ZMod 2) C = _
  exact (Module.finrank_mul_finrank (ZMod 2) F C).symm

include hover in
/-- The surviving complement is disjoint from the target's original central kernel. -/
theorem quotient_complement_disjoint (C : Submodule F (TraceZero F))
    (hC : Disjoint C (scalarLine F)) :
    Disjoint ((C.restrictScalars (ZMod 2)).map f.toLinearMap) p.toLinearMap.ker := by
  apply Submodule.disjoint_def.mpr
  rintro w ⟨x, hx, rfl⟩ hw
  have hs : x ∈ scalarLine F := (Submodule.Quotient.mk_eq_zero (scalarLine F)).mp (by
    change mk F x = 0
    rw [← hover]
    exact hw)
  have hx0 : x = 0 := Submodule.disjoint_def.mp hC x hx hs
  rw [hx0, map_zero]

include hf hover in
/-- A compatible quotient maps a literal natural-space preimage to the same
preimage in the target, preserving its point or plane complement. -/
theorem quotient_preimage_complement (N : Submodule F (Space F))
    (C : Submodule F (TraceZero F))
    (hN : N.comap (mk F) = C ⊔ scalarLine F) :
    (N.restrictScalars (ZMod 2)).comap p.toLinearMap =
      (C.restrictScalars (ZMod 2)).map f.toLinearMap ⊔ p.toLinearMap.ker := by
  have hm := map_preimage_of_surjective (binaryProjection F) p f hf hover
    (N.restrictScalars (ZMod 2))
  rw [← hm]
  change ((N.comap (mk F)).restrictScalars (ZMod 2)).map f.toLinearMap = _
  rw [hN, Submodule.restrictScalars_sup, Submodule.map_sup,
    quotient_scalar_image F p f hf hover]

omit [CharP F 2] in
include hf in
/-- The root commutator calculation survives restriction of scalars and the
same actual covering map. -/
theorem quotient_root_commutator (g : commutator (Model F)) :
    (((singularPlane F).map (OrthogonalCover.action F g)).restrictScalars (ZMod 2)).map
        f.toLinearMap = Coinvariants.ker (σ.comp (movedRoot F g).subtype) := by
  let fR : Representation.IntertwiningMap ((binaryAction F).comp (movedRoot F g).subtype)
      (σ.comp (movedRoot F g).subtype) :=
    f.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun t x => LinearMap.congr_fun (f.isIntertwining' t.val) x)
  have he : Coinvariants.ker ((binaryAction F).comp (movedRoot F g).subtype) =
      ((singularPlane F).map (OrthogonalCover.action F g)).restrictScalars (ZMod 2) := by
    change Coinvariants.ker (restrictScalars (k := ZMod 2)
      ((OrthogonalCover.action F).comp (movedRoot F g).subtype)) = _
    rw [coinvariants_restrictScalars, movedRoot_commutator]
  rw [← he]
  exact map_coinvariants_of_surjective fR hf

include hf hover in
/-- The first preimage is the fixed space of the actual derived Sylow even in
an arbitrary binary cover. -/
theorem quotient_sylow_fixed (g : commutator (Model F)) :
    fixed (σ.comp (movedSylow F g).subtype) =
      ((movedLine F g).restrictScalars (ZMod 2)).comap p.toLinearMap := by
  apply le_antisymm
  · intro w hw
    change p w ∈ movedLine F g
    rw [← movedLine_fixed]
    intro t
    change binaryNatural F t.val (p w) = p w
    rw [← p.isIntertwining]
    exact congrArg p (hw t)
  · intro w hw t
    have hm := map_preimage_of_surjective (binaryProjection F) p f hf hover
      ((movedLine F g).restrictScalars (ZMod 2))
    obtain ⟨x, hx, rfl⟩ := hm.symm ▸ hw
    change σ t.val (f x) = f x
    rw [← f.isIntertwining]
    exact congrArg f (show OrthogonalCover.action F t.val x = x from
      (show x ∈ fixed ((OrthogonalCover.action F).comp (movedSylow F g).subtype) from
        (moved_cover_fixed F g).symm ▸ hx) t)

end Atlas.G2.Natural.OrthogonalCover
