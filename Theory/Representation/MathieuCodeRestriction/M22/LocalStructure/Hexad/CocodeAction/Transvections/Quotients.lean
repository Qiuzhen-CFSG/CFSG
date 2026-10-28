module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.FixedSpaces
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Hyperplane
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Canonical quotients for the hexad transvection transfer

The pair line lies in the ambient octad-kernel fixed space. The third
isomorphism theorem and exact fixed-space lifting identify the quotient by
that fixed space with the corresponding quotient of the M22 cocode. This
identification intertwines the literal stabilizer actions and carries the
image of the ambient fixed-space span onto the hexad axis.

`AmbientTransvectionInput` specifies the permitted earlier M24 full action
and conjugation identification, entirely on the native M24 cocode and octad
pointwise kernel. It contains no assertion about the M22 quotient action.

Source: Aschbacher--Smith, H.15.2(6), printed pp.398--399,
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.Hexad.CocodeAction.Transvections

section General
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Fixed vectors are stable under a relative normalizer. -/
def relativeFixed (ρ : Representation (ZMod 2) G V) (H K : Subgroup G)
    (hn : H ≤ Subgroup.normalizer (K : Set G)) : Subrepresentation (ρ.comp H.subtype) where
  toSubmodule := fixedSpace ρ K
  apply_mem_toSubmodule g v hv a := by
    have ha : g.val⁻¹ * a.val * g.val ∈ K := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
        (hn (H.inv_mem g.property)) a.val).mp a.property
    change ρ a.val (ρ g.val v) = ρ g.val v
    calc
      _ = ρ g.val (ρ (g.val⁻¹ * a.val * g.val) v) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      _ = ρ g.val v := congrArg (ρ g.val) (hv ⟨_, ha⟩)

/-- Conjugation inside the kernel, without declaring it ambient normal. -/
def kernelConj (H K : Subgroup G) (hn : H ≤ Subgroup.normalizer (K : Set G))
    (g : H) (a : K) : K :=
  ⟨g.val * a.val * g.val⁻¹, (Subgroup.mem_normalizer_iff.mp (hn g.property) a.val).mp a.property⟩

end General

abbrev ambientFixed (O : Octad) : Submodule (ZMod 2) Cocode := fixedSpace cocodeRepresentation (octadPointwiseKernel O)
abbrev ambientSpan (O : Octad) : Submodule (ZMod 2) Cocode := fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O)
abbrev ambientAxis (O : Octad) : Submodule (ZMod 2) (Cocode ⧸ ambientFixed O) := (ambientSpan O).map (ambientFixed O).mkQ

theorem ambient_kernel_le (O : Octad) : octadPointwiseKernel O ≤ octadStabilizer O := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

theorem ambient_normalizes (O : Octad) :
    octadStabilizer O ≤ Subgroup.normalizer (octadPointwiseKernel O : Set M24) := by
  have h := (LinearFourCore.action O).ker.le_normalizer_map (octadStabilizer O).subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

abbrev ambientAction (O : Octad) :
    Representation (ZMod 2) (octadStabilizer O) (Cocode ⧸ ambientFixed O) :=
  (relativeFixed cocodeRepresentation _ _ (ambient_normalizes O)).quotientRepresentation

/-- The earlier full M24 transvection theorem and its conjugation identification.
Every carrier in this input is the original eleven-dimensional cocode or the
literal octad pointwise kernel. -/
structure AmbientTransvectionInput (O : Octad) where
  fixed_le_span : ambientFixed O ≤ ambientSpan O
  span_eq_parity : ambientSpan O = (CocodeOctad.octadParity O).ker
  kernelEquiv : octadPointwiseKernel O ≃* Multiplicative (ambientAxis O)
  action : ∀ (a : octadPointwiseKernel O) (v : Cocode),
    (ambientFixed O).mkQ (cocodeRepresentation a.val v) =
      (ambientFixed O).mkQ v + CocodeOctad.octadParity O v • (kernelEquiv a).toAdd.val
  conjugation : ∀ (g : octadStabilizer O) (a : octadPointwiseKernel O),
    (kernelEquiv (kernelConj _ _ (ambient_normalizes O) g a)).toAdd.val =
      ambientAction O g (kernelEquiv a).toAdd.val

variable {G : Type*} [Group G]
variable {f : G →* m22PairStabilizer} {K : Subgroup G} {O : Octad}

abbrev stabilizer (f : G →* m22PairStabilizer) (O : Octad) : Subgroup G :=
  (octadStabilizer O).comap (m22PairStabilizer.subtype.comp f)
abbrev fixed (f : G →* m22PairStabilizer) (K : Subgroup G) : Submodule (ZMod 2) M22Cocode :=
  fixedSpace (quotientRepresentation f) K
abbrev span (f : G →* m22PairStabilizer) (K : Subgroup G) : Submodule (ZMod 2) M22Cocode :=
  fixedSpaceSpan (quotientRepresentation f) K
abbrev axis (f : G →* m22PairStabilizer) (K : Subgroup G) :
    Submodule (ZMod 2) (M22Cocode ⧸ fixed f K) :=
  (span f K).map (fixed f K).mkQ

variable (h : RestrictionInput f K O)

/-- The actual inclusion into M24 on the relative hexad stabilizer. -/
def stabilizerMap : stabilizer f O →* octadStabilizer O :=
  (m22PairStabilizer.subtype.comp f).restrict (fun _ ha => ha)

/-- The specified image and injectivity identify the actual kernels. -/
def kernelEquiv : K ≃* octadPointwiseKernel O :=
  (K.equivMapOfInjective (m22PairStabilizer.subtype.comp f)
    (Subtype.val_injective.comp h.injective)).trans (MulEquiv.subgroupCongr h.kernel_image)

include h

@[simp] theorem kernelEquiv_coe (a : K) :
    (kernelEquiv h a).val = (f a.val).val := rfl

theorem kernel_mem_iff (a : G) : a ∈ K ↔ (f a).val ∈ octadPointwiseKernel O := by
  rw [← h.kernel_image]
  constructor
  · exact Subgroup.mem_map_of_mem _
  · rintro ⟨b, hb, he⟩
    exact (Subtype.val_injective.comp h.injective) he ▸ hb

theorem kernel_le : K ≤ stabilizer f O := by
  intro a ha
  exact ambient_kernel_le O ((kernel_mem_iff h a).mp ha)

theorem normalizes : stabilizer f O ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro a
  rw [kernel_mem_iff h, kernel_mem_iff h]
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    MonoidHom.comp_apply, Subgroup.subtype_apply] using
    Subgroup.mem_normalizer_iff.mp (ambient_normalizes O hg) (f a).val

abbrev quotientAction : Representation (ZMod 2) (stabilizer f O) (M22Cocode ⧸ fixed f K) :=
  (relativeFixed (quotientRepresentation f) _ _ (normalizes h)).quotientRepresentation

@[simp] theorem kernelEquiv_conj (g : stabilizer f O) (a : K) :
    kernelEquiv h (kernelConj _ _ (normalizes h) g a) =
      kernelConj _ _ (ambient_normalizes O) (stabilizerMap (f := f) (O := O) g)
        (kernelEquiv h a) := by
  apply Subtype.ext
  simp only [kernelEquiv_coe, kernelConj, map_mul, map_inv]
  rfl

variable (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
  fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)

theorem pairLine_le_ambientFixed : m22PairLine ≤ ambientFixed O := by
  rw [ambientFixed, ← h.kernel_image, ← fixedSpace_comp_map]
  exact pairLine_le_fixedSpace f K

include hd in
theorem fixed_eq_map : fixed f K = (ambientFixed O).map m22PairLine.mkQ := by
  simpa only [h.kernel_image] using h.fixedSpace_eq_map hd K le_rfl

/-- The canonical third-isomorphism equivalence; its map is induced by the
literal pair-line quotient, not chosen from equal dimensions. -/
def quotientEquiv : (Cocode ⧸ ambientFixed O) ≃ₗ[ZMod 2] (M22Cocode ⧸ fixed f K) :=
  (Submodule.quotientQuotientEquivQuotient m22PairLine (ambientFixed O)
    (pairLine_le_ambientFixed h)).symm.trans
      (Submodule.quotEquivOfEq _ _ (fixed_eq_map h hd).symm)

@[simp] theorem quotientEquiv_mk (v : Cocode) :
    quotientEquiv h hd ((ambientFixed O).mkQ v) =
      (fixed f K).mkQ (m22PairLine.mkQ v) := rfl

theorem quotientEquiv_equivariant (g : stabilizer f O) (x : Cocode ⧸ ambientFixed O) :
    quotientEquiv h hd (ambientAction O (stabilizerMap (f := f) (O := O) g) x) =
      quotientAction h g (quotientEquiv h hd x) := by
  obtain ⟨v, rfl⟩ := (ambientFixed O).mkQ_surjective x
  rfl

theorem quotientEquiv_map_axis :
    (ambientAxis O).map (quotientEquiv h hd).toLinearMap = axis f K := by
  rw [axis, span, h.fixedSpaceSpan_eq_map hd]
  change ((ambientSpan O).map (ambientFixed O).mkQ).map _ = _
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  rfl

/-- The induced equivalence carries precisely W0/U0 onto W/U. -/
def axisEquiv : ambientAxis O ≃ₗ[ZMod 2] axis f K :=
  (quotientEquiv h hd).ofSubmodules _ _ (quotientEquiv_map_axis h hd)

@[simp] theorem axisEquiv_coe (a : ambientAxis O) :
    (axisEquiv h hd a).val = quotientEquiv h hd a.val := rfl

end MathieuCode.Hexad.CocodeAction.Transvections
