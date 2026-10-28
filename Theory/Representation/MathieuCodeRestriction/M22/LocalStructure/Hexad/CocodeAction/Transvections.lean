module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.Transvections.Quotients

/-!
# Full hexad transvections on the quotient cocode

The canonical iterated-quotient equivalence transports the earlier full M24
transvection action to the quotient by the fixed space of the actual hexad
kernel. Octad parity descends to a surjective functional with kernel exactly
W/U. The kernel is isomorphic to the additive group of this axis, its action
is faithful, and its image consists of every map x ↦ x + parity(x) • a.

The isomorphism respects literal stabilizer conjugation. The induced axis
action kills the relative kernel and therefore factors through the actual
stabilizer/kernel quotient. The embedded axis is also identified canonically
with the literal quotient of W by U, retaining the quotient map on vectors.

The full-transvection inputs concern the native eleven-dimensional M24 cocode;
`RestrictionInput` supplies the earlier kernel marking and H.14 displacement.
This is a complete conditional transfer, not a proof of those earlier inputs.

Source: Aschbacher--Smith, H.15.2(6), printed pp.398--399,
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.Hexad.CocodeAction.Transvections
variable {G : Type*} [Group G]
variable {f : G →* m22PairStabilizer} {K : Subgroup G} {O : Octad}
variable (h : RestrictionInput f K O)
variable (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
  fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)

variable (ht : AmbientTransvectionInput O)

/-- Genuine octad intersection parity on the quotient by its fixed space. -/
def ambientParity : (Cocode ⧸ ambientFixed O) →ₗ[ZMod 2] ZMod 2 :=
  (ambientFixed O).liftQ (CocodeOctad.octadParity O)
    (ht.span_eq_parity ▸ ht.fixed_le_span)

@[simp] theorem ambientParity_mk (v : Cocode) :
    ambientParity ht ((ambientFixed O).mkQ v) = CocodeOctad.octadParity O v := rfl

theorem ambientParity_ker : (ambientParity ht).ker = ambientAxis O := by
  rw [ambientParity, Submodule.ker_liftQ, ← ht.span_eq_parity]

/-- Octad parity descended through the pair-line quotient and then through U. -/
def parity : (M22Cocode ⧸ fixed f K) →ₗ[ZMod 2] ZMod 2 :=
  (ambientParity ht).comp (quotientEquiv h hd).symm.toLinearMap

@[simp] theorem parity_quotientEquiv (x : Cocode ⧸ ambientFixed O) :
    parity h hd ht (quotientEquiv h hd x) = ambientParity ht x := by
  simp only [parity, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

@[simp] theorem parity_mk (v : Cocode) :
    parity h hd ht ((fixed f K).mkQ (m22PairLine.mkQ v)) = CocodeOctad.octadParity O v := by
  rw [← quotientEquiv_mk h hd, parity_quotientEquiv, ambientParity_mk]

theorem parity_surjective : Function.Surjective (parity h hd ht) := by
  intro c
  obtain ⟨v, hv⟩ := CocodeOctad.octadParity_surjective O c
  exact ⟨(fixed f K).mkQ (m22PairLine.mkQ v), (parity_mk h hd ht v).trans hv⟩

theorem parity_ker : (parity h hd ht).ker = axis f K := by
  rw [parity, LinearMap.ker_comp, ambientParity_ker,
    ← Submodule.map_equiv_eq_comap_symm, quotientEquiv_map_axis]

include h hd ht in
theorem fixed_le_span : fixed f K ≤ span f K := by
  rw [fixed_eq_map h hd, span, h.fixedSpaceSpan_eq_map hd]
  exact Submodule.map_mono ht.fixed_le_span

/-- Every element of the actual kernel is identified with its translation
parameter in W/U, with multiplication becoming addition. -/
def transvectionEquiv : K ≃* Multiplicative (axis f K) :=
  (kernelEquiv h).trans (ht.kernelEquiv.trans
    (AddEquiv.toMultiplicative (axisEquiv h hd).toAddEquiv))

@[simp] theorem transvectionEquiv_coe (a : K) :
    (transvectionEquiv h hd ht a).toAdd.val =
      quotientEquiv h hd (ht.kernelEquiv (kernelEquiv h a)).toAdd.val := rfl

/-- The full prescribed shear formula on the actual quotient representation. -/
theorem kernel_action (a : K) (x : M22Cocode ⧸ fixed f K) :
    quotientAction h ⟨a.val, kernel_le h a.property⟩ x =
      x + parity h hd ht x • (transvectionEquiv h hd ht a).toAdd.val := by
  obtain ⟨v, rfl⟩ := (fixed f K).mkQ_surjective x
  obtain ⟨v, rfl⟩ := m22PairLine.mkQ_surjective v
  change (fixed f K).mkQ (m22PairLine.mkQ (cocodeRepresentation (f a.val).val v)) = _
  have he := congrArg (quotientEquiv h hd) (ht.action (kernelEquiv h a) v)
  simpa only [map_add, map_smul, quotientEquiv_mk, kernelEquiv_coe,
    parity_mk, transvectionEquiv_coe] using he

/-- Every parameter occurs, and these are exactly the induced linear maps. -/
theorem full_image (T : Module.End (ZMod 2) (M22Cocode ⧸ fixed f K)) :
    (∃ a : K, quotientAction h ⟨a.val, kernel_le h a.property⟩ = T) ↔
      ∃ b : axis f K, ∀ x, T x = x + parity h hd ht x • b.val := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(transvectionEquiv h hd ht a).toAdd, kernel_action h hd ht a⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := (transvectionEquiv h hd ht).surjective (Multiplicative.ofAdd b)
    refine ⟨a, LinearMap.ext fun x => ?_⟩
    rw [kernel_action h hd ht, hb, ha]
    rfl

/-- Conjugation is the induced stabilizer action on the prescribed axis. -/
theorem transvectionEquiv_conjugation (g : stabilizer f O) (a : K) :
    (transvectionEquiv h hd ht (kernelConj _ _ (normalizes h) g a)).toAdd.val =
      quotientAction h g (transvectionEquiv h hd ht a).toAdd.val := by
  rw [transvectionEquiv_coe, kernelEquiv_conj, ht.conjugation,
    quotientEquiv_equivariant, transvectionEquiv_coe]

/-- The axis is invariant under the literal stabilizer action. -/
def axisSubrepresentation : Subrepresentation (quotientAction h) where
  toSubmodule := axis f K
  apply_mem_toSubmodule g x hx := by
    obtain ⟨a, ha⟩ := (transvectionEquiv h hd ht).surjective
      (Multiplicative.ofAdd (⟨x, hx⟩ : axis f K))
    have he : (transvectionEquiv h hd ht a).toAdd.val = x :=
      congrArg (fun b : Multiplicative (axis f K) => b.toAdd.val) ha
    rw [← he, ← transvectionEquiv_conjugation h hd ht]
    exact (transvectionEquiv h hd ht _).toAdd.property

abbrev axisAction : Representation (ZMod 2) (stabilizer f O) (axis f K) :=
  (axisSubrepresentation h hd ht).toRepresentation

theorem axisAction_conjugation (g : stabilizer f O) (a : K) :
    (transvectionEquiv h hd ht (kernelConj _ _ (normalizes h) g a)).toAdd =
      axisAction h hd ht g (transvectionEquiv h hd ht a).toAdd := by
  apply Subtype.ext
  exact transvectionEquiv_conjugation h hd ht g a

/-- The relative kernel acts trivially on W/U. -/
theorem kernel_le_axisAction_ker :
    K.subgroupOf (stabilizer f O) ≤ (axisAction h hd ht).ker := by
  intro a ha
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  change quotientAction h a b.val = b.val
  have he := kernel_action h hd ht (⟨a.val, ha⟩ : K) b.val
  have hp : parity h hd ht b.val = 0 := by
    have hb : b.val ∈ (parity h hd ht).ker := (parity_ker h hd ht).symm ▸ b.property
    exact hb
  simpa only [hp, zero_smul, add_zero] using he

include h in
/-- Normality is only inside the stabilizer. -/
theorem relativeKernelNormal : (K.subgroupOf (stabilizer f O)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (normalizes h)

/-- The action on W/U factors through the actual stabilizer/kernel quotient. -/
def axisQuotientAction :
    letI := relativeKernelNormal h
    Representation (ZMod 2)
      (stabilizer f O ⧸ K.subgroupOf (stabilizer f O)) (axis f K) := by
  letI := relativeKernelNormal h
  exact QuotientGroup.lift _ (axisAction h hd ht) (kernel_le_axisAction_ker h hd ht)

@[simp] theorem axisQuotientAction_mk (g : stabilizer f O) (b : axis f K) :
    axisQuotientAction h hd ht (QuotientGroup.mk g) b = axisAction h hd ht g b := rfl

/-- The group identification is an isomorphism for the quotient action: the
left action is literal conjugation, the right is the action induced on W/U. -/
theorem quotient_conjugation (g : stabilizer f O) (a : K) :
    (transvectionEquiv h hd ht (kernelConj _ _ (normalizes h) g a)).toAdd =
      axisQuotientAction h hd ht (QuotientGroup.mk g) (transvectionEquiv h hd ht a).toAdd :=
  axisAction_conjugation h hd ht g a

/-- The descended functional is invariant under the actual stabilizer. -/
theorem parity_invariant (g : stabilizer f O) (x : M22Cocode ⧸ fixed f K) :
    parity h hd ht (quotientAction h g x) = parity h hd ht x := by
  obtain ⟨v, rfl⟩ := (fixed f K).mkQ_surjective x
  obtain ⟨v, rfl⟩ := m22PairLine.mkQ_surjective v
  change parity h hd ht ((fixed f K).mkQ
    (m22PairLine.mkQ (cocodeRepresentation (f g.val).val v))) = _
  rw [parity_mk, parity_mk]
  exact CocodeOctad.octadParity_invariant O (stabilizerMap (f := f) (O := O) g) v

include hd ht in
/-- The quotient action of the kernel is faithful, not merely surjective
onto the transvection group. -/
theorem kernel_action_faithful : Function.Injective
    (fun a : K => quotientAction h ⟨a.val, kernel_le h a.property⟩) := by
  intro a b hab
  obtain ⟨x, hx⟩ := parity_surjective h hd ht 1
  have he := LinearMap.congr_fun hab x
  rw [kernel_action h hd ht, kernel_action h hd ht, hx, one_smul, one_smul] at he
  apply (transvectionEquiv h hd ht).injective
  exact congrArg Multiplicative.ofAdd (Subtype.ext (add_left_cancel he))

/-- Multiplication in the kernel is addition of its prescribed axis parameters. -/
theorem transvectionEquiv_mul (a b : K) :
    (transvectionEquiv h hd ht (a * b)).toAdd =
      (transvectionEquiv h hd ht a).toAdd + (transvectionEquiv h hd ht b).toAdd :=
  congrArg Multiplicative.toAdd ((transvectionEquiv h hd ht).map_mul a b)

/-- The embedded axis is canonically the literal subquotient W/U. -/
def spanQuotientEquivAxis :
    ((span f K) ⧸ (fixed f K).comap (span f K).subtype) ≃ₗ[ZMod 2] axis f K :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [LinearMap.ker_submoduleMap, Submodule.ker_mkQ])).trans
      (((fixed f K).mkQ.submoduleMap (span f K)).quotKerEquivOfSurjective
        ((fixed f K).mkQ.submoduleMap_surjective (span f K)))

@[simp] theorem spanQuotientEquivAxis_mk (w : span f K) :
    (spanQuotientEquivAxis (f := f) (K := K)
      (((fixed f K).comap (span f K).subtype).mkQ w)).val = (fixed f K).mkQ w.val := by
  rfl

/-- The earlier equivariant identification makes the ambient axis a literal
subrepresentation of the octad stabilizer's quotient action. -/
def ambientAxisSubrepresentation : Subrepresentation (ambientAction O) where
  toSubmodule := ambientAxis O
  apply_mem_toSubmodule g x hx := by
    obtain ⟨a, ha⟩ := ht.kernelEquiv.surjective
      (Multiplicative.ofAdd (⟨x, hx⟩ : ambientAxis O))
    have he : (ht.kernelEquiv a).toAdd.val = x :=
      congrArg (fun b : Multiplicative (ambientAxis O) => b.toAdd.val) ha
    rw [← he, ← ht.conjugation]
    exact (ht.kernelEquiv _).toAdd.property

abbrev ambientAxisAction : Representation (ZMod 2) (octadStabilizer O) (ambientAxis O) :=
  (ambientAxisSubrepresentation ht).toRepresentation

/-- Equivariance of the actual isomorphism between the two axis modules. -/
theorem axisEquiv_equivariant (g : stabilizer f O) (a : ambientAxis O) :
    axisEquiv h hd (ambientAxisAction ht (stabilizerMap (f := f) (O := O) g) a) =
      axisAction h hd ht g (axisEquiv h hd a) := by
  apply Subtype.ext
  exact quotientEquiv_equivariant h hd g a.val

/-- The same identification with the literal quotient of W by the included U. -/
def literalTransvectionEquiv :
    K ≃* Multiplicative ((span f K) ⧸ (fixed f K).comap (span f K).subtype) :=
  (transvectionEquiv h hd ht).trans
    (AddEquiv.toMultiplicative (spanQuotientEquivAxis (f := f) (K := K)).symm.toAddEquiv)

/-- The literal quotient identification retains the parameter in V/U. -/
@[simp] theorem literalTransvectionEquiv_axis (a : K) :
    spanQuotientEquivAxis (literalTransvectionEquiv h hd ht a).toAdd =
      (transvectionEquiv h hd ht a).toAdd :=
  (spanQuotientEquivAxis (f := f) (K := K)).apply_symm_apply _

include hd ht in
/-- Each nonidentity kernel element fixes precisely the prescribed axis. -/
theorem kernel_fixed_iff (a : K) (ha : a ≠ 1) (x : M22Cocode ⧸ fixed f K) :
    quotientAction h ⟨a.val, kernel_le h a.property⟩ x = x ↔ x ∈ axis f K := by
  have hb : (transvectionEquiv h hd ht a).toAdd.val ≠ 0 := by
    intro hz
    apply ha
    apply (transvectionEquiv h hd ht).injective
    rw [map_one]
    exact congrArg Multiplicative.ofAdd (Subtype.ext hz)
  rw [kernel_action h hd ht]
  constructor
  · intro he
    have hs : parity h hd ht x • (transvectionEquiv h hd ht a).toAdd.val = 0 :=
      add_left_cancel (he.trans (add_zero x).symm)
    have hp : parity h hd ht x = 0 := (smul_eq_zero.mp hs).resolve_right hb
    rw [← parity_ker h hd ht]
    exact hp
  · intro hx
    have hp : parity h hd ht x = 0 := by
      rw [← parity_ker h hd ht] at hx
      exact hx
    rw [hp, zero_smul, add_zero]

/-- The induced action on V/U agrees with the original quotient cocode action
on representatives. -/
@[simp] theorem quotientAction_mk (g : stabilizer f O) (v : M22Cocode) :
    quotientAction h g ((fixed f K).mkQ v) =
      (fixed f K).mkQ (quotientRepresentation f g.val v) := rfl

end MathieuCode.Hexad.CocodeAction.Transvections
