module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Structure
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Natural
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Nonsplit
public import Theory.Representation.Quotient

/-!
# Intrinsic quintet conjugation modules and their actual quotients

The core identifications transport the genuine hexacode translation actions
to the intrinsic kernels without changing their underlying native elements.
The inner four-space is irreducible and its two F4 coordinates intertwine the
pointwise distinguished-tetrad stabilizer with the natural SL2(4) action. Its
faithful quotient is identified with its image in the literal five-part S5.

The inner irreducibility discharges the only premise of the outer translation
indecomposability theorem. Equivariant core transport gives the exact
`kernelConjugation` conclusion consumed downstream. Since the elementary
core centralizes itself, this action descends to Q/O₂(Q), and then to S5 via
the actual five-part quotient; inflation preserves its subrepresentation
lattice and hence its indecomposability.

Source: Aschbacher--Smith H.14.3(2), printed p.397, setup on p.396. The
underlying native and licensed ATLAS comparisons, including the F4 model and
fixed-vector calculation, are in `Structure`, `Natural` and `Nonsplit`.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer Representation
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M22ChapterH.Quintet

private def subrepresentationsEquiv {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q V} {σ : Representation (ZMod 2) Q W}
    (e : Representation.Equiv ρ σ) : Subrepresentation ρ ≃o Subrepresentation σ where
  toFun A := {
    toSubmodule := A.toSubmodule.comap e.symm.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change e.symm (σ g v) ∈ A
      have he : e.symm (σ g v) = ρ g (e.symm v) := LinearMap.congr_fun (e.symm.isIntertwining' g) v
      rw [he]
      exact A.apply_mem_toSubmodule g hv }
  invFun A := {
    toSubmodule := A.toSubmodule.comap e.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change e (ρ g v) ∈ A
      have he : e (ρ g v) = σ g (e v) := LinearMap.congr_fun (e.isIntertwining' g) v
      rw [he]
      exact A.apply_mem_toSubmodule g hv }
  left_inv A := by
    ext v
    change e.symm (e v) ∈ A ↔ v ∈ A
    rw [e.symm_apply_apply]
  right_inv A := by
    ext v
    change e (e.symm v) ∈ A ↔ v ∈ A
    rw [e.apply_symm_apply]
  map_rel_iff' := by
    intro A B
    constructor
    · intro h v hv
      have hh := h (show e v ∈ A.toSubmodule.comap e.symm.toLinearMap by
        change e.symm (e v) ∈ A; simpa only [e.symm_apply_apply] using hv)
      change e.symm (e v) ∈ B at hh
      simpa only [e.symm_apply_apply] using hh
    · intro h v hv
      exact h hv

/-- The intrinsic core has the same literal elements as the outer translations. -/
def coreTranslationEquiv : Additive K ≃ₗ[ZMod 2] Additive outerTranslationGroup := by
  let e := (MulEquiv.subgroupCongr outerTranslations_eq_core.symm).toAdditive
  exact LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap 2) e.bijective

@[simp] theorem coreTranslationEquiv_apply (v : Additive K) :
    (coreTranslationEquiv v).toMul.val = v.toMul.val := rfl

def coreTranslationRepresentationEquiv :
    Representation.Equiv kernelConjugation outerTranslationConjugation :=
  .mk coreTranslationEquiv (by
    intro g
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl)

theorem innerTranslationGroup_eq_intersection : innerTranslationGroup = A0 :=
  congrArg (fun H : Subgroup m22PairStabilizer => H ⊓ L) outerTranslations_eq_core

/-- The intrinsic inner M22 core maps onto the inner intersection by the native embedding. -/
def innerCoreGroupEquiv : (m22InnerQuintetKernel m22SourceSextet) ≃* A0 :=
  ((MulEquiv.subgroupCongr innerTranslations_eq_core.symm).trans innerTranslationGroupEquiv).trans
    (MulEquiv.subgroupCongr innerTranslationGroup_eq_intersection)

@[simp] theorem innerCoreGroupEquiv_apply (g : m22InnerQuintetKernel m22SourceSextet) :
    (innerCoreGroupEquiv g).val = m22ToPairStabilizer g.val := rfl

instance innerCore_elementary : IsElementaryAbelian 2 (m22InnerQuintetKernel m22SourceSextet) where
  is_comm := ⟨fun a b => innerCoreGroupEquiv.injective (by
    simp only [map_mul]; exact mul_comm _ _)⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a =>
    innerCoreGroupEquiv.injective (by
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A0) (innerCoreGroupEquiv a))

/-- The inner transport also retains the native pair-stabilizer element. -/
def innerCoreTranslationEquiv : Additive A0 ≃ₗ[ZMod 2] Additive innerTranslationGroup := by
  let e := (MulEquiv.subgroupCongr innerTranslationGroup_eq_intersection.symm).toAdditive
  exact LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap 2) e.bijective

@[simp] theorem innerCoreTranslationEquiv_apply (v : Additive A0) :
    (innerCoreTranslationEquiv v).toMul.val = v.toMul.val := rfl

def innerCoreTranslationRepresentationEquiv :
    Representation.Equiv (innerConjugation innerInputs) innerTranslationConjugation :=
  .mk innerCoreTranslationEquiv (by
    intro g
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl)

theorem innerConjugation_isIrreducible :
    Representation.IsIrreducible (innerConjugation innerInputs) :=
  (subrepresentationsEquiv innerCoreTranslationRepresentationEquiv).isSimpleOrder_iff.mpr
    innerTranslationConjugation_isIrreducible

theorem kernelConjugation_indecomposable
    (A B : Subrepresentation kernelConjugation) (hAB : IsCompl A B) :
    A = ⊥ ∨ B = ⊥ := by
  let e := subrepresentationsEquiv coreTranslationRepresentationEquiv
  have h := outerTranslationConjugation_indecomposable
    innerTranslationConjugation_isIrreducible (e A) (e B) (e.isCompl_iff.mp hAB)
  simpa only [map_eq_bot_iff e] using h

theorem kernel_finrank : Module.finrank (ZMod 2) (Additive K) = 5 :=
  coreTranslationEquiv.finrank_eq.trans outerTranslationGroup_finrank

theorem innerIntersection_finrank : Module.finrank (ZMod 2) (Additive A0) = 4 :=
  innerCoreTranslationEquiv.finrank_eq.trans innerTranslationGroup_finrank

/-- Core coordinates are the same genuine F4 coordinates as the translations. -/
def innerCoreNaturalEquiv : Additive A0 ≃ₗ[ZMod 2] SL2FourNatural.V :=
  innerCoreTranslationEquiv.trans innerTranslationNaturalEquiv

theorem innerCore_natural (a : naturalActor) (v : Additive A0) :
    innerCoreNaturalEquiv (innerConjugation innerInputs a.val v) =
      SL2FourNatural.action (naturalActorModelEquiv (QuotientGroup.mk a))
        (innerCoreNaturalEquiv v) := by
  change innerTranslationNaturalEquiv
    (innerCoreTranslationRepresentationEquiv (innerConjugation innerInputs a.val v)) = _
  have he : innerCoreTranslationRepresentationEquiv
      (innerConjugation innerInputs a.val v) =
      innerTranslationConjugation a.val (innerCoreTranslationRepresentationEquiv v) :=
    LinearMap.congr_fun (innerCoreTranslationRepresentationEquiv.isIntertwining' a.val) v
  rw [he]
  exact innerTranslation_natural a (innerCoreTranslationEquiv v)

/-- Coordinates on the canonical field of four elements for the actual inner core. -/
def innerCoreStandardEquiv : Additive A0 ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2) :=
  innerCoreTranslationEquiv.trans innerTranslationStandardEquiv

theorem innerCore_standard_natural (a : naturalActor) (v : Additive A0) :
    innerCoreStandardEquiv (innerConjugation innerInputs a.val v) =
      specialLinearNatural 2 (naturalActorStandardEquiv (QuotientGroup.mk a))
        (innerCoreStandardEquiv v) := by
  have he : innerCoreTranslationEquiv (innerConjugation innerInputs a.val v) =
      innerTranslationConjugation a.val (innerCoreTranslationEquiv v) :=
    LinearMap.congr_fun (innerCoreTranslationRepresentationEquiv.isIntertwining' a.val) v
  change innerTranslationStandardEquiv
    (innerCoreTranslationEquiv (innerConjugation innerInputs a.val v)) = _
  rw [he]
  exact innerTranslation_standard_natural a (innerCoreTranslationEquiv v)

/-- The geometric actor's translation kernel is its intersection with O2(Q). -/
theorem naturalActorTranslations_eq_core : naturalActorTranslations =
    (pCore 2 Q).comap naturalActor.subtype := by
  rw [← naturalActorProjection_kernel]
  ext a
  obtain ⟨x, rfl⟩ := naturalActorEquiv.surjective a
  change naturalActorProjection (naturalActorEquiv x) = 1 ↔
    (naturalActorEquiv x).val ∈ pCore 2 Q
  rw [naturalActorProjection_equiv, naturalActorEquiv_coe,
    ← partAction_ker, Structure.Native.part_kernel]
  change x.right = 1 ↔ (naturalActorInclusion x).val ∈ outerTranslationGroup
  constructor
  · intro hx
    have he : x = SemidirectProduct.inl x.left := by
      rw [← SemidirectProduct.inl_left_mul_inr_right x, hx, map_one, mul_one]
      rfl
    rw [he, naturalActorInclusion_inl]
    exact (naturalTranslation x.left).property.1
  · intro hx
    have hs : (naturalAffineEquiv (Atlas.Codes.tetradPointAffineInclusion naturalIndex x)).val ∈
        Sextet.sourceCore := by
      rw [← naturalActorInclusion_coe]
      exact hx
    obtain ⟨w, hw⟩ := Sextet.sourceTranslationEquiv.surjective
      ⟨(naturalAffineEquiv (Atlas.Codes.tetradPointAffineInclusion naturalIndex x)).val, hs⟩
    have he : naturalAffineEquiv (SemidirectProduct.inl w) =
        naturalAffineEquiv (Atlas.Codes.tetradPointAffineInclusion naturalIndex x) := by
      apply Subtype.ext
      rw [naturalAffineEquiv_translation, hw]
    have hr := congrArg SemidirectProduct.right (naturalAffineEquiv.injective he)
    apply Subtype.ext
    apply Subtype.ext
    exact hr.symm

theorem naturalActor_fivePart_kernel :
    (NaturalQuotient.q.comp naturalActor.subtype).ker = naturalActorTranslations := by
  rw [naturalActorTranslations_eq_core, ← partAction_ker,
    ← NaturalQuotient.q_ker_eq_partAction_ker]
  rfl

/-- The actual subgroup of the five-part S5, rather than an abstract A5 tag. -/
abbrev naturalFivePartGroup := (NaturalQuotient.q.comp naturalActor.subtype).range

def naturalActorFivePartEquiv :
    (naturalActor ⧸ naturalActorTranslations) ≃* naturalFivePartGroup :=
  (QuotientGroup.quotientMulEquivOfEq naturalActor_fivePart_kernel.symm).trans
    (QuotientGroup.quotientKerEquivRange (NaturalQuotient.q.comp naturalActor.subtype))

@[simp] theorem naturalActorFivePartEquiv_mk (a : naturalActor) :
    (naturalActorFivePartEquiv (QuotientGroup.mk a)).val = NaturalQuotient.q a.val := rfl

def naturalFivePartModelEquiv : naturalFivePartGroup ≃* SL2FourNatural.SL :=
  naturalActorFivePartEquiv.symm.trans naturalActorModelEquiv

theorem innerCore_fivePart_natural (a : naturalActor) (v : Additive A0) :
    innerCoreNaturalEquiv (innerConjugation innerInputs a.val v) =
      SL2FourNatural.action
        (naturalFivePartModelEquiv (naturalActorFivePartEquiv (QuotientGroup.mk a)))
        (innerCoreNaturalEquiv v) := by
  change _ = SL2FourNatural.action
    (naturalActorModelEquiv (naturalActorFivePartEquiv.symm
      (naturalActorFivePartEquiv (QuotientGroup.mk a)))) _
  rw [naturalActorFivePartEquiv.symm_apply_apply]
  exact innerCore_natural a v

/-- The elementary core acts trivially on itself by conjugation. -/
theorem twoCore_le_kernelConjugation_ker : pCore 2 Q ≤ kernelConjugation.ker := by
  intro g hg
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  change g.val * v.toMul.val * g.val⁻¹ = v.toMul.val
  have hgK : g.val ∈ K := ⟨g, hg, rfl⟩
  have hc : g.val * v.toMul.val = v.toMul.val * g.val :=
    congrArg (fun k : K => k.val) (mul_comm (⟨g.val, hgK⟩ : K) v.toMul)
  rw [hc, mul_inv_cancel_right]

/-- The intrinsic quotient acts on the actual five-dimensional core. -/
def kernelQuotientConjugation : Representation (ZMod 2) (Q ⧸ pCore 2 Q) (Additive K) :=
  Representation.quotientOfLEKer kernelConjugation (pCore 2 Q) twoCore_le_kernelConjugation_ker

@[simp] theorem kernelQuotientConjugation_mk (g : Q) :
    kernelQuotientConjugation (QuotientGroup.mk' (pCore 2 Q) g) = kernelConjugation g := rfl

/-- The outer S5 action is transported through the literal five-part quotient. -/
def kernelS5Conjugation : Representation (ZMod 2) (Equiv.Perm (Fin 5)) (Additive K) :=
  kernelQuotientConjugation.comp quotientEquiv.symm.toMonoidHom

@[simp] theorem kernelS5Conjugation_q (g : Q) :
    kernelS5Conjugation (NaturalQuotient.q g) = kernelConjugation g := by
  rw [← quotientEquiv_mk]
  change kernelQuotientConjugation (quotientEquiv.symm (quotientEquiv _)) = _
  rw [quotientEquiv.symm_apply_apply, kernelQuotientConjugation_mk]

theorem kernelS5Conjugation_comp :
    kernelS5Conjugation.comp NaturalQuotient.q = kernelConjugation := by
  apply MonoidHom.ext
  intro g
  exact kernelS5Conjugation_q g

/-- The five-dimensional S5-module has no decomposition into two nonzero summands. -/
theorem kernelS5Conjugation_indecomposable
    (A B : Subrepresentation kernelS5Conjugation) (hAB : IsCompl A B) :
    A = ⊥ ∨ B = ⊥ := by
  have hi : ∀ U W : Subrepresentation (kernelS5Conjugation.comp NaturalQuotient.q),
      IsCompl U W → U = ⊥ ∨ W = ⊥ := by
    rw [kernelS5Conjugation_comp]
    exact kernelConjugation_indecomposable
  let e := Representation.inflationSubrepresentationOrderIso
    NaturalQuotient.q q_surjective kernelS5Conjugation
  have h := hi (e.symm A) (e.symm B) (e.symm.isCompl_iff.mp hAB)
  simpa only [map_eq_bot_iff e.symm] using h

end Sporadic.Mathieu.M22ChapterH.Quintet
