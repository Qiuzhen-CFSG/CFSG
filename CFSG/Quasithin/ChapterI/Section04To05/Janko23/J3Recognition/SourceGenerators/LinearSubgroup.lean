module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.SourceGenerators
public import Theory.SpecificGroups.PSL2.BinaryFourFieldExtension

/-!
# The linear subgroup extracted from a field-extension embedding

An injective homomorphism from the genuine PSL₂(16) extension by fourth-power
Frobenius supplies its normal linear subgroup of order 4080 and its outside
involution. The induced conjugation is the specified field action. The image
of the extension is exactly the join of that subgroup and the involution
line. Applying Lagrange discharges the divisor 17 in the source-generator
order reduction.

The embedding is an explicit input. Its existence from `J3Type G` and
simplicity is the outstanding Thompson construction mentioned in
Aschbacher–Smith I.4.7(2), printed p.418. Neither this transport nor the
intrinsic extension model proves that source existence statement.
-/

namespace CFSG.Quasithin.Janko23.J3Recognition.LinearSubgroup

open Theory.PSL2
open BinaryFourFieldExtension

variable {G : Type*} [Group G]

/-- The actual image of the linear factor under an extension homomorphism. -/
@[expose] public noncomputable def linearSubgroup (f : Model →* G) : Subgroup G :=
  (f.comp linearInclusion).range

/-- An embedding gives the required equivalence with the genuine matrix quotient. -/
@[expose] public noncomputable def linearEquiv (f : Model →* G)
    (hf : Function.Injective f) : linearSubgroup f ≃* BinaryGroup 4 :=
  (MonoidHom.ofInjective (f := f.comp linearInclusion)
    (hf.comp SemidirectProduct.inl_injective)).symm

public theorem linearEquiv_symm_coe (f : Model →* G) (hf : Function.Injective f)
    (x : BinaryGroup 4) : ((linearEquiv f hf).symm x : G) = f (linearInclusion x) := rfl

public theorem linearSubgroup_card (f : Model →* G) (hf : Function.Injective f) :
    Nat.card (linearSubgroup f) = 4080 :=
  (Nat.card_congr (linearEquiv f hf).toEquiv).trans linear_card

public theorem involution_image_order (f : Model →* G) (hf : Function.Injective f) :
    orderOf (f involution) = 2 :=
  (orderOf_injective f hf involution).trans involution_order

public theorem involution_image_not_mem (f : Model →* G) (hf : Function.Injective f) :
    f involution ∉ linearSubgroup f := by
  rintro ⟨x, hx⟩
  exact involution_not_mem_linear ⟨x, hf hx⟩

/-- The conjugation formula uses the literal inclusion and fourth-power action. -/
public theorem conjugation_image (f : Model →* G) (x : BinaryGroup 4) :
    f involution * f (linearInclusion x) * (f involution)⁻¹ =
      f (linearInclusion (fieldAut fieldInvolution x)) := by
  simpa only [map_mul, map_inv] using congrArg f (conjugation x)

public theorem conjugation_equiv (f : Model →* G) (hf : Function.Injective f)
    (x : BinaryGroup 4) :
    f involution * ((linearEquiv f hf).symm x : G) * (f involution)⁻¹ =
      ((linearEquiv f hf).symm (fieldAut fieldInvolution x) : G) :=
  conjugation_image f x

public theorem involution_image_normalizes (f : Model →* G) :
    f involution ∈ Subgroup.normalizer (linearSubgroup f : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨fieldAut fieldInvolution y, (conjugation_image f y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨(fieldAut fieldInvolution).symm y, ?_⟩
    apply (MulAut.conj (f involution)).injective
    change f involution * f (linearInclusion ((fieldAut fieldInvolution).symm y)) *
      (f involution)⁻¹ = f involution * x * (f involution)⁻¹
    rw [conjugation_image, MulEquiv.apply_symm_apply]
    exact hy

public theorem range_eq_generated (f : Model →* G) :
    f.range = linearSubgroup f ⊔ Subgroup.zpowers (f involution) := by
  rw [MonoidHom.range_eq_map, ← generated, Subgroup.map_sup, MonoidHom.map_zpowers]
  rw [linearSubgroup, MonoidHom.range_comp]

public theorem generated_card (f : Model →* G) (hf : Function.Injective f) :
    Nat.card ↥(linearSubgroup f ⊔ Subgroup.zpowers (f involution)) = 8160 := by
  rw [← range_eq_generated f, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    model_card]

public theorem seventeen_dvd_card (f : Model →* G) (hf : Function.Injective f) :
    17 ∣ Nat.card G := by
  apply (show 17 ∣ 4080 by decide).trans
  rw [← linearSubgroup_card f hf]
  exact (linearSubgroup f).card_subgroup_dvd_card

variable [Finite G]

/-- Actual application to the parent's subgroup order reduction. The source
embedding, generating pair and order-243 subgroup remain explicit inputs. -/
public theorem card_lower_bound_of_embedding [Nontrivial G]
    (htype : J3Type G) (hgen : Sporadic.Janko3.RecognitionPresentation.HasGenerators G)
    (P : Subgroup G) (hP : Nat.card P = 243)
    (f : Model →* G) (hf : Function.Injective f) : 50232960 ≤ Nat.card G :=
  card_lower_bound_of_generators_of_subgroups htype hgen P (linearSubgroup f)
    hP (linearSubgroup_card f hf)

end CFSG.Quasithin.Janko23.J3Recognition.LinearSubgroup
