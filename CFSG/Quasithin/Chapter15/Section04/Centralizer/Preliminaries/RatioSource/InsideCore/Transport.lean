module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.Setup
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.InsideCore.SourceImplications
public import Theory.Representation.BinaryOffender.SmallRatioTransport

/-!
# The intrinsic module and the D.1 action image

The quotient M₀/C_M₀(V) is identified with the actual conjugation image by
`actionImageEquiv`. The inclusion of intrinsic V in G induces a binary linear
equivalence, and conjugation on quotient representatives proves equivariance.
Fixed-space codimensions and quadratic actors then transport the ratio bound;
the contragredient equivalence transports the dual-FF alternative.

Both applications retain the exact quotient map and representation consumed
by `MaximalPrimeFive.Earlier1542Four`. They are used by the inside-core case
split, rather than assuming a bound on a separately chosen representation.

Source: Aschbacher–Smith, D.1.5 and 15.4.2(4), printed pp.177 and 1156.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
open InsideCore
universe u
variable {G : Type u} [Group G]
variable {T : Sylow 2 G} {M₀ M : Subgroup G} {V : Subgroup M₀}

/-- The original intrinsic V and its embedded image have the same binary coordinates. -/
noncomputable def LocalHypotheses.moduleImageEquiv (l : LocalHypotheses T M₀ M V) :
    letI := l.reduced.elementary
    letI := IsElementaryAbelian.map (p := 2) (A := V) M₀.subtype
    Additive V ≃ₗ[ZMod 2] Additive (V.map M₀.subtype) := by
  let := l.reduced.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) M₀.subtype
  let e := (V.equivMapOfInjective M₀.subtype M₀.subtype_injective).toAdditive
  exact { e with map_smul' := ZMod.map_smul e }

/-- The literal quotient-to-image map intertwines the two conjugation actions. -/
theorem LocalHypotheses.actionImage_equivariant (l : LocalHypotheses T M₀ M V) :
    letI := l.reduced.normal
    letI := l.reduced.elementary
    letI := IsElementaryAbelian.map (p := 2) (A := V) M₀.subtype
    let ρ := Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ∀ g v, l.moduleImageEquiv (ρ g v) =
      imageRepresentation M₀ (V.map M₀.subtype) l.normalizes
        (l.actionImageEquiv g) (l.moduleImageEquiv v) := by
  let := l.reduced.normal
  let := l.reduced.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) M₀.subtype
  intro ρ g v
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (centralizer (V : Set M₀)) g
  apply Additive.toMul.injective
  apply Subtype.ext
  change (((ρ (QuotientGroup.mk' _ m) v).toMul : M₀) : G) = _
  rw [Representation.NormalElementaryQuotient.representation_apply]
  rfl

private theorem quadratic_bound_transport
    {D E W X : Type*} [Group D] [Group E] [Finite D] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D W) (σ : Representation (ZMod 2) E X)
    (e : D ≃* E) (f : W ≃ₗ[ZMod 2] X)
    (hf : ∀ g v, f (ρ g v) = σ (e g) (f v))
    (hσ : quadraticRatio σ ≤ 2) : quadraticRatio ρ ≤ 2 := by
  let τ := σ.comp e.toMonoidHom
  have hf' : ∀ g w, f.symm (τ g w) = ρ g (f.symm w) := by
    intro g w
    apply f.injective
    change f (f.symm (σ (e g) w)) = _
    rw [f.apply_symm_apply, hf, f.apply_symm_apply]
  obtain ⟨A, hA, hq, hc⟩ := (quadraticRatio_le_two_iff τ).mp
    (quadraticRatio_comp_equiv_le_two σ e hσ)
  apply (quadraticRatio_le_two_iff ρ).mpr
  refine ⟨A, hA, quadratic_of_equivariant_surjection τ ρ f.symm.toLinearMap
    f.symm.surjective hf' A hq, ?_⟩
  have he := fixedCodim_map_equivariant τ ρ (MonoidHom.id D) f.symm hf' A
  rw [Subgroup.map_id] at he
  exact he ▸ hc

private theorem dual_ff_transport
    {D E W X : Type*} [Group D] [Group E]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D W) (σ : Representation (ZMod 2) E X)
    (e : D ≃* E) (f : W ≃ₗ[ZMod 2] X)
    (hf : ∀ g v, f (ρ g v) = σ (e g) (f v))
    (hσ : IsFFModule σ.dual) : IsFFModule ρ.dual := by
  apply hσ.map_equivariant σ.dual ρ.dual e.symm.toMonoidHom e.symm.injective f.dualMap
  intro g φ
  ext v
  change φ (σ g⁻¹ (f v)) = φ (f (ρ (e.symm g)⁻¹ v))
  rw [hf, e.map_inv, e.apply_symm_apply]


/-- A quadratic bound for D.1's action image holds for the original quotient. -/
theorem LocalHypotheses.quadraticRatio_le_two_of_image [Finite G]
    (l : LocalHypotheses T M₀ M V) :
    letI := l.reduced.normal
    letI := l.reduced.elementary
    letI := IsElementaryAbelian.map (p := 2) (A := V) M₀.subtype
    quadraticRatio (imageRepresentation M₀ (V.map M₀.subtype) l.normalizes) ≤ 2 →
    quadraticRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  let := l.reduced.normal
  let := l.reduced.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) M₀.subtype
  exact quadratic_bound_transport _ _ l.actionImageEquiv l.moduleImageEquiv
    l.actionImage_equivariant

/-- The dual-FF alternative transports through the actual quotient and module maps. -/
theorem LocalHypotheses.dualFF_of_image
    (l : LocalHypotheses T M₀ M V) :
    letI := l.reduced.normal
    letI := l.reduced.elementary
    letI := IsElementaryAbelian.map (p := 2) (A := V) M₀.subtype
    IsFFModule (imageRepresentation M₀ (V.map M₀.subtype) l.normalizes).dual →
    IsFFModule (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).dual := by
  let := l.reduced.normal
  let := l.reduced.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) M₀.subtype
  exact dual_ff_transport _ _ l.actionImageEquiv l.moduleImageEquiv
    l.actionImage_equivariant

end CFSG.Quasithin.Chapter15.Section04.RatioSource
