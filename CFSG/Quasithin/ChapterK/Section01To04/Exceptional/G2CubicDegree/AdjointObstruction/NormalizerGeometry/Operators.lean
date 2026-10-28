module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.NormalizerGeometry.Density
public import Theory.Representation.FiniteFieldSemilinearDisplacement
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage

/-!
# Scalars, field actors, and the actual adjoint normalizer

The coordinate density theorem proves binary irreducibility and identifies the
additive centralizer with field scalars. Simplicity and a nontrivial root operator
prove faithfulness. We transport literal normalizer conjugation through that
faithful image and apply the proved inner-field description of G₂ automorphisms.
Every normalizer operator is then a scalar times the actual inner operator and
coefficient transport. For an involution, a trivial field component forces the
scalar to one. A nontrivial field component has order two; semilinear descent
gives fixed codimension exactly half the binary dimension, namely `7*r`.

No F-linearity of arbitrary normalizer elements is assumed. This calculation is
independent of the inner involution fixed-kernel calculation.
Source: GM04 II, Proposition 8.2 and Lemma 8.5, manuscript pp.53–56;
see `G2CubicDegree/Source.md` for the normalizer and scalar conventions.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction.NormalizerGeometry
open Atlas.G2 Atlas.G2.Restricted.Adjoint
attribute [local instance] ZMod.algebra RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
variable (F : Type*) [Field F] [CharP F 2]

open Representation Representation.BinaryOffender Subgroup
open Atlas.G2.Restricted

/-- The coordinates intertwine the literal binary adjoint action. -/
def binaryCoordinateEquiv : Representation.RepEquiv (adjointBinary F)
    (Representation.restrictScalars (k := ZMod 2) (Coordinates.action F)) where
  toLinearEquiv := (Coordinates.equiv F).restrictScalars (ZMod 2)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact (Coordinates.repEquiv F).isIntertwining g v

/-- Irreducibility on the actual derivation carrier after scalar restriction. -/
theorem binary_irreducible : Representation.IsIrreducible (adjointBinary F) :=
  (binaryCoordinateEquiv F).irreducible_euqiv.mpr (coordinates_binary_irreducible F)

/-- The additive centralizer on actual derivations is precisely the field scalars. -/
theorem centralizer_scalar (f : Adjoint.Space F →+ Adjoint.Space F)
    (hf : ∀ g v, f (Adjoint.action F g v) = Adjoint.action F g (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  let e := Coordinates.equiv F
  let f' := e.toAddEquiv.toAddMonoidHom.comp (f.comp e.symm.toAddEquiv.toAddMonoidHom)
  have he (g : Model F) (v : Adjoint.Space F) :
      e (Adjoint.action F g v) = Coordinates.action F g (e v) :=
    (Coordinates.repEquiv F).isIntertwining g v
  have he' (g : Model F) (v : Coordinates.Space F) :
      e.symm (Coordinates.action F g v) = Adjoint.action F g (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  obtain ⟨c, hc⟩ := coordinates_centralizer_scalar F f' (by
    intro g v
    change e (f (e.symm (Coordinates.action F g v))) = _
    rw [he', hf, he]
    rfl)
  refine ⟨c, fun v => e.injective ?_⟩
  simpa [f', map_smul] using hc (e v)

variable [Finite F]

/-- Simplicity and a nontrivial root operator prove faithfulness of the actual action. -/
theorem binary_faithful (hq : 2 < Nat.card F) : Function.Injective (adjointBinary F) := by
  let := Atlas.G2.isSimple hq
  let ρ := Representation.restrictScalars (k := ZMod 2) (Coordinates.action F)
  have hk : ρ.asGroupHom.ker = ⊥ := by
    rcases (inferInstance : ρ.asGroupHom.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hg : rootB (1 : F) ∈ ρ.asGroupHom.ker := h ▸ mem_top _
      have he : ρ (rootB 1) = 1 := congrArg Units.val hg
      have hv := congrArg (fun f : Module.End (ZMod 2) (Coordinates.Space F) =>
        f (Pi.single 3 1) 0) he
      simp [ρ, Representation.restrictScalars, Coordinates.action_rootB] at hv
  have hi : Function.Injective ρ := by
    intro g h he
    exact ρ.asGroupHom.ker_eq_bot_iff.mp hk (Units.ext he)
  intro g h he
  apply hi
  apply LinearMap.ext
  intro v
  have he' := LinearMap.congr_fun he ((Coordinates.equiv F).symm v)
  change Coordinates.action F g v = Coordinates.action F h v
  change Adjoint.action F g ((Coordinates.equiv F).symm v) =
    Adjoint.action F h ((Coordinates.equiv F).symm v) at he'
  have hh := congrArg (Coordinates.equiv F) he'
  have hequiv (k : Model F) (w : Adjoint.Space F) :
      Coordinates.equiv F (Adjoint.action F k w) =
        Coordinates.action F k (Coordinates.equiv F w) :=
    (Coordinates.repEquiv F).isIntertwining k w
  simpa only [hequiv, LinearEquiv.apply_symm_apply] using hh

/-- Actual normalizer conjugation, transported back along the faithful action image. -/
def normalizerAutomorphism (hq : 2 < Nat.card F) :
    linearNormalizer (adjointBinary F) →* MulAut (Model F) :=
  let hf : Function.Injective (adjointBinary F).asGroupHom :=
    fun _ _ h => binary_faithful F hq (congrArg Units.val h)
  let e : Model F ≃* actionImage (adjointBinary F) := MonoidHom.ofInjective hf
  (MulAut.congr e.symm).toMonoidHom.comp (actionImage (adjointBinary F)).normalizerMonoidHom

/-- The transported automorphism retains the original normalizer operator. -/
theorem normalizerAutomorphism_intertwines (hq : 2 < Nat.card F)
    (t : linearNormalizer (adjointBinary F)) (g : Model F) (v : Adjoint.Space F) :
    t.val.val (Adjoint.action F g v) =
      Adjoint.action F (normalizerAutomorphism F hq t g) (t.val.val v) := by
  let hf : Function.Injective (adjointBinary F).asGroupHom :=
    fun _ _ h => binary_faithful F hq (congrArg Units.val h)
  let e : Model F ≃* actionImage (adjointBinary F) := MonoidHom.ofInjective hf
  let t' : normalizer (actionImage (adjointBinary F) : Set (Module.End (ZMod 2) (Adjoint.Space F))ˣ) := ⟨t.val, t.property⟩
  have he : (adjointBinary F).asGroupHom (normalizerAutomorphism F hq t g) =
      t.val * (adjointBinary F).asGroupHom g * t.val⁻¹ := by
    change (e (e.symm ((actionImage (adjointBinary F)).normalizerMonoidHom t' (e g)))).val = _
    rw [e.apply_symm_apply]
    rfl
  have hh := congrArg (fun u : (Module.End (ZMod 2) (Adjoint.Space F))ˣ =>
    u.val (t.val.val v)) he
  have hinv : (t.val⁻¹).val (t.val.val v) = v := by
    change (t.val⁻¹ * t.val).val v = v
    rw [inv_mul_cancel]
    rfl
  change Adjoint.action F (normalizerAutomorphism F hq t g) (t.val.val v) =
    t.val.val (Adjoint.action F g ((t.val⁻¹).val (t.val.val v))) at hh
  rw [hinv] at hh
  exact hh.symm

local notation "V" => Adjoint.Space F

omit [CharP F 2] [Finite F] in
private theorem coefficient_one (v : V) :
    Adjoint.coefficientSemilinearEquiv F (1 : F ≃+* F) v = v := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  ext i
  rfl

/-- A literal normalizer operator over an inner-field automorphism differs only
by a field scalar from the specified inner and coefficient operators. -/
theorem normalizer_scalar_factor (hq : 2 < Nat.card F)
    (t : linearNormalizer (adjointBinary F)) (g : Model F) (σ : F ≃+* F)
    (ha : normalizerAutomorphism F hq t =
      MulAut.conj g * LieAutomorphismExtensions.fieldAction σ) :
    ∃ c : F, ∀ v : V, t.val.val v =
      c • Adjoint.action F g (Adjoint.coefficientSemilinearEquiv F σ v) := by
  let τ := Adjoint.coefficientSemilinearEquiv F σ
  have hc (h : Model F) (v : V) :
      τ.symm (Adjoint.action F (fieldEquiv σ h) v) =
        Adjoint.action F h (τ.symm v) := by
    apply τ.injective
    rw [τ.apply_symm_apply, Adjoint.coefficientSemilinearEquiv_action,
      τ.apply_symm_apply]
  have hg (h : Model F) (v : V) :
      Adjoint.action F g⁻¹ (Adjoint.action F (normalizerAutomorphism F hq t h) v) =
      Adjoint.action F (fieldEquiv σ h) (Adjoint.action F g⁻¹ v) := by
    have he : g⁻¹ * normalizerAutomorphism F hq t h = fieldEquiv σ h * g⁻¹ := by
      rw [ha]
      change g⁻¹ * (g * fieldEquiv σ h * g⁻¹) = _
      group
    simp only [← Module.End.mul_apply, ← map_mul, he]
  let f : V →+ V := τ.symm.toAddEquiv.toAddMonoidHom.comp
    ((Adjoint.action F g⁻¹).toAddMonoidHom.comp t.val.val.toAddMonoidHom)
  obtain ⟨c, hc'⟩ := centralizer_scalar F f (by
    intro h v
    change τ.symm (Adjoint.action F g⁻¹ (t.val.val (Adjoint.action F h v))) = _
    rw [normalizerAutomorphism_intertwines F hq t h v, hg, hc]
    rfl)
  refine ⟨σ c, fun v => ?_⟩
  have h := congrArg (fun w : V => Adjoint.action F g (τ w)) (hc' v)
  change Adjoint.action F g (τ (τ.symm (Adjoint.action F g⁻¹ (t.val.val v)))) = _ at h
  rw [τ.apply_symm_apply] at h
  simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply, LinearEquiv.map_smulₛₗ, map_smul] at h
  exact h

/-- Nontrivial coefficient involutions move exactly half the binary adjoint space. -/
theorem field_involution_codim (hq : 2 < Nat.card F)
    {r : ℕ} (hF : Nat.card F = 2 ^ r)
    (t : linearNormalizer (adjointBinary F)) (ht : t ^ 2 = 1)
    (z : Model F ⋊[LieAutomorphismExtensions.fieldAction] (F ≃+* F))
    (hz : LieAutomorphismExtensions.semilinearAction z = normalizerAutomorphism F hq t)
    (hσ : z.right ≠ 1) :
    fixedCodim (normalizerRepresentation (adjointBinary F)) (zpowers t) = 7 * r := by
  have hz2 : z ^ 2 = 1 := by
    apply LieAutomorphismExtensions.semilinearAction_injective hq
    rw [map_pow, hz, ← map_pow, ht, map_one, map_one]
  have hσ2 : z.right ^ 2 = 1 := congrArg SemidirectProduct.right hz2
  have ht1 : t ≠ 1 := by
    intro he
    have hz1 : z = 1 := by
      apply LieAutomorphismExtensions.semilinearAction_injective hq
      rw [hz, he, map_one, map_one]
    exact hσ (congrArg SemidirectProduct.right hz1)
  obtain ⟨c, hc⟩ := normalizer_scalar_factor F hq t z.left z.right hz.symm
  have hsemi (a : F) (v : V) :
      normalizerRepresentation (adjointBinary F) t (a • v) =
        z.right a • normalizerRepresentation (adjointBinary F) t v := by
    change t.val.val (a • v) = z.right a • t.val.val v
    rw [hc, hc, LinearEquiv.map_smulₛₗ, map_smul, smul_comm]
    rfl
  let : FiniteDimensional F V := (Coordinates.equiv F).symm.finiteDimensional
  have hh := Representation.FiniteFieldSemilinearDisplacement.fixedCodim_formula
    (normalizerRepresentation (adjointBinary F)) (by decide : 0 < 2)
    t (orderOf_eq_prime ht ht1) z.right (orderOf_eq_prime hσ2 hσ) hsemi
  have hdimF : Module.finrank (ZMod 2) F = r := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hF
  rw [hdimF, Adjoint.finrank] at hh
  omega

/-- If the field component is trivial, an involutory normalizer operator is inner.
The scalar factor is forced to one, rather than assumed absent. -/
theorem inner_involution_mem (hq : 2 < Nat.card F)
    (t : linearNormalizer (adjointBinary F)) (ht : t ^ 2 = 1)
    (z : Model F ⋊[LieAutomorphismExtensions.fieldAction] (F ≃+* F))
    (hz : LieAutomorphismExtensions.semilinearAction z = normalizerAutomorphism F hq t)
    (hσ : z.right = 1) :
    t ∈ (normalizerEmbedding (adjointBinary F)).range := by
  have hz2 : z ^ 2 = 1 := by
    apply LieAutomorphismExtensions.semilinearAction_injective hq
    rw [map_pow, hz, ← map_pow, ht, map_one, map_one]
  have hg2 : z.left ^ 2 = 1 := by
    have h := congrArg SemidirectProduct.left hz2
    simpa [pow_two, hσ] using h
  obtain ⟨c, hc⟩ := normalizer_scalar_factor F hq t z.left z.right hz.symm
  have htv (v : V) : t.val.val v = c • Adjoint.action F z.left v := by
    have he : Adjoint.coefficientSemilinearEquiv F z.right v = v :=
      (congrArg (fun σ : F ≃+* F => Adjoint.coefficientSemilinearEquiv F σ v) hσ).trans
        (coefficient_one F v)
    simpa only [he] using hc v
  have hs (v : V) : (c ^ 2) • v = v := by
    have he := congrArg (fun u : linearNormalizer (adjointBinary F) => u.val.val v) ht
    change t.val.val (t.val.val v) = v at he
    rw [htv, htv, map_smul, smul_smul, ← pow_two,
      ← Module.End.mul_apply, ← map_mul, ← pow_two, hg2, map_one,
      Module.End.one_apply] at he
    exact he
  have hc2 : c ^ 2 = 1 := by
    have he := congrArg (fun v : V => Coordinates.equiv F v 0)
      (hs ((Coordinates.equiv F).symm (Pi.single 0 1)))
    simpa only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply,
      smul_eq_mul, Pi.single_eq_same, mul_one] using he
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc2 with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  refine ⟨z.left, ?_⟩
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  change Adjoint.action F z.left v = t.val.val v
  simpa only [hc1, one_smul] using (htv v).symm

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction.NormalizerGeometry
