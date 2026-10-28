module

public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer
public import Theory.Representation.SL3OddNaturalNormalizer.Index

/-!
# Recovering the field from the doubled natural normalizer

Conjugation by a binary normalizer preserves the full multiplicity algebra
`M₂(F)` and hence its center. The published commutant calculation identifies
that center with the original field scalars, producing a genuine coefficient
automorphism and the semilinearity equation. An involution induces a coefficient
automorphism whose square is one. The field automorphism group has odd order
when the binary field degree is odd, so that automorphism is trivial.

This proves field linearity, including over `F₂`. Extracting tensor factors and
normalizing their determinants are separate steps in normalizer coverage.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.5.9(3) and B.5.10(2), printed pp.107–109.
-/

public section
namespace Representation.SL3DoubledNaturalOffenders
open Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

private def conjugate (b : Ambient F) :
    Module.End (ZMod 2) (Space F) ≃+* Module.End (ZMod 2) (Space F) :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv b).conjRingEquiv

private theorem conjugate_apply (b : Ambient F) (f : Module.End (ZMod 2) (Space F)) :
    conjugate b f = (b : Module.End (ZMod 2) (Space F)) * f *
      (↑b⁻¹ : Module.End (ZMod 2) (Space F)) := rfl

private theorem conjugate_commutes (b : Ambient F) (hb : b ∈ normalizer F)
    (f : Module.End (ZMod 2) (Space F))
    (hf : ∀ g : SL F, f * representation F g = representation F g * f) :
    ∀ g : SL F, conjugate b f * representation F g =
      representation F g * conjugate b f := by
  intro g
  obtain ⟨h, hh⟩ := (Subgroup.mem_normalizer_iff''.mp hb
    ((representation F).asGroupHom g)).mp ⟨g, rfl⟩
  have he : representation F h = (↑b⁻¹ : Module.End (ZMod 2) (Space F)) *
      representation F g * (b : Module.End (ZMod 2) (Space F)) :=
    congrArg Units.val hh
  have hc := congrArg (fun t : Module.End (ZMod 2) (Space F) =>
    (b : Module.End (ZMod 2) (Space F)) * t *
      (↑b⁻¹ : Module.End (ZMod 2) (Space F))) (hf h)
  simpa [he, conjugate_apply, mul_assoc] using hc

/-- Conjugation by an actual normalizer preserves the full multiplicity algebra. -/
theorem normalizer_conjugate_multiplicity (b : Ambient F) (hb : b ∈ normalizer F)
    (c : Matrix (Fin 2) (Fin 2) F) :
    ∃ d : Matrix (Fin 2) (Fin 2) F,
      (b : Module.End (ZMod 2) (Space F)) * multiplicity F c *
        (↑b⁻¹ : Module.End (ZMod 2) (Space F)) = multiplicity F d := by
  apply centralizer_multiplicity
  intro g v
  exact LinearMap.congr_fun (conjugate_commutes b hb (multiplicity F c)
    (multiplicity_commutes F c) g) v

private def scalar : F →ₐ[ZMod 2] Module.End (ZMod 2) (Space F) :=
  Algebra.lsmul (ZMod 2) (ZMod 2) (Space F)

private theorem scalar_apply (a : F) (v : Space F) : scalar a v = a • v := rfl

private theorem scalar_commutes_representation (a : F) (g : SL F) :
    scalar a * representation F g = representation F g * scalar a := by
  apply LinearMap.ext
  intro v
  funext i j
  change (a • g.val.mulVec (v i)) j = g.val.mulVec (a • v i) j
  rw [Matrix.mulVec_smul]

private theorem scalar_commutes_multiplicity (a : F) (c : Matrix (Fin 2) (Fin 2) F) :
    scalar a * multiplicity F c = multiplicity F c * scalar a := by
  apply LinearMap.ext
  intro v
  funext i j
  simp [scalar_apply, Module.End.mul_apply, multiplicity, smul_smul]
  ring

private theorem conjugate_scalar (b : Ambient F) (hb : b ∈ normalizer F) (a : F) :
    ∃ d : F, ∀ v, conjugate b (scalar a) v = d • v := by
  apply commutant_center_scalar
  · intro g v
    exact LinearMap.congr_fun (conjugate_commutes b hb (scalar a)
      (scalar_commutes_representation a) g) v
  · intro c
    obtain ⟨d, hd⟩ := normalizer_conjugate_multiplicity b⁻¹ ((normalizer F).inv_mem hb) c
    have hh := congrArg (conjugate b) (scalar_commutes_multiplicity a d).symm
    have hcancel : conjugate b (multiplicity F d) = multiplicity F c := by
      rw [← hd, conjugate_apply]
      simp [mul_assoc]
    simpa only [map_mul, hcancel] using hh

/-- The binary normalizer acts semilinearly over the recovered field. -/
theorem normalizer_semilinear [Finite F] (b : Ambient F) (hb : b ∈ normalizer F) :
    ∃ σ : F ≃+* F, ∀ (c : F) (v : Space F),
      (b : Module.End (ZMod 2) (Space F)) (c • v) =
        σ c • (b : Module.End (ZMod 2) (Space F)) v := by
  let φ : F → F := fun c => conjugate b (scalar c) (fun _ _ => 1) 0 0
  have hφ (c : F) (v : Space F) : conjugate b (scalar c) v = φ c • v := by
    obtain ⟨d, hd⟩ := conjugate_scalar b hb c
    have he : φ c = d := by simp [φ, hd]
    exact he ▸ hd v
  let φhom : F →+* F :=
    { toFun := φ
      map_one' := by simp [φ, map_one]
      map_mul' := by
        intro a c
        change conjugate b (scalar (a * c)) (fun _ _ => 1) 0 0 = φ a * φ c
        rw [map_mul, map_mul, Module.End.mul_apply, hφ, hφ]
        simp
      map_zero' := by simp [φ]
      map_add' := by
        intro a c
        change conjugate b (scalar (a + c)) (fun _ _ => 1) 0 0 = φ a + φ c
        simp only [map_add, LinearMap.add_apply, Pi.add_apply]
        rfl }
  refine ⟨RingEquiv.ofBijective φhom
    ⟨φhom.injective, Finite.surjective_of_injective φhom.injective⟩, fun c v => ?_⟩
  have he := hφ c ((b : Module.End (ZMod 2) (Space F)) v)
  change (b : Module.End (ZMod 2) (Space F))
    (c • (↑b⁻¹ : Module.End (ZMod 2) (Space F))
      ((b : Module.End (ZMod 2) (Space F)) v)) = _ at he
  change (b : Module.End (ZMod 2) (Space F)) (c • v) = φ c • _
  simpa [← Module.End.mul_apply] using he

/-- Over an odd-degree binary field, every normalizer involution is field linear. -/
theorem normalizer_involution_linear [Finite F] {m : ℕ} (hodd : Odd m)
    (hc : Nat.card F = 2 ^ m) (b : Ambient F) (hb : b ∈ normalizer F)
    (hb2 : b ^ 2 = 1) (c : F) (v : Space F) :
    (b : Module.End (ZMod 2) (Space F)) (c • v) =
      c • (b : Module.End (ZMod 2) (Space F)) v := by
  obtain ⟨σ, hσ⟩ := normalizer_semilinear b hb
  have hsq (v : Space F) : (b : Module.End (ZMod 2) (Space F))
      ((b : Module.End (ZMod 2) (Space F)) v) = v := by
    have he := congrArg Units.val hb2
    exact LinearMap.congr_fun he v
  have hσ2 : σ ^ 2 = 1 := by
    ext a
    change σ (σ a) = a
    have he := hsq (a • (fun (_ : Fin 2) (_ : Fin 3) => (1 : F)))
    rw [hσ, hσ, hsq] at he
    simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using congrFun (congrFun he 0) 0
  have hσm : σ ^ m = 1 := by
    rw [← SL3OddNaturalNormalizer.binaryFieldAut_card hc]
    exact pow_card_eq_one'
  obtain ⟨k, hk⟩ := hodd
  have hσone : σ = 1 := by
    rw [hk, pow_add, pow_mul, hσ2] at hσm
    simpa using hσm
  simpa only [hσone, RingAut.one_apply] using hσ c v

/-- The source elementary actor acts field linearly on the marked doubled module.
This supplies the field-linearity premise for extracting its tensor factors. -/
theorem normalizer_elementary_linear [Finite F] {m : ℕ} (hodd : Odd m)
    (hc : Nat.card F = 2 ^ m) (A : Subgroup (Ambient F))
    (hA : BinaryOffender.IsElementaryTwo A) (hAN : A ≤ normalizer F)
    (a : A) (c : F) (v : Space F) :
    (a.val : Module.End (ZMod 2) (Space F)) (c • v) =
      c • (a.val : Module.End (ZMod 2) (Space F)) v := by
  let : IsElementaryAbelian 2 A := hA.2
  exact normalizer_involution_linear hodd hc a.val (hAN a.property)
    (elemPow_eq_one_of_isElementaryAbelian a.val a.property) c v

end Representation.SL3DoubledNaturalOffenders
