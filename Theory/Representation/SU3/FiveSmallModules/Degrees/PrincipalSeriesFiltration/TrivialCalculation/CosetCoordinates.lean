module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.InductionConvention

/-!
# Trivial induction and the literal left-coset module

The map `[t ⊗ a] ↦ a δ_(t⁻¹B)` identifies the coinvariant induction
quotient with the left-coset permutation module. Its inverse is defined on
cosets using the checked subgroup relation. A group equivalence preserving
the actual subgroup transports this permutation module, and finite support
can then be replaced by functions without changing the action.

These are the convention and model-identification steps for the trivial
SU₃(5) principal series used in the approach to Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, p.10.
-/

@[expose] public section

open scoped MonoidAlgebra
open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
variable {K G : Type*} [Field K] [Group G] (B : Subgroup G)

noncomputable abbrev cosetAction := ofMulAction K G (G ⧸ B)

/-- The base-coset vector is fixed by the inducing subgroup. -/
theorem coset_base_fixed (b : B) :
    cosetAction (K := K) B b (MonoidAlgebra.single (QuotientGroup.mk 1) 1) =
      ((1 : B →* Kˣ) b : K) • MonoidAlgebra.single (QuotientGroup.mk 1) 1 := by
  rw [ofMulAction_single]
  have hb : (b : G) • (QuotientGroup.mk 1 : G ⧸ B) = QuotientGroup.mk 1 := by
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    simp
  simp [hb]

noncomputable def toCosets :
    (ind B.subtype (scalarCharacter (1 : B →* Kˣ))).IntertwiningMap (cosetAction B) :=
  inducedMap B 1 (cosetAction B) (MonoidAlgebra.single (QuotientGroup.mk 1) 1)
    (coset_base_fixed B)

@[simp] theorem toCosets_mk (g : G) (a : K) :
    toCosets B (IndV.mk B.subtype (scalarCharacter (1 : B →* Kˣ)) g a) =
      MonoidAlgebra.single (QuotientGroup.mk g⁻¹) a := by
  simp [toCosets, inducedMap, inductionLift, ofMulAction_single]

noncomputable def cosetValue : G ⧸ B → IndV B.subtype (scalarCharacter (1 : B →* Kˣ)) :=
  Quotient.lift (fun g : G => IndV.mk B.subtype (scalarCharacter (1 : B →* Kˣ)) g⁻¹ 1)
    (by
      intro g h hh
      let b : B := ⟨g⁻¹ * h, QuotientGroup.leftRel_apply.mp hh⟩
      have he : h⁻¹ = ((b⁻¹ : B) : G) * g⁻¹ := by simp [b, mul_inv_rev, mul_assoc]
      rw [he, induced_mk_subgroup_mul]
      simp)

noncomputable def fromCosets :
    K[G ⧸ B] →ₗ[K] IndV B.subtype (scalarCharacter (1 : B →* Kˣ)) :=
  (MonoidAlgebra.basis (G ⧸ B) K).constr K (cosetValue B)

@[simp] theorem fromCosets_single_one (x : G ⧸ B) :
    fromCosets (K := K) B (MonoidAlgebra.single x 1) = cosetValue B x :=
  (MonoidAlgebra.basis (G ⧸ B) K).constr_basis K (cosetValue B) x

@[simp] theorem fromCosets_single (g : G) (a : K) :
    fromCosets B (MonoidAlgebra.single (QuotientGroup.mk g) a) =
      IndV.mk B.subtype (scalarCharacter (1 : B →* Kˣ)) g⁻¹ a := by
  have hs : MonoidAlgebra.single (QuotientGroup.mk (s := B) g) a =
      a • MonoidAlgebra.single (QuotientGroup.mk g) (1 : K) := by simp
  rw [hs, map_smul, fromCosets_single_one]
  change a • IndV.mk B.subtype (scalarCharacter (1 : B →* Kˣ)) g⁻¹ 1 = _
  rw [← map_smul]
  simp

noncomputable def inductionCosetEquiv :
    IndV B.subtype (scalarCharacter (1 : B →* Kˣ)) ≃ₗ[K] K[G ⧸ B] := by
  have hl : (fromCosets (K := K) B).comp (toCosets B).toLinearMap = LinearMap.id := by
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro a
    change fromCosets B (toCosets B (IndV.mk B.subtype (scalarCharacter (1 : B →* Kˣ)) g a)) = _
    rw [toCosets_mk, fromCosets_single, inv_inv]
    rfl
  have hr : (toCosets (K := K) B).toLinearMap.comp (fromCosets B) = LinearMap.id := by
    apply (MonoidAlgebra.basis (G ⧸ B) K).ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H g => change toCosets B (fromCosets B (MonoidAlgebra.single (QuotientGroup.mk g) 1)) = _
             rw [fromCosets_single, toCosets_mk, inv_inv]
             rfl
  exact { (toCosets B).toLinearMap with
    invFun := fromCosets B
    left_inv := LinearMap.congr_fun hl
    right_inv := LinearMap.congr_fun hr }

theorem inductionCosetEquiv_equivariant (g : G)
    (v : IndV B.subtype (scalarCharacter (1 : B →* Kˣ))) :
    inductionCosetEquiv B (ind B.subtype (scalarCharacter (1 : B →* Kˣ)) g v) =
      cosetAction B g (inductionCosetEquiv B v) :=
  (toCosets B).isIntertwining _ _ g v

/-- The inversion required by Mathlib's induction convention. -/
@[simp] theorem inductionCosetEquiv_mk (g : G) (a : K) :
    inductionCosetEquiv B (IndV.mk B.subtype (scalarCharacter (1 : B →* Kˣ)) g a) =
      MonoidAlgebra.single (QuotientGroup.mk g⁻¹) a :=
  toCosets_mk B g a

variable {H : Type*} [Group H] (C : Subgroup H)

def cosetEquiv (e : G ≃* H) (he : ∀ g, e g ∈ C ↔ g ∈ B) : (G ⧸ B) ≃ (H ⧸ C) where
  toFun := Quotient.map e (by
    intro g h hh
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul, he]
    exact QuotientGroup.leftRel_apply.mp hh)
  invFun := Quotient.map e.symm (by
    intro g h hh
    apply QuotientGroup.leftRel_apply.mpr
    rw [← he, map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply]
    exact QuotientGroup.leftRel_apply.mp hh)
  left_inv x := by induction x using QuotientGroup.induction_on; simp
  right_inv x := by induction x using QuotientGroup.induction_on; simp

@[simp] theorem cosetEquiv_smul (e : G ≃* H) (he : ∀ g, e g ∈ C ↔ g ∈ B)
    (g : G) (x : G ⧸ B) : cosetEquiv B C e he (g • x) = e g • cosetEquiv B C e he x := by
  induction x using QuotientGroup.induction_on with
  | H x => change QuotientGroup.mk (e (g * x)) = QuotientGroup.mk (e g * e x)
           rw [map_mul]

noncomputable def cosetModuleEquiv (e : G ≃* H) (he : ∀ g, e g ∈ C ↔ g ∈ B) :
    K[G ⧸ B] ≃ₗ[K] K[H ⧸ C] := MonoidAlgebra.mapDomainLinearEquiv K K (cosetEquiv B C e he)

theorem cosetModuleEquiv_equivariant (e : G ≃* H) (he : ∀ g, e g ∈ C ↔ g ∈ B)
    (g : G) (v : K[G ⧸ B]) :
    cosetModuleEquiv B C e he (cosetAction B g v) =
      cosetAction C (e g) (cosetModuleEquiv B C e he v) := by
  have hl : (cosetModuleEquiv (K := K) B C e he).toLinearMap.comp (cosetAction B g) =
      (cosetAction C (e g)).comp (cosetModuleEquiv B C e he).toLinearMap := by
    apply (MonoidAlgebra.basis (G ⧸ B) K).ext
    intro x
    change cosetModuleEquiv B C e he (cosetAction B g (MonoidAlgebra.single x 1)) = _
    simp [cosetModuleEquiv, ofMulAction_single]
  exact LinearMap.congr_fun hl v
end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation

namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
section Permutation
variable {K G Ω : Type*} [Field K] [Group G] [MulAction G Ω]

def functionAction : Representation K G (Ω → K) where
  toFun g :=
    { toFun := fun v x => v (g⁻¹ • x)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext v x; simp
  map_mul' g h := by ext v x; simp [mul_smul]

noncomputable def functionEquiv [Finite Ω] : K[Ω] ≃ₗ[K] (Ω → K) :=
  (MonoidAlgebra.coeffLinearEquiv K).trans (Finsupp.linearEquivFunOnFinite K K Ω)

theorem functionEquiv_equivariant [Finite Ω] (g : G) (v : K[Ω]) :
    functionEquiv (ofMulAction K G Ω g v) = functionAction g (functionEquiv v) := by
  ext x
  exact coeff_ofMulAction g v x

end Permutation
end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
