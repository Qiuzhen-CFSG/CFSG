module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.InductionConvention
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Transport

/-!
# Transport of the literal principal series along a group-subgroup isomorphism

A compatible pair of group isomorphisms and matching subgroup characters
induces a linear equivalence of the actual coinvariant induction quotients.
It sends `[g ⊗ a]` to `[e(g) ⊗ a]`. The inverse pair provides its inverse;
the group actions intertwine with the same group map. The construction uses
the checked inverse-character relation in `InductionConvention`.

Consequently every invariant subspace and its simple literal quotient can
be transported while retaining the original coefficient field. This is the
field-model comparison needed by the principal-series approach to
Guralnick–Malle, Proposition 4.3, p.10, and Aschbacher–Smith K.2, p.453.
-/

public noncomputable section

namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
variable {K G H : Type*} [Field K] [Group G] [Group H]

noncomputable def inductionPairMap (B : Subgroup G) (C : Subgroup H)
    (f : G →* H) (b : B →* C) (hb : ∀ x : B, f x = b x)
    (χ : B →* Kˣ) (ψ : C →* Kˣ) (hχ : ∀ x, ψ (b x) = χ x) :
    (ind B.subtype (scalarCharacter χ)).IntertwiningMap
      ((ind C.subtype (scalarCharacter ψ)).comp f) := by
  let j : (scalarCharacter χ).IntertwiningMap
      (((ind C.subtype (scalarCharacter ψ)).comp f).comp B.subtype) :=
    ⟨IndV.mk C.subtype (scalarCharacter ψ) 1, by
      intro x
      apply LinearMap.ext
      intro a
      change IndV.mk C.subtype (scalarCharacter ψ) 1 ((χ x : K) * a) =
        ind C.subtype (scalarCharacter ψ) (f x) (IndV.mk C.subtype (scalarCharacter ψ) 1 a)
      rw [ind_mk, one_mul, hb]
      simpa only [map_inv, Units.val_inv_eq_inv_val, inv_inv, hχ, mul_one, Subgroup.coe_inv] using
        (induced_mk_subgroup_mul C ψ (b x)⁻¹ 1 a).symm⟩
  exact inductionLift B.subtype (scalarCharacter χ) _ j

@[simp] theorem inductionPairMap_mk (B : Subgroup G) (C : Subgroup H)
    (f : G →* H) (b : B →* C) (hb : ∀ x : B, f x = b x)
    (χ : B →* Kˣ) (ψ : C →* Kˣ) (hχ : ∀ x, ψ (b x) = χ x)
    (g : G) (a : K) :
    inductionPairMap B C f b hb χ ψ hχ (IndV.mk B.subtype (scalarCharacter χ) g a) =
      IndV.mk C.subtype (scalarCharacter ψ) (f g) a := by
  simp only [inductionPairMap, inductionLift_mk, MonoidHom.comp_apply,
    IntertwiningMap.coe_mk, map_inv, ind_mk, inv_inv, one_mul]

/-- A compatible isomorphism of group-subgroup pairs identifies the literal
induction quotients, sending each identity tensor to its specified image. -/
noncomputable def inductionPairEquiv (B : Subgroup G) (C : Subgroup H)
    (e : G ≃* H) (b : B ≃* C) (hb : ∀ x : B, e x = b x)
    (χ : B →* Kˣ) (ψ : C →* Kˣ) (hχ : ∀ x, ψ (b x) = χ x) :
    IndV B.subtype (scalarCharacter χ) ≃ₗ[K] IndV C.subtype (scalarCharacter ψ) := by
  have hb' (x : C) : e.symm x = b.symm x := by
    apply e.injective
    simpa only [e.apply_symm_apply, b.apply_symm_apply] using (hb (b.symm x)).symm
  have hχ' (x : C) : χ (b.symm x) = ψ x := by
    simpa only [b.apply_symm_apply] using (hχ (b.symm x)).symm
  let f := inductionPairMap B C e.toMonoidHom b.toMonoidHom hb χ ψ hχ
  let r := inductionPairMap C B e.symm.toMonoidHom b.symm.toMonoidHom hb' ψ χ hχ'
  have hl : r.toLinearMap.comp f.toLinearMap = LinearMap.id := by
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    change r (f (IndV.mk B.subtype (scalarCharacter χ) g a)) = _
    calc
      _ = r (IndV.mk C.subtype (scalarCharacter ψ) (e g) a) :=
        congrArg r (inductionPairMap_mk B C e.toMonoidHom b.toMonoidHom hb χ ψ hχ g a)
      _ = IndV.mk B.subtype (scalarCharacter χ) (e.symm (e g)) a :=
        inductionPairMap_mk C B e.symm.toMonoidHom b.symm.toMonoidHom hb' ψ χ hχ' (e g) a
      _ = _ := by rw [e.symm_apply_apply]; rfl
  have hr : f.toLinearMap.comp r.toLinearMap = LinearMap.id := by
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    change f (r (IndV.mk C.subtype (scalarCharacter ψ) g a)) = _
    calc
      _ = f (IndV.mk B.subtype (scalarCharacter χ) (e.symm g) a) :=
        congrArg f (inductionPairMap_mk C B e.symm.toMonoidHom b.symm.toMonoidHom hb' ψ χ hχ' g a)
      _ = IndV.mk C.subtype (scalarCharacter ψ) (e (e.symm g)) a :=
        inductionPairMap_mk B C e.toMonoidHom b.toMonoidHom hb χ ψ hχ (e.symm g) a
      _ = _ := by rw [e.apply_symm_apply]; rfl
  exact { f.toLinearMap with
    invFun := r
    left_inv := fun x => LinearMap.congr_fun hl x
    right_inv := fun x => LinearMap.congr_fun hr x }

@[simp] theorem inductionPairEquiv_mk (B : Subgroup G) (C : Subgroup H)
    (e : G ≃* H) (b : B ≃* C) (hb : ∀ x : B, e x = b x)
    (χ : B →* Kˣ) (ψ : C →* Kˣ) (hχ : ∀ x, ψ (b x) = χ x)
    (g : G) (a : K) :
    inductionPairEquiv B C e b hb χ ψ hχ (IndV.mk B.subtype (scalarCharacter χ) g a) =
      IndV.mk C.subtype (scalarCharacter ψ) (e g) a :=
  inductionPairMap_mk B C e.toMonoidHom b.toMonoidHom hb χ ψ hχ g a

theorem inductionPairEquiv_intertwines (B : Subgroup G) (C : Subgroup H)
    (e : G ≃* H) (b : B ≃* C) (hb : ∀ x : B, e x = b x)
    (χ : B →* Kˣ) (ψ : C →* Kˣ) (hχ : ∀ x, ψ (b x) = χ x)
    (g : G) (v : IndV B.subtype (scalarCharacter χ)) :
    inductionPairEquiv B C e b hb χ ψ hχ (ind B.subtype (scalarCharacter χ) g v) =
      ind C.subtype (scalarCharacter ψ) (e g) (inductionPairEquiv B C e b hb χ ψ hχ v) :=
  IntertwiningMap.isIntertwining _ _
    (inductionPairMap B C e.toMonoidHom b.toMonoidHom hb χ ψ hχ) g v

/-- Transport the invariant subspaces and their simple literal quotients
across the pair isomorphism, without changing the coefficient field. -/
theorem inductionPair_filtration (B : Subgroup G) (C : Subgroup H)
    (e : G ≃* H) (b : B ≃* C) (hb : ∀ x : B, e x = b x)
    (χ : B →* Kˣ) (ψ : C →* Kˣ) (hχ : ∀ x, ψ (b x) = χ x)
    (D : Set ℕ) (h : FactorDegreeFiltration D (ind B.subtype (scalarCharacter χ))) :
    FactorDegreeFiltration D (ind C.subtype (scalarCharacter ψ)) :=
  h.transport e.toMonoidHom e.surjective _ (inductionPairEquiv B C e b hb χ ψ hχ)
    (inductionPairEquiv_intertwines B C e b hb χ ψ hχ)

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
