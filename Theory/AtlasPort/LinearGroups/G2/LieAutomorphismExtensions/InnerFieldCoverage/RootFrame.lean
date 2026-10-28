module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.RootDiagonal
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.FieldAction

/-!
# The labelled root frame for abstract G₂ automorphisms

The six positive roots and the two negative simple roots are actual additive
subgroups of the split-octonion automorphism model. An automorphism preserving
these eight subgroups induces eight additive bijections of the field. Torus
conjugations and coefficientwise field automorphisms preserve the frame, with
exactly the prescribed parameter actions.

This supplies the coordinate interface for inner-field coverage. Preservation
of this frame by an inner correction of an arbitrary automorphism remains a
separate geometric assertion; it is not assumed as a property of the model.

Source: the automorphism input used in Aschbacher--Smith F.1.12, printed
pp.263--264. The root and torus formulas are the licensed ATLAS port imported
through RootDiagonal; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.SplitOctonion Atlas.G2.Explicit
namespace Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
open RootDiagonal
variable {F : Type*} [Field F]

theorem root_add (i : Fin 8) (s t : F) :
    root i (s + t) = root i s * root i t := by
  fin_cases i
  · exact (rootA_add s t).symm
  · exact (rootB_add s t).symm
  · exact (rootC_add s t).symm
  · exact (rootD_add s t).symm
  · exact (rootE_add s t).symm
  · exact (rootF_add s t).symm
  · exact ((MulAut.conj (weylR : Model F)).map_mul (rootE s) (rootE t)).symm.trans
      (congrArg (MulAut.conj weylR) (rootE_add s t)) |>.symm
  · exact ((MulAut.conj (weylS : Model F)).map_mul (rootF s) (rootF t)).symm.trans
      (congrArg (MulAut.conj weylS) (rootF_add s t)) |>.symm

theorem root_zero (i : Fin 8) : root i (0 : F) = 1 := by
  have h := root_add i (0 : F) 0
  apply mul_left_cancel (a := root i (0 : F))
  simpa only [add_zero, mul_one] using h.symm

theorem root_injective (i : Fin 8) : Function.Injective (root i (E := F)) := by
  fin_cases i
  · exact rootA_injective
  · exact rootB_injective
  · exact rootC_injective
  · exact rootD_injective
  · exact rootE_injective
  · exact rootF_injective
  · exact (MulAut.conj (weylR : Model F)).injective.comp rootE_injective
  · exact (MulAut.conj (weylS : Model F)).injective.comp rootF_injective

def rootHom (i : Fin 8) : Multiplicative F →* Model F where
  toFun t := root i t.toAdd
  map_one' := root_zero i
  map_mul' s t := root_add i s.toAdd t.toAdd

def rootGroup (i : Fin 8) : Subgroup (Model F) := (rootHom i).range

def PreservesRootGroups (a : MulAut (Model F)) : Prop :=
  ∀ i : Fin 8, (rootGroup i).map a.toMonoidHom = rootGroup i

theorem PreservesRootGroups.mul {a b : MulAut (Model F)}
    (ha : PreservesRootGroups a) (hb : PreservesRootGroups b) :
    PreservesRootGroups (a * b) := by
  intro i
  change (rootGroup i).map (a.toMonoidHom.comp b.toMonoidHom) = rootGroup i
  rw [← Subgroup.map_map, hb i, ha i]

theorem PreservesRootGroups.inv {a : MulAut (Model F)}
    (ha : PreservesRootGroups a) : PreservesRootGroups a⁻¹ := by
  intro i
  have h := congrArg (Subgroup.map a.symm.toMonoidHom) (ha i)
  rw [Subgroup.map_map] at h
  have he : a.symm.toMonoidHom.comp a.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact a.symm_apply_apply x
  rw [he, Subgroup.map_id] at h
  exact h.symm

theorem torus_preservesRootGroups (u v : Fˣ) :
    PreservesRootGroups (MulAut.conj (torus (u ^ 2 * v) (u * v))) := by
  intro i
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨Multiplicative.ofAdd ((character u v i : F) * t.toAdd),
      (torus_character u v i t.toAdd).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨root i ((↑(character u v i) : F)⁻¹ * t.toAdd),
      ⟨Multiplicative.ofAdd _, rfl⟩, ?_⟩
    change MulAut.conj _ (root i _) = root i t.toAdd
    rw [torus_character]
    congr 1
    rw [mul_inv_cancel_left₀ (Units.ne_zero _)]

noncomputable def rootParameterization (i : Fin 8) :
    Multiplicative F ≃* rootGroup (F := F) i :=
  MonoidHom.ofInjective (f := rootHom (F := F) i)
    ((root_injective i).comp Multiplicative.toAdd.injective)

noncomputable def rootParameter (a : MulAut (Model F)) (ha : PreservesRootGroups a)
    (i : Fin 8) : F ≃+ F :=
  let e := (rootParameterization i).trans
    ((a.subgroupMap (rootGroup i)).trans
      ((MulEquiv.subgroupCongr (ha i)).trans (rootParameterization i).symm))
  { toFun := fun t => (e (Multiplicative.ofAdd t)).toAdd
    invFun := fun t => (e.symm (Multiplicative.ofAdd t)).toAdd
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_mul }

theorem apply_rootParameter (a : MulAut (Model F)) (ha : PreservesRootGroups a)
    (i : Fin 8) (t : F) : a (root i t) = root i (rootParameter a ha i t) := by
  symm
  exact MonoidHom.apply_ofInjective_symm (f := rootHom (F := F) i)
    ((root_injective i).comp Multiplicative.toAdd.injective)
    ((MulEquiv.subgroupCongr (ha i)) (a.subgroupMap (rootGroup i)
      (rootParameterization i (Multiplicative.ofAdd t))))

private theorem field_rootC (σ : F ≃+* F) (t : F) :
    fieldAction σ (rootC t) = rootC (σ t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [fieldAction, fieldEquiv, transportAutomorphism, transportLinear,
      mapCoefficients, rootC, rootCEquiv, rootCLinear, rootCApply]

private theorem field_rootD (σ : F ≃+* F) (t : F) :
    fieldAction σ (rootD t) = rootD (σ t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [fieldAction, fieldEquiv, transportAutomorphism, transportLinear,
      mapCoefficients, rootD, rootDEquiv, rootDLinear, rootDApply]

private theorem field_rootE (σ : F ≃+* F) (t : F) :
    fieldAction σ (rootE t) = rootE (σ t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [fieldAction, fieldEquiv, transportAutomorphism, transportLinear,
      mapCoefficients, rootE, rootEEquiv, rootELinear, rootEApply]

private theorem field_rootF (σ : F ≃+* F) (t : F) :
    fieldAction σ (rootF t) = rootF (σ t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [fieldAction, fieldEquiv, transportAutomorphism, transportLinear,
      mapCoefficients, rootF, rootFEquiv, rootFLinear, rootFApply]

private theorem field_weylR (σ : F ≃+* F) :
    fieldAction σ (weylR : Model F) = weylR := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [fieldAction, fieldEquiv, transportAutomorphism, transportLinear,
      mapCoefficients, weylR, weylREquiv, weylRLinear, weylRApply]

private theorem field_weylS (σ : F ≃+* F) :
    fieldAction σ (weylS : Model F) = weylS := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext j
  fin_cases j <;>
    simp [fieldAction, fieldEquiv, transportAutomorphism, transportLinear,
      mapCoefficients, weylS, weylSEquiv, weylSLinear, weylSApply]

theorem fieldAction_root (σ : F ≃+* F) (i : Fin 8) (t : F) :
    fieldAction σ (root i t) = root i (σ t) := by
  fin_cases i
  · exact fieldEquiv_rootA σ t
  · exact fieldEquiv_rootB σ t
  · exact field_rootC σ t
  · exact field_rootD σ t
  · exact field_rootE σ t
  · exact field_rootF σ t
  · change fieldAction σ (weylR * rootE t * weylR⁻¹) = _
    rw [map_mul, map_mul, map_inv, field_weylR, field_rootE]
    rfl
  · change fieldAction σ (weylS * rootF t * weylS⁻¹) = _
    rw [map_mul, map_mul, map_inv, field_weylS, field_rootF]
    rfl

end Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
