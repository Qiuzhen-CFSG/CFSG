module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.FixedCodimTransport

/-!
# Keeping the actor marking on four-dimensional extensions

Reindexing an action along a group isomorphism preserves its fixed and moved
spaces under the literal subgroup image, and hence its best offenders and
quadratic ratio. Indecomposability supplies the invariant-complement criterion
used by the fixed-space calculations. These identities transport B.4.8(2)–(3)
to the exact actor identification of the source quotient or submodule.

Source: Aschbacher–Smith, B.4.8, printed p.91 (1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.FourSpaceOffenders
variable {D E V : Type*} [Group D] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) D V) (j : E ≃* D)

theorem reindex_fixed (A : Subgroup E) :
    fixedSpace (σ.comp j.toMonoidHom) A = fixedSpace σ (A.map j.toMonoidHom) :=
  fixedSpace_comp_map σ j.toMonoidHom A

theorem reindex_moved (A : Subgroup E) :
    moved (σ.comp j.toMonoidHom) A = moved σ (A.map j.toMonoidHom) := by
  have hh := subspaceCommutator_map_embedding (σ.comp j.toMonoidHom) σ j.toMonoidHom
    (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ => rfl) A ⊤
  simpa using hh

theorem reindex_invariants : Representation.invariants (σ.comp j.toMonoidHom) = σ.invariants := by
  ext v
  constructor
  · intro hv g
    obtain ⟨a,rfl⟩ := j.surjective g
    exact hv a
  · intro hv a
    exact hv (j a)

theorem reindex_elementary {A : Subgroup E} (hA : IsElementaryTwo A) :
    IsElementaryTwo (A.map j.toMonoidHom) := by
  let _ : IsElementaryAbelian 2 A := hA.2
  exact ⟨fun hb => hA.1 ((map_eq_bot_iff_of_injective A j.injective).mp hb),
    IsElementaryAbelian.map _⟩

theorem reindex_quadratic {A : Subgroup E}
    (hA : IsQuadratic (σ.comp j.toMonoidHom) A) :
    IsQuadratic σ (A.map j.toMonoidHom) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  exact hA a ha b hb v

theorem reindex_ratio_le : quadraticRatio σ ≤ quadraticRatio (σ.comp j.toMonoidHom) := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA,hq⟩
  have hr : actionRatio σ (A.map j.toMonoidHom) = actionRatio (σ.comp j.toMonoidHom) A := by
    unfold actionRatio fixedCodim
    rw [reindex_fixed, rank_map_injective _ j.injective]
  exact iInf_le_of_le (A.map j.toMonoidHom)
    (iInf_le_of_le ⟨reindex_elementary j hA, reindex_quadratic σ j hq⟩ hr.le)

theorem reindex_ratio : quadraticRatio (σ.comp j.toMonoidHom) = quadraticRatio σ := by
  apply le_antisymm _ (reindex_ratio_le σ j)
  have h := reindex_ratio_le (σ.comp j.toMonoidHom) j.symm
  have he : (σ.comp j.toMonoidHom).comp j.symm.toMonoidHom = σ := by
    ext a v
    change σ (j (j.symm a)) v = σ a v
    rw [j.apply_symm_apply]
  rwa [he] at h

variable [FiniteDimensional (ZMod 2) V]
theorem reindex_best (A : Subgroup E) :
    IsBestOffender (σ.comp j.toMonoidHom) A ↔ IsBestOffender σ (A.map j.toMonoidHom) := by
  constructor
  · exact fun h => h.map_of_fixedCodim _ _ j.toMonoidHom j.injective
      (fun B => by unfold fixedCodim; rw [reindex_fixed])
  · intro h
    have hc (B : Subgroup D) : fixedCodim σ B =
        fixedCodim (σ.comp j.toMonoidHom) (B.map j.symm.toMonoidHom) := by
      unfold fixedCodim
      have hm : (B.map j.symm.toMonoidHom).map j.toMonoidHom = B := by
        rw [map_map]
        have hf : j.toMonoidHom.comp j.symm.toMonoidHom = MonoidHom.id D :=
          MonoidHom.ext (fun a => j.apply_symm_apply a)
        rw [hf, map_id]
      rw [reindex_fixed, hm]
    have hh := h.map_of_fixedCodim _ _ j.symm.toMonoidHom j.symm.injective hc
    simpa [map_map] using hh

omit [FiniteDimensional (ZMod 2) V] in
theorem reindex_indecomposable (hind : IsIndecomposable σ)
    (A B : Submodule (ZMod 2) V)
    (hA : ∀ g v, v ∈ A → (σ.comp j.toMonoidHom) g v ∈ A)
    (hB : ∀ g v, v ∈ B → (σ.comp j.toMonoidHom) g v ∈ B)
    (hc : IsCompl A B) : A = ⊥ ∨ B = ⊥ := by
  let A' : Subrepresentation σ :=
    { toSubmodule := A
      apply_mem_toSubmodule g v hv := by simpa using hA (j.symm g) v hv }
  let B' : Subrepresentation σ :=
    { toSubmodule := B
      apply_mem_toSubmodule g v hv := by simpa using hB (j.symm g) v hv }
  exact (hind.2 A' B' hc).imp
    (fun h => congrArg Subrepresentation.toSubmodule h)
    (fun h => congrArg Subrepresentation.toSubmodule h)
end CFSG.Quasithin.ChapterB.NaturalExtensions.FourSpaceOffenders
