module
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Normalizers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage

public import Theory.GroupAction.TypedCosetAutomorphisms
public import Theory.GroupAction.InvariantFixedTree
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover

/-!
# An automorphism-invariant parabolic for an even-field G₂ two-subgroup

Coefficient transport preserves the two root-defined parabolics, hence acts
on their actual left-coset graph. The proved inner-field description lifts
every abstract automorphism to a color-preserving semilinear graph symmetry.
The center of the fixed tree therefore selects a vertex whose stabilizer
contains the original two-subgroup normalizer and is fixed by every
abstract automorphism preserving that two-subgroup.

The selected subgroup is an actual conjugate full parabolic. No invariance
of a chosen Sylow subgroup or bound on its order is assumed.
Source: Aschbacher--Smith 2.4.25, printed p.543, the G₂ model escape.
-/

public section
open Subgroup
namespace Atlas.G2.EvenLocal.NormalizerCover
open LieParabolicSetup LieAutomorphismExtensions SylowParabolicInvariance
variable {F : Type*} [Field F]

theorem fieldAction_highestRoot (σ : F ≃+* F) :
    (highestRoot (F := F)).map (fieldAction σ).toMonoidHom = highestRoot := by
  ext g
  constructor
  · rintro ⟨_, ⟨a,rfl⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd (σ a.toAdd), ?_⟩
    exact (fieldEquiv_rootA σ a.toAdd).symm
  · rintro ⟨a,rfl⟩
    refine ⟨rootA (σ.symm a.toAdd), ⟨Multiplicative.ofAdd _,rfl⟩, ?_⟩
    change fieldEquiv σ (rootA _) = rootA _
    rw [fieldEquiv_rootA, σ.apply_symm_apply]

theorem fieldAction_longRootLocal (σ : F ≃+* F) :
    (longRootLocal (F := F)).map (fieldAction σ).toMonoidHom = longRootLocal := by
  apply SetLike.coe_injective
  exact fieldEquiv_longRootLocal_image σ

variable [CharP F 2]

theorem fieldAction_parabolic₁ (σ : F ≃+* F) :
    (parabolic₁ (F := F)).map (fieldAction σ).toMonoidHom = parabolic₁ := by
  rw [← normalizer_highestRoot, map_equiv_normalizer_eq, fieldAction_highestRoot]

omit [CharP F 2] in
theorem fieldAction_parabolic₂ (σ : F ≃+* F) :
    (parabolic₂ (F := F)).map (fieldAction σ).toMonoidHom = parabolic₂ := by
  rw [← normalizer_longRootLocal, map_equiv_normalizer_eq, fieldAction_longRootLocal]
end Atlas.G2.EvenLocal.NormalizerCover

namespace Atlas.G2.EvenLocal.NormalizerCover
open LieParabolicSetup LieAutomorphismExtensions
open Subgroup.CosetGeometry
variable {F : Type*} [Field F] [CharP F 2]
noncomputable section

private def fieldVertexEquiv (σ : F ≃+* F) : Vertex F ≃ Vertex F :=
  Equiv.sumCongr
    (cosetAutomorphism parabolic₁ (fieldAction σ) (fieldAction_parabolic₁ σ))
    (cosetAutomorphism parabolic₂ (fieldAction σ) (fieldAction_parabolic₂ σ))

private theorem fieldVertexEquiv_short (σ : F ≃+* F) (g : Model F) :
    fieldVertexEquiv σ (shortVertex g) = shortVertex (fieldAction σ g) := by
  exact congrArg Sum.inl (cosetAutomorphism_mk _ _ _ g)

private theorem fieldVertexEquiv_long (σ : F ≃+* F) (g : Model F) :
    fieldVertexEquiv σ (longVertex g) = longVertex (fieldAction σ g) := by
  exact congrArg Sum.inr (cosetAutomorphism_mk _ _ _ g)

/-- Coefficient transport acts on the actual two-parabolic coset graph. -/
def fieldGraphIso (σ : F ≃+* F) : incidenceGraph (F := F) ≃g incidenceGraph (F := F) where
  toEquiv := fieldVertexEquiv σ
  map_rel_iff' := by
    intro x y
    constructor
    · rintro (⟨g,hx,hy⟩ | ⟨g,hx,hy⟩)
      · obtain ⟨k,rfl⟩ := (fieldAction σ).surjective g
        exact Or.inl ⟨k, (fieldVertexEquiv σ).injective
          (hx.trans (fieldVertexEquiv_short σ k).symm), (fieldVertexEquiv σ).injective
          (hy.trans (fieldVertexEquiv_long σ k).symm)⟩
      · obtain ⟨k,rfl⟩ := (fieldAction σ).surjective g
        exact Or.inr ⟨k, (fieldVertexEquiv σ).injective
          (hx.trans (fieldVertexEquiv_long σ k).symm), (fieldVertexEquiv σ).injective
          (hy.trans (fieldVertexEquiv_short σ k).symm)⟩
    · rintro (⟨g,rfl,rfl⟩ | ⟨g,rfl,rfl⟩)
      · exact Or.inl ⟨fieldAction σ g,fieldVertexEquiv_short σ g,fieldVertexEquiv_long σ g⟩
      · exact Or.inr ⟨fieldAction σ g,fieldVertexEquiv_long σ g,fieldVertexEquiv_short σ g⟩

theorem fieldGraphIso_color (σ : F ≃+* F) (v : Vertex F) :
    vertexColor (fieldGraphIso σ v) = vertexColor v := by
  cases v <;> rfl

theorem fieldGraphIso_smul (σ : F ≃+* F) (g : Model F) (v : Vertex F) :
    fieldGraphIso σ (g • v) = fieldAction σ g • fieldGraphIso σ v := by
  cases v with
  | inl q => exact congrArg Sum.inl (cosetAutomorphism_smul _ _ _ g q)
  | inr q => exact congrArg Sum.inr (cosetAutomorphism_smul _ _ _ g q)

omit [CharP F 2] in
private def translationGraphIso (g : Model F) : incidenceGraph (F := F) ≃g incidenceGraph (F := F) where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      simpa only [MulAction.toPerm_apply,inv_smul_smul] using smul_incident g⁻¹ h
    · exact smul_incident g

/-- Every abstract automorphism lifts to the literal colored coset graph. -/
theorem exists_semilinear_graphIso [Finite F] (hq : 2 < Nat.card F)
    (a : MulAut (Model F)) :
    ∃ f : incidenceGraph (F := F) ≃g incidenceGraph (F := F),
      (∀ g v, f (g • v) = a g • f v) ∧ ∀ v, vertexColor (f v) = vertexColor v := by
  obtain ⟨k,σ,rfl⟩ := exists_inner_field hq a
  refine ⟨(fieldGraphIso σ).trans (translationGraphIso k), ?_, ?_⟩
  · intro g v
    change k • fieldGraphIso σ (g • v) =
      (k * fieldAction σ g * k⁻¹) • (k • fieldGraphIso σ v)
    rw [fieldGraphIso_smul]
    simp only [mul_smul,inv_smul_smul]
  · intro v
    change vertexColor (k • fieldGraphIso σ v) = _
    rw [vertexColor_smul,fieldGraphIso_color]
end
end Atlas.G2.EvenLocal.NormalizerCover

namespace Atlas.G2.EvenLocal.NormalizerCover
open Subgroup LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A nonidentity two-subgroup selects a full parabolic invariant under every
abstract automorphism preserving that original subgroup. -/
theorem exists_invariant_parabolic (hq : 2 < Nat.card F)
    (R : Subgroup (Model F)) (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    ∃ P : Subgroup (Model F),
      (∃ g : Model F, P = parabolic₁.map (MulAut.conj g).toMonoidHom ∨
        P = parabolic₂.map (MulAut.conj g).toMonoidHom) ∧
      normalizer (R : Set (Model F)) ≤ P ∧
      ∀ a : MulAut (Model F), R.map a.toMonoidHom = R → P.map a.toMonoidHom = P := by
  have hT := fixed_graph_isTree (OctonionHexagon.hexagonData (F := F)) R hR hp
    (exists_fixed_edge R hp)
  obtain ⟨v,hN,hv⟩ := GroupAction.EvenPolygon.fixed_tree_invariant_stabilizer
    (Γ := incidenceGraph) (color := vertexColor) R hT
    incident_vertices_different_colors smul_incident vertexColor_smul
  refine ⟨MulAction.stabilizer (Model F) v, ?_, hN,
    fun a ha => hv a ha (exists_semilinear_graphIso hq a)⟩
  rcases vertex_cases v with ⟨g,rfl⟩ | ⟨g,rfl⟩
  · refine ⟨g,Or.inl ?_⟩
    have he : shortVertex g = g • shortVertex (1 : Model F) := by
      rw [smul_shortVertex,mul_one]
    rw [he,MulAction.stabilizer_smul_eq_stabilizer_map_conj,stabilizer_shortVertex_one]
  · refine ⟨g,Or.inr ?_⟩
    have he : longVertex g = g • longVertex (1 : Model F) := by
      rw [smul_longVertex,mul_one]
    rw [he,MulAction.stabilizer_smul_eq_stabilizer_map_conj,stabilizer_longVertex_one]
end Atlas.G2.EvenLocal.NormalizerCover
