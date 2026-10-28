module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.Coordinates
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.Algebra.Pointwise.Stabilizer
/-!
# The actual local residual in marked natural coordinates

Equivariance identifies N_L(V₁) with the full set stabilizer of the marked
F-line, under the original star quotient followed by the given SL₃ model.
Surjective residual transport then identifies the image of the literal
embedded O²(N_L(V₁)). In particular, neither a vector stabilizer nor a
solvable residual may be substituted for this actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Hypothesis G.2.1 and G.2.5(8), printed pp.332,335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  (d : Hypothesis D F n g h)

def modelProjection : D.L →* SL(3, F) := d.model.toMonoidHom.comp (starProjection D)

theorem modelProjection_surjective : Function.Surjective (modelProjection d) :=
  d.model.surjective.comp (starProjection_surjective D)

def markedStabilizer : Subgroup SL(3, F) :=
  MulAction.stabilizer SL(3, F) (d.point : Set (Fin 3 → F))

theorem mem_pointNormalizer_iff (l : D.L) :
    (l : G) ∈ D.G₁ ↔ modelProjection d l ∈ markedStabilizer d := by
  have hn := normalizes_of_span D d.span_eq l.property
  have hc (v : D.V) :
      (l : G) * (v : G) * (l : G)⁻¹ ∈ D.V₁ ↔
        (modelProjection d l).val *ᵥ (d.coordinates v).toAdd ∈ d.point := by
    change _ ↔ (d.model (starProjection D l)).val *ᵥ (d.coordinates v).toAdd ∈ d.point
    rw [← d.equivariant l v]
    exact d.point_mem ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp hn v).mp v.property⟩
  constructor
  · intro hl
    apply MulAction.mem_stabilizer_set.mpr
    intro w
    obtain ⟨v, rfl⟩ := d.coordinates.surjective (Multiplicative.ofAdd w)
    exact ((hc v).symm.trans ((mem_normalizer_iff.mp hl v).symm)).trans (d.point_mem v)
  · intro hl
    apply mem_normalizer_iff.mpr
    intro v
    constructor
    · intro hv
      have hvV := d.setup.point_le hv
      apply (hc ⟨v, hvV⟩).mpr
      exact (MulAction.mem_stabilizer_set.mp hl _).mpr ((d.point_mem ⟨v, hvV⟩).mp hv)
    · intro hv
      have hvV := (mem_normalizer_iff.mp hn v).mpr (d.setup.point_le hv)
      apply (d.point_mem ⟨v, hvV⟩).mpr
      exact (MulAction.mem_stabilizer_set.mp hl _).mp ((hc ⟨v, hvV⟩).mp hv)

theorem stabilizer_image :
    (D.G₁.subgroupOf D.L).map (modelProjection d) = markedStabilizer d := by
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    exact (mem_pointNormalizer_iff d l).mp hl
  · intro x hx
    obtain ⟨l, rfl⟩ := modelProjection_surjective d x
    exact ⟨l, (mem_pointNormalizer_iff d l).mpr hx, rfl⟩

theorem residual_image :
    (D.L₁.subgroupOf D.L).map (modelProjection d) =
      (pResidual 2 (markedStabilizer d)).map (markedStabilizer d).subtype := by
  -- Use the equivalence of the two literal copies of the normalizer inside L.
  let j : (D.L ⊓ D.G₁ : Subgroup G) →* D.L := inclusion inf_le_left
  have hrange : j.range = D.G₁.subgroupOf D.L := by
    ext x
    exact ⟨fun ⟨a, ha⟩ => by rw [← ha]; exact a.property.2,
      fun hx => ⟨⟨x, x.property, hx⟩, rfl⟩⟩
  have he : (pResidual 2 (D.L ⊓ D.G₁ : Subgroup G)).map j = D.L₁.subgroupOf D.L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, Subtype.ext he⟩
  rw [← he, Subgroup.map_map]
  let f := (modelProjection d).comp j
  have hf : f.range = markedStabilizer d := by
    rw [MonoidHom.range_comp, hrange, stabilizer_image]
  have ht := map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective
  have ht' := congrArg (fun A : Subgroup f.range => A.map f.range.subtype) ht
  rw [Subgroup.map_map] at ht'
  change (pResidual 2 (D.L ⊓ D.G₁ : Subgroup G)).map f =
    (pResidual 2 f.range).map f.range.subtype at ht'
  rw [hf] at ht'
  exact ht'
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
