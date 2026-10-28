module

public import CFSG.Quasithin.ChapterG.Section02.Intersection
public import Theory.SpecificGroups.SL2.Affine.Action
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The actual higher-field natural action in G.2.3

The model identifies the literal image L* in LT/O₂(LT) with SL₂(F),
and the coordinates intertwine the original conjugation action on V.
The point is an F-line. No Sylow-image, generation or quotient-module
conclusion is included in these source data.

Transitivity on nonzero columns proves irreducibility on binary subgroups.
The one-dimensional field subspaces give disjointness of the original
marked points. Together with the earlier G.2.2 containment and Frattini
bound, these facts discharge the geometric inputs to the intersection layer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3, printed pp.333–334, PDF pp.344–345.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
open Setup
variable {G : Type*} [Group G]

/-- Restriction of the original star map to its actual L-image. -/
def starProjection (D : Setup G) : D.L →* D.star D.L :=
  ((QuotientGroup.mk' (pCore 2 D.LT)).comp
    (inclusion (show D.L ≤ D.LT from le_sup_left))).codRestrict _
    (fun l => mem_map.mpr ⟨⟨l, (show D.L ≤ D.LT from le_sup_left) l.property⟩,
      l.property, rfl⟩)

theorem starProjection_surjective (D : Setup G) : Function.Surjective (starProjection D) := by
  intro q
  obtain ⟨l, hl, he⟩ := q.property
  exact ⟨⟨l, hl⟩, Subtype.ext he⟩

theorem normalizes_of_span (D : Setup G) (hspan : D.VL = D.V) :
    D.L ≤ normalizer (D.V : Set G) := by
  rw [← hspan]
  exact le_normalizer_conjugateSpanBy D.V₁ D.L

/-- The additional source hypotheses for n>1, including the original
marked conjugator. Earlier G.2.2 outputs are separate premises. -/
structure Hypothesis [Finite G] (D : Setup G) (F : Type*) [Field F] [Finite F]
    (n : ℕ) (g : G) where
  setup : D.Hypothesis
  exponent_gt_one : 1 < n
  field_card : Nat.card F = 2 ^ n
  span_eq : D.VL = D.V
  model : D.star D.L ≃* SL(2, F)
  coordinates : D.V ≃* Multiplicative (Fin 2 → F)
  equivariant (l : D.L) (v : D.V) :
    (coordinates ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D span_eq l.property) v).mp v.property⟩).toAdd =
        (model (starProjection D l)).val *ᵥ (coordinates v).toAdd
  point : Submodule F (Fin 2 → F)
  point_dimension : Module.finrank F point = 1
  point_mem (v : D.V) : (v : G) ∈ D.V₁ ↔ (coordinates v).toAdd ∈ point
  star_U_ne_bot : D.star D.U ≠ ⊥
  g_mem : g ∈ D.L
  g_not_normalizing : g ∉ D.G₁

namespace Hypothesis
variable [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g : G} (d : Hypothesis D F n g)
include d

/-- Irreducibility on binary subgroups follows from transitivity on all
nonzero natural vectors, not merely F-linear irreducibility. -/
theorem irreducible (A : Subgroup G) (hAV : A ≤ D.V)
    (hLA : D.L ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = D.V := by
  by_cases hA : A = ⊥
  · exact Or.inl hA
  right
  apply le_antisymm hAV
  obtain ⟨a, ha1⟩ := ne_bot_iff_exists_ne_one.mp hA
  have ha := a.property
  have ha1 : (a : G) ≠ 1 := fun he => ha1 (Subtype.ext he)
  have hca : (d.coordinates ⟨a, hAV ha⟩).toAdd ≠ 0 := by
    intro he
    have hh : (⟨a, hAV ha⟩ : D.V) = 1 := d.coordinates.injective (he.trans d.coordinates.map_one.symm)
    exact ha1 (congrArg Subtype.val hh)
  intro v hv
  by_cases hv1 : v = 1
  · simp [hv1]
  have hcv : (d.coordinates ⟨v, hv⟩).toAdd ≠ 0 := by
    intro he
    have hh : (⟨v, hv⟩ : D.V) = 1 := d.coordinates.injective (he.trans d.coordinates.map_one.symm)
    exact hv1 (congrArg Subtype.val hh)
  obtain ⟨x, hx⟩ := Matrix.SL2.exists_mulVec_eq F _ _ hca hcv
  obtain ⟨l, hl⟩ := (d.model.surjective.comp (starProjection_surjective D)) x
  change d.model (starProjection D l) = x at hl
  have he := (d.equivariant l ⟨a, hAV ha⟩).trans (by simpa [hl] using hx)
  have he' : (l : G) * a * (l : G)⁻¹ = v :=
    congrArg Subtype.val (d.coordinates.injective he)
  exact he' ▸ (mem_normalizer_iff.mp (hLA l.property) a).mp ha

/-- The actual natural plane has order q². -/
theorem card_V : Nat.card D.V = 2 ^ (2 * n) := by
  rw [Nat.card_congr d.coordinates.toEquiv]
  change Nat.card (Fin 2 → F) = _
  rw [Nat.card_fun, Nat.card_fin, d.field_card, ← pow_mul, Nat.mul_comm n 2]

/-- Natural coordinates identify the original point with its field line. -/
noncomputable def pointEquiv : D.V₁ ≃ d.point where
  toFun x := ⟨(d.coordinates ⟨x, d.setup.point_le x.property⟩).toAdd,
    (d.point_mem _).mp x.property⟩
  invFun x := ⟨(d.coordinates.symm (Multiplicative.ofAdd x) : G),
    (d.point_mem _).mpr (by simp)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

/-- The point has the same order as the defining field. -/
theorem card_point : Nat.card D.V₁ = 2 ^ n := by
  rw [Nat.card_congr d.pointEquiv, Module.natCard_eq_pow_finrank (K := F),
    d.point_dimension, pow_one, d.field_card]

private theorem conjugate_point_le (l : D.L) :
    conjugate D.V₁ (l : G)⁻¹ ≤ D.V := by
  rintro x ⟨y, hy, rfl⟩
  change (l : G)⁻¹⁻¹ * y * ((l : G)⁻¹⁻¹)⁻¹ ∈ D.V
  simp only [inv_inv]
  exact (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) y).mp
    (d.setup.point_le hy)

/-- Coordinates of a marked conjugate point, with the source right-conjugation
convention converted to the left natural matrix action. -/
theorem conjugate_point_mem (l : D.L) (v : D.V) :
    (v : G) ∈ conjugate D.V₁ (l : G)⁻¹ ↔
      (d.coordinates v).toAdd ∈ d.point.map
        (Matrix.SpecialLinearGroup.toLin' (d.model (starProjection D l))).toLinearMap := by
  constructor
  · rintro ⟨y, hy, hye⟩
    let yv : D.V := ⟨y, d.setup.point_le hy⟩
    refine ⟨(d.coordinates yv).toAdd, (d.point_mem yv).mp hy, ?_⟩
    have he := d.equivariant l yv
    have hv : (⟨(l : G) * yv * (l : G)⁻¹,
        (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) yv).mp yv.property⟩ : D.V) = v := by
      apply Subtype.ext
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, yv] using hye
    rw [hv] at he
    exact he.symm
  · rintro ⟨y, hy, he⟩
    let yv : D.V := d.coordinates.symm (Multiplicative.ofAdd y)
    have hyv : (yv : G) ∈ D.V₁ := (d.point_mem yv).mpr (by simpa [yv] using hy)
    refine ⟨yv, hyv, ?_⟩
    have h := d.equivariant l yv
    have hv : (⟨(l : G) * yv * (l : G)⁻¹,
        (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) yv).mp yv.property⟩ : D.V) = v := by
      apply d.coordinates.injective
      apply Multiplicative.toAdd.injective
      exact h.trans (by simpa [yv, SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] using he)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using congrArg Subtype.val hv

/-- Distinct marked F-lines have trivial intersection. The original g is
kept, and disjointness is a conclusion of the natural-action hypotheses. -/
theorem point_disjoint : Disjoint D.V₁ (conjugate D.V₁ g) := by
  let l : D.L := (⟨g, d.g_mem⟩ : D.L)⁻¹
  let e := Matrix.SpecialLinearGroup.toLin' (d.model (starProjection D l))
  have hm (v : D.V) : (v : G) ∈ conjugate D.V₁ g ↔
      (d.coordinates v).toAdd ∈ d.point.map e.toLinearMap := by
    simpa only [l, Subgroup.coe_inv, inv_inv] using d.conjugate_point_mem l v
  have hconj : conjugate D.V₁ g ≤ D.V := by
    simpa only [l, Subgroup.coe_inv, inv_inv] using d.conjugate_point_le l
  have hne : d.point ≠ d.point.map e.toLinearMap := by
    intro he
    have heq : conjugate D.V₁ g = D.V₁ := by
      apply le_antisymm
      · intro x hx
        exact (d.point_mem ⟨x, hconj hx⟩).mpr (he ▸ (hm ⟨x, hconj hx⟩).mp hx)
      · intro x hx
        exact (hm ⟨x, d.setup.point_le hx⟩).mpr
          (he ▸ (d.point_mem ⟨x, d.setup.point_le hx⟩).mp hx)
    have hg : g⁻¹ ∈ normalizer (D.V₁ : Set G) := mem_normalizer_iff_map_conj_eq.mpr heq
    apply d.g_not_normalizing
    change g ∈ normalizer (D.V₁ : Set G)
    simpa only [inv_inv] using (normalizer (D.V₁ : Set G)).inv_mem hg
  have hdis : Disjoint d.point (d.point.map e.toLinearMap) :=
    (Submodule.isAtom_iff_finrank_eq_one.mpr d.point_dimension).disjoint_of_ne
      (Submodule.isAtom_iff_finrank_eq_one.mpr ((e.finrank_map_eq d.point).trans d.point_dimension)) hne
  apply disjoint_def.mpr
  intro x hx hxg
  let v : D.V := ⟨x, d.setup.point_le hx⟩
  have hz : (d.coordinates v).toAdd = 0 :=
    (Submodule.disjoint_def.mp hdis) (d.coordinates v).toAdd ((d.point_mem v).mp hx)
      ((hm v).mp hxg)
  exact congrArg Subtype.val (d.coordinates.injective (hz.trans d.coordinates.map_one.symm))

/-- G.2.2(3) and the marked Sylow subgroup give the required two-group. -/
theorem U_isPGroup (hUT : D.U ≤ D.T) : IsPGroup 2 D.U := by
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  have hT : IsPGroup 2 D.T := by
    rw [← hP]
    exact P.isPGroup'.map D.LT.subtype
  exact hT.of_injective (inclusion hUT) (inclusion_injective hUT)

/-- The natural module is invariant under both original generators. -/
theorem I_normalizes (hUT : D.U ≤ D.T) : D.I g ≤ normalizer (D.V : Set G) := by
  have hU := hUT.trans d.setup.T_normalizes_V
  have hg := normalizes_of_span D d.span_eq d.g_mem
  refine sup_le hU ?_
  rintro _ ⟨u, hu, rfl⟩
  change g⁻¹ * u * g⁻¹⁻¹ ∈ normalizer (D.V : Set G)
  rw [inv_inv]
  exact (normalizer (D.V : Set G)).mul_mem
    ((normalizer (D.V : Set G)).mul_mem ((normalizer (D.V : Set G)).inv_mem hg) (hU hu)) hg

/-- Clauses (4–5) except centrality of V, from exactly the earlier
containment and Frattini conclusions. Point geometry is discharged here. -/
theorem intersection (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.V ≤ D.S₂ g ∧ D.S₂ g ≤ D.S g ∧
    ((D.S₂ g).subgroupOf (D.I g)).Normal ∧
    ⁅D.S₂ g, D.I g⁆ ≤ D.V ∧ IsElementaryAbelian 2 (D.S₂ g) :=
  D.rank_one_intersection_layer g (d.U_isPGroup hUT) hf d.setup.point_le
    (d.I_normalizes hUT) (normalizes_of_span D d.span_eq d.g_mem) d.point_disjoint

/-- Once generation places L in I, the natural first layer is central in S.
The irreducibility and disjointness premises are proved from the model. -/
theorem central_first (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ D.I g) :
    D.V ≤ D.S g ⊓ centralizer (D.S g : Set G) :=
  D.rank_one_central_first_layer g (d.U_isPGroup hUT) hf d.setup.point_le
    (d.I_normalizes hUT) (normalizes_of_span D d.span_eq d.g_mem) d.point_disjoint hLI
    d.irreducible

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
