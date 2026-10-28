module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Star.Action
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The genuine point normalizer in higher-field G.2.3

The Sylow supplement to the two-residual puts the full N_L(V₁) inside H.
It therefore normalizes U. The given natural coordinates identify its
literal star image with the full setwise stabilizer of the field line.
These arguments adapt the field-independent normalizer calculations in
`LinearThree.Structure.Radical.Action`, with the original quotient and
residual conventions preserved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.1–3, printed pp.332–333, PDF pp.343–344.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
open Setup
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F] {n : ℕ} {g : G}
  (d : Hypothesis D F n g)
include d

theorem pointNormalizer_le_H : D.L ⊓ D.G₁ ≤ D.H := by
  let L' := D.L.subgroupOf D.LT
  let : L'.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.L.le_normalizer d.setup.T_normalizes_L)
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal L'
  let e : L' ≃* D.L := subgroupOfEquivOfLe le_sup_left
  let QL : Sylow 2 D.L := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQL (x : D.L) : x ∈ (QL : Subgroup D.L) ↔ (x : G) ∈ D.T := by
    change x ∈ (Q : Subgroup L').map e.toMonoidHom ↔ _
    rw [mem_map_equiv, hQ]
    change (⟨x, mem_sup_left x.property⟩ : D.LT) ∈ (P : Subgroup D.LT) ↔ _
    constructor
    · intro hx
      exact hP ▸ mem_map_of_mem D.LT.subtype hx
    · intro hx
      exact (mem_map_iff_mem (f := D.LT.subtype) D.LT.subtype_injective).mp (hP.symm ▸ hx)
  let N := D.G₁.subgroupOf D.L
  have hQN : (QL : Subgroup D.L) ≤ N := by
    intro x hx
    exact d.setup.T_normalizes_point ((hQL x).mp hx)
  have hs := congrArg (fun A : Subgroup N => A.map N.subtype)
    (pResidual_sup_sylow_eq_top (QL.subtype hQN))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hs
  let eN : N ≃* (D.L ⊓ D.G₁ : Subgroup G) :=
    { toFun := fun x => ⟨x, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hR : ((pResidual 2 N).map N.subtype).map D.L.subtype = D.L₁ := by
    change _ = (pResidual 2 (D.L ⊓ D.G₁ : Subgroup G)).map (D.L ⊓ D.G₁).subtype
    rw [← map_pResidual_of_surjective 2 eN.toMonoidHom eN.surjective, Subgroup.map_map, Subgroup.map_map]
    rfl
  intro x hx
  have hxN : (⟨x, hx.1⟩ : D.L) ∈ N := hx.2
  rw [← hs] at hxN
  have hm := mem_map_of_mem D.L.subtype hxN
  rw [Subgroup.map_sup, hR] at hm
  apply (sup_le (le_sup_left.trans d.setup.local_le)
    (show (((QL.subtype hQN : Sylow 2 N) : Subgroup N).map N.subtype).map D.L.subtype ≤ D.H from ?_)) hm
  rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  exact (le_sup_right.trans d.setup.local_le) ((hQL z.val).mp hz)

theorem pointNormalizer_normalizes_U : D.L ⊓ D.G₁ ≤ normalizer (D.U : Set G) :=
  d.pointNormalizer_le_H.trans (le_normalizer_conjugateSpanBy _ _)

/-- The coordinate model identifies the full setwise point stabilizer,
not just the pointwise local subgroup. -/
theorem model_mem_pointStabilizer_iff (l : D.L) :
    d.model (starProjection D l) ∈
      MulAction.stabilizer SL(2,F) (d.point : Set (Fin 2 → F)) ↔ (l : G) ∈ D.G₁ := by
  rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 2 → F⦄, v ∈ d.point →
    (d.model (starProjection D l)).val *ᵥ v ∈ d.point) ↔ _
  constructor
  · intro hl
    apply mem_normalizer_fintype
    intro w hw
    have hwV := d.setup.point_le hw
    have he := d.equivariant l ⟨w, hwV⟩
    apply (d.point_mem ⟨(l : G) * w * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) w).mp hwV⟩).mpr
    rw [he]
    exact hl ((d.point_mem ⟨w, hwV⟩).mp hw)
  · intro hl v hv
    let w := d.coordinates.symm (Multiplicative.ofAdd v)
    have hw : (w : G) ∈ D.V₁ := (d.point_mem w).mpr (by simpa [w] using hv)
    have hc := (mem_normalizer_iff.mp hl w).mp hw
    have hp := (d.point_mem ⟨(l : G) * w * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) w).mp w.property⟩).mp hc
    rw [d.equivariant l w] at hp
    simpa only [w, d.coordinates.apply_symm_apply, toAdd_ofAdd] using hp

/-- The literal star image of N_L(V₁), transported by the supplied model. -/
theorem pointNormalizer_model :
    ((D.star (D.L ⊓ D.G₁)).subgroupOf (D.star D.L)).map d.model.toMonoidHom =
      MulAction.stabilizer SL(2,F) (d.point : Set (Fin 2 → F)) := by
  ext s
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, hx, he⟩ := hq
    let l : D.L := ⟨x, hx.1⟩
    have hq' : starProjection D l = q := Subtype.ext he
    rw [← hq']
    exact (d.model_mem_pointStabilizer_iff l).mpr hx.2
  · intro hs
    obtain ⟨l, hl⟩ := (d.model.surjective.comp (starProjection_surjective D)) s
    change d.model (starProjection D l) = s at hl
    have hx : (l : G) ∈ D.G₁ := (d.model_mem_pointStabilizer_iff l).mp (hl.symm ▸ hs)
    exact ⟨starProjection D l,
      ⟨⟨l, mem_sup_left l.property⟩, ⟨l.property, hx⟩, rfl⟩, hl⟩


end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
