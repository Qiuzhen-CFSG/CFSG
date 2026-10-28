module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Star.GeometryData
public import Theory.SpecificGroups.SL2.LineRootGeometry
/-!
# The line-root step in higher-field G.2.3

The actual matrix image of U* fixes the marked field line, is nontrivial,
and is normalized by its full Borel. Line-root irreducibility therefore
identifies it with the pointwise fixer. Transporting the Sylow subgroup and
its cardinality through the specified model gives the literal U* conclusions.
The same transport identifies the full relative normalizer.

The original marked g moves the line. Its two root groups generate SL₂;
we lift their containment through the original quotient LT/O₂(LT) to prove
I* = L*. No replacement conjugator, root equality, or generation premise
is used. The only earlier-source premises are U ≤ T and Φ(U) ≤ V₁.
The subsequent lift from I* = L* to I = LU belongs to the reduction layer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3(1–2), printed pp.333–334, PDF pp.344–345.
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

/-- The actual image of U is the full root group fixing the marked line. -/
theorem matrixU_eq_fixingSubgroup (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    d.matrixU = fixingSubgroup SL(2,F) (d.point : Set (Fin 2 → F)) := by
  let : CharP F 2 := d.field_char_two
  exact SpecialLinearGroup.eq_fixing_line_of_normalized d.point d.point_dimension
    d.matrixU d.matrixU_le_fixingSubgroup (d.matrixU_ne_bot hUT hf) d.matrixU_normalized

/-- The literal U* is Sylow in the supplied copy of L*. -/
theorem exists_star_U_sylow (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U := by
  let : CharP F 2 := d.field_char_two
  obtain ⟨S, hS⟩ := SpecialLinearGroup.exists_sylow_fixing_line d.point d.point_dimension
  let P : Sylow 2 (D.star D.L) :=
    S.mapSurjective (f := d.model.symm.toMonoidHom) d.model.symm.surjective
  have hP : (P : Subgroup (D.star D.L)) = (D.star D.U).subgroupOf (D.star D.L) := by
    ext x
    change x ∈ (S : Subgroup SL(2,F)).map d.model.symm.toMonoidHom ↔ _
    rw [mem_map_equiv, hS, ← d.matrixU_eq_fixingSubgroup hUT hf]
    change d.model x ∈ ((D.star D.U).subgroupOf (D.star D.L)).map d.model.toMonoidHom ↔ _
    rw [mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply]
  exact ⟨P, by rw [hP, map_subgroupOf_eq_of_le (d.star_U_le_star_L hUT hf)]⟩

/-- The order assertion for the original quotient image, not an abstract tag. -/
theorem card_star_U (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : Nat.card (D.star D.U) = 2 ^ n := by
  calc
    Nat.card (D.star D.U) = Nat.card ((D.star D.U).subgroupOf (D.star D.L)) :=
      (Nat.card_congr (subgroupOfEquivOfLe (d.star_U_le_star_L hUT hf)).toEquiv).symm
    _ = Nat.card d.matrixU := Nat.card_congr
      (((D.star D.U).subgroupOf (D.star D.L)).equivMapOfInjective
        d.model.toMonoidHom d.model.injective).toEquiv
    _ = Nat.card F := by
      rw [d.matrixU_eq_fixingSubgroup hUT hf]
      exact SpecialLinearGroup.card_fixing_line d.point d.point_dimension
    _ = 2 ^ n := d.field_card

/-- The full relative normalizer equality on the literal starred subgroups. -/
theorem star_pointNormalizer_eq (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.star (D.L ⊓ D.G₁) = D.star D.L ⊓ normalizer (D.star D.U : Set D.Star) := by
  have he : (D.star (D.L ⊓ D.G₁)).subgroupOf (D.star D.L) =
      (normalizer (D.star D.U : Set D.Star)).subgroupOf (D.star D.L) := by
    apply Subgroup.map_injective (f := d.model.toMonoidHom) d.model.injective
    rw [d.pointNormalizer_model, subgroupOf_normalizer_eq (d.star_U_le_star_L hUT hf),
      map_equiv_normalizer_eq]
    change _ = normalizer (d.matrixU : Set SL(2,F))
    rw [d.matrixU_eq_fixingSubgroup hUT hf,
      SpecialLinearGroup.normalizer_fixing_line d.point d.point_dimension]
  apply le_antisymm
  · exact le_inf (binary_star_mono inf_le_left) d.pointNormalizer_star_normalizes_U
  · rintro x ⟨hxL, hxN⟩
    have hh : (⟨x, hxL⟩ : D.star D.L) ∈
        (normalizer (D.star D.U : Set D.Star)).subgroupOf (D.star D.L) := hxN
    rw [← he] at hh
    exact hh

/-- The original marked pair generates all of L* in the original quotient. -/
theorem star_I_eq_star_L (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : D.star (D.I g) = D.star D.L := by
  let : CharP F 2 := d.field_char_two
  let k : D.star D.L := starProjection D ⟨g, d.g_mem⟩
  let K := (D.star (D.I g)).subgroupOf (D.star D.L)
  let M := K.map d.model.toMonoidHom
  have hUM : d.matrixU ≤ M :=
    map_mono (comap_mono (binary_star_mono (show D.U ≤ D.I g from le_sup_left)))
  have hconj : d.matrixU.map (MulAut.conj (d.model k)⁻¹).toMonoidHom ≤ M := by
    rintro x ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨k⁻¹ * q * k, ?_, ?_⟩
    · obtain ⟨u, hu, he⟩ := hq
      let z : D.LT := ⟨g, mem_sup_left d.g_mem⟩
      have hc : ((z⁻¹ * u * z : D.LT) : G) ∈ D.I g := by
        apply (show conjugate D.U g ≤ D.I g from le_sup_right)
        exact ⟨u, hu, by simp [z]⟩
      refine ⟨z⁻¹ * u * z, hc, ?_⟩
      simp only [map_mul, map_inv]
      change _ = (k : D.Star)⁻¹ * (q : D.Star) * (k : D.Star)
      rw [he]
      rfl
    · change d.model (k⁻¹ * q * k) = (d.model k)⁻¹ * d.model q * ((d.model k)⁻¹)⁻¹
      simp only [map_mul, map_inv, inv_inv]
  have hgen : d.matrixU ⊔ d.matrixU.map (MulAut.conj (d.model k)⁻¹).toMonoidHom = ⊤ := by
    rw [d.matrixU_eq_fixingSubgroup hUT hf]
    exact SpecialLinearGroup.fixing_line_sup_right_conjugate d.point d.point_dimension
      (d.model k) d.marked_matrix_not_stabilizing
  have hM : M = ⊤ := top_unique (hgen ▸ sup_le hUM hconj)
  apply le_antisymm (d.star_I_le_star_L hUT hf)
  intro x hx
  have hm : d.model ⟨x, hx⟩ ∈ M := hM ▸ mem_top _
  change d.model ⟨x, hx⟩ ∈ K.map d.model.toMonoidHom at hm
  rw [mem_map_equiv] at hm
  exact (show (⟨x, hx⟩ : D.star D.L) ∈ K from by
    simpa only [MulEquiv.symm_apply_apply] using hm)

end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
