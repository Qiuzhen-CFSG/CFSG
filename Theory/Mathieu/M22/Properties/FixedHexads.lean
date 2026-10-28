module

public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.Basic

/-!
# Fixed hexads of involutions in the concrete M₂₂

An M₂₂ involution extends to an involution in the point-9 stabilizer of M₂₃.
The checked M₂₃ fusion theorem identifies its fixed points with a heptad.
The actual identification of the derived designs then removes point 9,
leaving a hexad in the original degree-22 action. Commuting permutations
preserve this hexad. Transitivity makes its stabilizer proper, and simplicity
then gives centerlessness.

This supplies the involution geometry used in Aschbacher–Smith 2.3.9(7)(f),
printed pp.525–526. The M₂₃ involution calculation is the checked model result
used for 5.2.21, printed p.657. No maximality or intersection with an ambient
local subgroup is asserted here.
-/

@[expose] public section

open scoped Pointwise
open Subgroup
namespace Sporadic.Mathieu

private theorem m23_exists_fixed_heptad (t : M23) (ht : orderOf t = 2) :
    ∃ D ∈ m23Blocks, ∀ x : Fin 23, t • x = x ↔ x ∈ D := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (M23Geometry.involutions_isConj
    M23Geometry.involutionRepresentative t M23Geometry.involutionRepresentative_order ht)
  let D := g • M23Geometry.involutionHeptad
  have hD : D ∈ m23Blocks := by
    have hm : (g : Equiv.Perm (Fin 23)) • M23Geometry.involutionHeptad ∈
        (g : Equiv.Perm (Fin 23)) • (m23Blocks : Set (Finset (Fin 23))) :=
      Set.smul_mem_smul_set M23Geometry.involutionHeptad_mem
    rw [(mem_M23_iff _).mp g.property] at hm
    exact hm
  refine ⟨D, hD, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    have hf : M23Geometry.involutionRepresentative • (g⁻¹ • x) = g⁻¹ • x := by
      have he := congrArg (fun y : Fin 23 => g⁻¹ • y) hx
      rw [← hg] at he
      simpa only [mul_smul, inv_smul_smul] using he
    exact Finset.mem_smul_finset.mpr ⟨g⁻¹ • x,
      (M23Geometry.involutionRepresentative_fixed_iff _).mp hf, smul_inv_smul g x⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hx
    rw [← hg]
    simp only [mul_smul, inv_smul_smul]
    rw [show M23Geometry.involutionRepresentative • y = y from
      (M23Geometry.involutionRepresentative_fixed_iff y).mpr hy]

/-- Every involution fixes exactly the six points of an actual hexad. -/
theorem m22_exists_fixed_hexad (t : M22) (ht : orderOf t = 2) :
    ∃ B ∈ m22Blocks, ∀ x : Fin 22, t • x = x ↔ x ∈ B := by
  let t' : M23 := m23EquivM22PointStabilizer t
  have ht' : orderOf t' = 2 := by
    rw [show orderOf t' = orderOf (m23EquivM22PointStabilizer t) from
      Subgroup.orderOf_coe _]
    exact (m23EquivM22PointStabilizer.orderOf_eq t).trans ht
  obtain ⟨D, hD, hfix⟩ := m23_exists_fixed_heptad t' ht'
  have h9 : (9 : Fin 23) ∈ D :=
    (hfix 9).mp (m23EquivM22PointStabilizer t).property
  have him : D ∈ m22Blocks.image m22M23AugmentedBlock := by
    rw [← m23Blocks_through_nine]
    exact Finset.mem_filter.mpr ⟨hD, h9⟩
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp him
  refine ⟨B, hB, fun x => ?_⟩
  have hact : t' • m22M23PointMap x = m22M23PointMap (t • x) := by
    change m22M23RelabelHom (t : Equiv.Perm (Fin 22)) (m22M23PointMap x) = _
    rw [m22M23RelabelHom_apply_of_ne_nine _ _ (m22M23PointMap_ne_nine x),
      m22M23PointMap_leftInverse]
    rfl
  have hf := hfix (m22M23PointMap x)
  rw [hact, m22M23PointMap_injective.eq_iff] at hf
  simpa [m22M23AugmentedBlock, m22M23LiftBlock, m22M23PointEmbedding,
    m22M23PointMap_ne_nine x] using hf

/-- The fixed points in the original natural degree-22 action. -/
noncomputable def m22FixedPoints (t : M22) : Finset (Fin 22) :=
  Finset.univ.filter fun x => t • x = x

theorem mem_m22FixedPoints (t : M22) (x : Fin 22) :
    x ∈ m22FixedPoints t ↔ t • x = x := by
  classical
  simp [m22FixedPoints]

/-- The fixed-point set of an involution belongs to the verified Witt design. -/
theorem m22FixedPoints_mem_blocks (t : M22) (ht : orderOf t = 2) :
    m22FixedPoints t ∈ m22Blocks := by
  obtain ⟨B, hB, hf⟩ := m22_exists_fixed_hexad t ht
  have he : m22FixedPoints t = B := by
    ext x
    exact (mem_m22FixedPoints t x).trans (hf x)
  rwa [he]

/-- Commuting permutations preserve the fixed-point set. -/
theorem m22_centralizer_le_fixedPoints_stabilizer (t : M22) :
    centralizer ({t} : Set M22) ≤ MulAction.stabilizer M22 (m22FixedPoints t) := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro x hx
  apply (mem_m22FixedPoints t _).mpr
  have hc := congrArg (fun k : M22 => k • x) (mem_centralizer_singleton_iff.mp hg)
  simpa only [mul_smul, (mem_m22FixedPoints t x).mp hx] using hc.symm

/-- Transitivity on 22 points makes every six-point stabilizer proper. -/
theorem m22_hexad_stabilizer_ne_top (B : Finset (Fin 22)) (hB : B ∈ m22Blocks) :
    MulAction.stabilizer M22 B ≠ ⊤ := by
  classical
  let : MulAction.IsPretransitive M22 (Fin 22) := m22_isPretransitive
  have hc := m22Blocks_card B hB
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  have hne : B ≠ Finset.univ := by
    intro he
    rw [he] at hc
    simp at hc
  obtain ⟨y, hy⟩ := not_forall.mp (mt Finset.eq_univ_iff_forall.mpr hne)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 x y
  intro htop
  have hgs : g ∈ MulAction.stabilizer M22 B := htop ▸ mem_top g
  apply hy
  rw [← hg]
  exact MulAction.mem_stabilizer_finset'.mp hgs hx

/-- The actual M₂₂ model is centerless. -/
theorem m22_center_eq_bot : center M22 = ⊥ := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  rcases (inferInstance : (center M22).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hA : orderOf m22GeneratorAInM22 = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact m22GeneratorA_order
    apply False.elim
    apply m22_hexad_stabilizer_ne_top _ (m22FixedPoints_mem_blocks _ hA)
    apply top_unique
    intro x _
    apply m22_centralizer_le_fixedPoints_stabilizer
    apply mem_centralizer_singleton_iff.mpr
    have hx : x ∈ center M22 := ht ▸ mem_top x
    exact (mem_center_iff.mp hx _).symm

end Sporadic.Mathieu

end
