module

public import Theory.SpecificGroups.PSL3.CartanActions
import Mathlib.GroupTheory.Complement

/-!
# Three-subgroups in the upper Borel of PSL₃

Every upper triangular determinant-one matrix factors as an upper
unitriangular matrix followed by `diag(a, (ab)⁻¹, b)`. These two subgroups
complement each other inside the SL₃ Borel, so the diagonal subgroup has
index q³. The surjective projection to the projective Borel shows that the
projective torus index divides q³, including when the scalar kernel has
order three. For q a power of two, a Sylow three-subgroup of the torus is
therefore Sylow in the Borel. Sylow conjugacy inside the Borel aligns any
three-subgroup with the torus while preserving the unipotent group.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`). The Sylow-index argument also occurs
for the concrete G₂ Borel in `Theory.AtlasPort.LinearGroups.G2.OddSubgroupPlacement`.
The present factorization uses the existing PSL₃ matrix model directly.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree
namespace Matrix.PSL3.CartanActions.ThreeAlignment

variable (F : Type*) [Field F] [Finite F]

private theorem borelSL_factorization (g : SL(3,F)) (hg : g ∈ borelSL F) :
    ∃ d : Fˣ × Fˣ, ∃ u ∈ unipotentSL F, g = u * torusSL F d := by
  obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F g).mp hg
  have hd : g.val 0 0 * g.val 1 1 * g.val 2 2 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_three, h10,h20,h21] at h
    simpa only [zero_mul, mul_zero, add_zero, sub_zero] using h
  have h00 : g.val 0 0 ≠ 0 := by intro h; simp [h] at hd
  have h22 : g.val 2 2 ≠ 0 := by intro h; simp [h] at hd
  let d : Fˣ × Fˣ := (Units.mk0 _ h00, Units.mk0 _ h22)
  refine ⟨d, g * torusSL F d⁻¹, ?_, ?_⟩
  · rw [unipotentSL, mem_inf, mem_pointLocalSL_iff, mem_lineLocalSL_iff]
    simp [torusSL_val, Matrix.mul_diagonal,
      d, h00,h22,h10,h20,h21]
  · simp only [map_inv, mul_assoc, inv_mul_cancel, mul_one]

omit [Finite F] in
private theorem unipotentSL_disjoint_torusSL : Disjoint (unipotentSL F) (torusSL F).range := by
  rw [Subgroup.disjoint_def]
  rintro x hx ⟨d,rfl⟩
  have h00 := ((mem_pointLocalSL_iff F _).mp hx.1).1
  have h22 := ((mem_lineLocalSL_iff F _).mp hx.2).2.2
  have hd : d = 1 := Prod.ext (Units.ext h00) (Units.ext h22)
  rw [hd, map_one]

private theorem torusSL_mem_borel (d : Fˣ × Fˣ) : torusSL F d ∈ borelSL F := by
  rw [mem_borelSL_iff, torusSL_val]
  simp

private theorem borelSL_complement :
    ((unipotentSL F).subgroupOf (borelSL F)).IsComplement'
      ((torusSL F).range.subgroupOf (borelSL F)) := by
  refine ⟨Subgroup.mul_injective_of_disjoint ?_, ?_⟩
  · rw [Subgroup.disjoint_def]
    intro x hx hy
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp (unipotentSL_disjoint_torusSL F)) hx hy
  · intro g
    obtain ⟨d,u,hu,hg⟩ := borelSL_factorization F g.val g.property
    refine ⟨(⟨⟨u,unipotentSL_le_borelSL F hu⟩,hu⟩,
      ⟨⟨torusSL F d,torusSL_mem_borel F d⟩,⟨d,rfl⟩⟩), ?_⟩
    exact Subtype.ext hg.symm

private theorem torusSL_index :
    ((torusSL F).range.subgroupOf (borelSL F)).index = Nat.card F ^ 3 := by
  rw [(borelSL_complement F).index_eq_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (unipotentSL_le_borelSL F)).toEquiv,
    card_unipotentSL]

/-- The projective split torus has index dividing q³ in the upper Borel.
This uses the surjective Borel projection and allows a nontrivial scalar kernel. -/
theorem torus_index_dvd :
    ((torus F).subgroupOf (borel F)).index ∣ Nat.card F ^ 3 := by
  let π : borelSL F →* borel F := (projection F).subgroupMap (borelSL F)
  have hmap : ((torusSL F).range.subgroupOf (borelSL F)).map π =
      (torus F).subgroupOf (borel F) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨d,hd⟩ := hy
      exact ⟨d,congrArg (projection F) hd⟩
    · rintro ⟨d,hd⟩
      refine ⟨⟨torusSL F d,torusSL_mem_borel F d⟩,⟨d,rfl⟩,?_⟩
      exact Subtype.ext hd
  have h := (((torusSL F).range.subgroupOf (borelSL F))).index_map_dvd
    ((projection F).subgroupMap_surjective (borelSL F))
  change (((torusSL F).range.subgroupOf (borelSL F)).map π).index ∣ _ at h
  rwa [hmap,torusSL_index] at h

private theorem conjugate_threeSubgroup_into {G : Type*} [Group G] [Finite G]
    (H B : Subgroup G) (hH : ¬ 3 ∣ H.index) (hB : IsPGroup 3 B) :
    ∃ g : G, B.map (MulAut.conj g).toMonoidHom ≤ H := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := H)
  have hm : ¬ 3 ∣ ((P : Subgroup H).map H.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out P.not_dvd_index hH
  let Q : Sylow 3 G := (P.isPGroup'.map H.subtype).toSylow hm
  obtain ⟨R, hR⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R Q
  refine ⟨g, ?_⟩
  have hmap : (R : Subgroup G).map (MulAut.conj g).toMonoidHom = Q :=
    congrArg Sylow.toSubgroup hg
  exact (map_mono hR).trans (hmap ▸ map_subtype_le (P : Subgroup H))

/-- Sylow conjugacy inside the upper Borel puts a three-subgroup into the
split torus. The conjugating element remains in the Borel. -/
theorem conjugate_borel_threeSubgroup_into_torus {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (B : Subgroup PSL(3,F))
    (hB : IsPGroup 3 B) (hBb : B ≤ borel F) :
    ∃ g ∈ borel F, B.map (MulAut.conj g).toMonoidHom ≤ torus F := by
  have hind : ¬ 3 ∣ ((torus F).subgroupOf (borel F)).index := by
    intro h
    have hd := h.trans (torus_index_dvd F)
    rw [hF] at hd
    exact (by decide : ¬ 3 ∣ 2)
      (Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow hd))
  have hPB : IsPGroup 3 (B.subgroupOf (borel F)) :=
    hB.of_injective (subgroupOfEquivOfLe hBb).toMonoidHom
      (subgroupOfEquivOfLe hBb).injective
  obtain ⟨g, hg⟩ := conjugate_threeSubgroup_into ((torus F).subgroupOf (borel F))
    (B.subgroupOf (borel F)) hind hPB
  refine ⟨g, g.property, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  exact hg (mem_map_of_mem (MulAut.conj g).toMonoidHom
    (show (⟨b, hBb hb⟩ : borel F) ∈ B.subgroupOf (borel F) from hb))

end Matrix.PSL3.CartanActions.ThreeAlignment
