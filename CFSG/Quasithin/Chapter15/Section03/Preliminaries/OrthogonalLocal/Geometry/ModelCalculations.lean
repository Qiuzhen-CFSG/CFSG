module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Planes

/-!
# Fixed spaces of the natural orthogonal Sylow action

For the literal action of `SL₂(2) ≀ C₂` on the sum of its two natural binary
planes, a Sylow two-subgroup fixes a line. Its plane stabilizer is an elementary
four-group, fixes a four-group of vectors, and fixes a line in each plane.
We construct a multiplicative equivalence from that actual stabilizer subgroup
to the binary plane. The pointwise stabilizer of either fixed line has even
index in the full actor.

Small kernel-checked calculations use the exposed dihedral embedding, with
quantifiers over its eight elements and the sixteen module vectors. Sylow
conjugacy transfers them through the actual conjugating actor: its action maps
fixed spaces and permutes the two coordinate planes. The final index argument
uses a nonidentity vector on the fixed line to force preservation of its plane,
whose setwise stabilizer already has index two.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.2(2) and
the definite-plane geometry preceding and used in 15.3.5–6, printed
pp.1121–1122 (PDF pp.1138–1139). Ambient transport and source assembly remain
with the parent geometry development.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03
open Subgroup
open scoped IsMulCommutative
namespace OrthogonalGeometry
local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector :=
  FourGroupMatrixCoordinates.naturalAction
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

private abbrev baseKernel : Subgroup OrthogonalActor :=
  (RegularWreathProduct.rightHom : OrthogonalActor →* OrthogonalPlaneIndex).ker
private abbrev standardPlaneSylow : Subgroup OrthogonalActor :=
  wreathTwoDihedralHom.range ⊓ baseKernel

private theorem mem_standard_fixed (v : OrthogonalVector) :
    v ∈ fixedVectors wreathTwoDihedralHom.range ↔
      ∀ x : DihedralGroup 4, wreathTwoDihedralHom x • v = v := by
  constructor
  · intro h x; exact h _ ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩; exact h x

private theorem mem_standard_plane_fixed (v : OrthogonalVector) :
    v ∈ fixedVectors standardPlaneSylow ↔
      ∀ x : DihedralGroup 4, (wreathTwoDihedralHom x).right = 1 →
        wreathTwoDihedralHom x • v = v := by
  constructor
  · intro h x hx; exact h _ ⟨⟨x, rfl⟩, hx⟩
  · rintro h _ ⟨⟨x, rfl⟩, hx⟩; exact h x hx

set_option maxRecDepth 10000 in
private theorem standard_fixed_card : Nat.card (fixedVectors wreathTwoDihedralHom.range) = 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight mem_standard_fixed), Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 10000 in
private theorem standard_plane_fixed_card : Nat.card (fixedVectors standardPlaneSylow) = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight mem_standard_plane_fixed), Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 10000 in
private theorem standard_line_card (i : OrthogonalPlaneIndex) :
    Nat.card ↥(orthogonalCoordinatePlane i ⊓ fixedVectors standardPlaneSylow) = 2 := by
  let e := Equiv.subtypeEquivRight (fun v : OrthogonalVector =>
    and_congr (Iff.rfl : (∀ j, j ≠ i → v j = 1) ↔ _) (mem_standard_plane_fixed v))
  change Nat.card {v : OrthogonalVector //
    (∀ j, j ≠ i → v j = 1) ∧ v ∈ fixedVectors standardPlaneSylow} = 2
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  have h : ∀ i : OrthogonalPlaneIndex, Fintype.card {v : OrthogonalVector //
    (∀ j, j ≠ i → v j = 1) ∧ ∀ x : DihedralGroup 4,
      (wreathTwoDihedralHom x).right = 1 → wreathTwoDihedralHom x • v = v} = 2 := by
    decide +kernel
  exact h i

private theorem fixedVectors_map_conj (g : OrthogonalActor) (H : Subgroup OrthogonalActor) :
    fixedVectors (H.map (MulAut.conj g).toMonoidHom) =
      (fixedVectors H).map (MulDistribMulAction.toMulEquiv OrthogonalVector g).toMonoidHom := by
  apply le_antisymm
  · intro v hv
    refine ⟨g⁻¹ • v, ?_, smul_inv_smul g v⟩
    intro x hx
    apply MulAction.injective g
    have h := hv ((MulAut.conj g) x) ⟨x, hx, rfl⟩
    simpa only [MulAut.conj_apply, mul_smul, smul_inv_smul] using h
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨x, hx, rfl⟩
    change (g * x * g⁻¹) • (g • v) = g • v
    simp only [mul_smul, inv_smul_smul, hv x hx]

private theorem map_plane (g : OrthogonalActor) (i : OrthogonalPlaneIndex) :
    (orthogonalCoordinatePlane i).map
      (MulDistribMulAction.toMulEquiv OrthogonalVector g).toMonoidHom =
      orthogonalCoordinatePlane (g.right * i) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩ j hj
    change g.left j • v (g.right⁻¹ * j) = 1
    rw [hv _ (by intro h; apply hj; rw [← h, mul_inv_cancel_left]), smul_one]
  · intro v hv
    refine ⟨g⁻¹ • v, ?_, smul_inv_smul g v⟩
    intro j hj
    change (g⁻¹).left j • v ((g⁻¹).right⁻¹ * j) = 1
    rw [show (g⁻¹).right⁻¹ = g.right by simp]
    rw [hv _ (fun h => hj (mul_left_cancel h)), smul_one]

private theorem map_baseKernel (g : OrthogonalActor) :
    baseKernel.map (MulAut.conj g).toMonoidHom = baseKernel := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change (g * x * g⁻¹).right = 1
    change x.right = 1 at hx
    simp [hx]
  · intro x hx
    refine ⟨(MulAut.conj g).symm x, ?_, (MulAut.conj g).apply_symm_apply x⟩
    change (g⁻¹ * x * g).right = 1
    change x.right = 1 at hx
    simp [hx]

private theorem exists_sylow_map (P : Sylow 2 OrthogonalActor) :
    ∃ g : OrthogonalActor,
      (P : Subgroup OrthogonalActor) = wreathTwoDihedralHom.range.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq OrthogonalActor wreathTwoSylow P
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, wreathTwoSylow_coe]
  rfl

private theorem plane_sylow_map (g : OrthogonalActor) (i : OrthogonalPlaneIndex) :
    wreathTwoDihedralHom.range.map (MulAut.conj g).toMonoidHom ⊓
      setwise (orthogonalCoordinatePlane i) =
        standardPlaneSylow.map (MulAut.conj g).toMonoidHom := by
  rw [setwise_plane_eq_ker, map_inf _ _ _ (MulAut.conj g).injective, map_baseKernel]

/-- Every Sylow actor fixes exactly one nonidentity vector in the natural module. -/
theorem sylow_fixedVectors_card (P : Sylow 2 OrthogonalActor) :
    Nat.card (fixedVectors P) = 2 := by
  obtain ⟨g, hg⟩ := exists_sylow_map P
  rw [hg, fixedVectors_map_conj,
    card_map_of_injective (f := (MulDistribMulAction.toMulEquiv OrthogonalVector g).toMonoidHom)
      (MulDistribMulAction.toMulEquiv OrthogonalVector g).injective]
  exact standard_fixed_card

/-- The plane-preserving part of a Sylow actor fixes a four-group of vectors. -/
theorem plane_sylow_fixedVectors_card (P : Sylow 2 OrthogonalActor)
    (i : OrthogonalPlaneIndex) :
    Nat.card (fixedVectors ((P : Subgroup OrthogonalActor) ⊓
      setwise (orthogonalCoordinatePlane i))) = 4 := by
  obtain ⟨g, hg⟩ := exists_sylow_map P
  rw [hg, plane_sylow_map, fixedVectors_map_conj,
    card_map_of_injective (f := (MulDistribMulAction.toMulEquiv OrthogonalVector g).toMonoidHom)
      (MulDistribMulAction.toMulEquiv OrthogonalVector g).injective]
  exact standard_plane_fixed_card

set_option maxRecDepth 10000 in
private theorem standard_plane_square (x : OrthogonalActor) (hx : x ∈ standardPlaneSylow) :
    x ^ 2 = 1 := by
  obtain ⟨⟨y, rfl⟩, hy⟩ := hx
  have h : ∀ y : DihedralGroup 4, (wreathTwoDihedralHom y).right = 1 →
      y ^ 2 = 1 := by decide +kernel
  rw [← map_pow, h y hy, map_one]

/-- The actual plane-stabilizer subgroup is elementary abelian. -/
theorem plane_sylow_elementary (P : Sylow 2 OrthogonalActor) (i : OrthogonalPlaneIndex) :
    IsElementaryAbelian 2 ↥((P : Subgroup OrthogonalActor) ⊓
      setwise (orthogonalCoordinatePlane i)) := by
  refine {
    toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (p := 2) (plane_sylow_card P i)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  obtain ⟨g, hg⟩ := exists_sylow_map P
  have hx := x.property
  simp only [hg, plane_sylow_map] at hx
  obtain ⟨y, hy, he⟩ := hx
  change (x : OrthogonalActor) ^ 2 = 1
  rw [← he, ← map_pow, standard_plane_square y hy, map_one]

/-- Coordinates on the actual order-four subgroup as the multiplicative binary plane. -/
theorem plane_sylow_mulEquiv (P : Sylow 2 OrthogonalActor) (i : OrthogonalPlaneIndex) :
    Nonempty (↥((P : Subgroup OrthogonalActor) ⊓ setwise (orthogonalCoordinatePlane i)) ≃*
      OrthogonalPlaneVector) := by
  classical
  let Q := (P : Subgroup OrthogonalActor) ⊓ setwise (orthogonalCoordinatePlane i)
  let _ := plane_sylow_elementary P i
  have hdim : Module.finrank (ZMod 2) (Additive Q) = 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
    change Nat.card Q = _ at hsize
    rw [plane_sylow_card P i, Nat.card_zmod] at hsize
    exact Nat.pow_right_injective (by decide : 1 < 2) hsize.symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive Q) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

/-- The fixed four-group meets each definite plane in a line of order two. -/
theorem plane_sylow_fixed_line_card (P : Sylow 2 OrthogonalActor)
    (i : OrthogonalPlaneIndex) :
    Nat.card ↥(orthogonalCoordinatePlane i ⊓ fixedVectors
      ((P : Subgroup OrthogonalActor) ⊓ setwise (orthogonalCoordinatePlane i))) = 2 := by
  obtain ⟨g, hg⟩ := exists_sylow_map P
  rw [hg, plane_sylow_map, fixedVectors_map_conj]
  have he := map_plane g (g.right⁻¹ * i)
  rw [mul_inv_cancel_left] at he
  rw [← he, ← map_inf _ _ (MulDistribMulAction.toMulEquiv OrthogonalVector g).toMonoidHom
      (MulDistribMulAction.toMulEquiv OrthogonalVector g).injective,
    card_map_of_injective (f := (MulDistribMulAction.toMulEquiv OrthogonalVector g).toMonoidHom)
      (MulDistribMulAction.toMulEquiv OrthogonalVector g).injective]
  exact standard_line_card _

private theorem pointwise_le_plane {A : Subgroup OrthogonalVector} (i : OrthogonalPlaneIndex)
    (hA : A ≤ orthogonalCoordinatePlane i) (hne : A ≠ ⊥) :
    pointwise A ≤ setwise (orthogonalCoordinatePlane i) := by
  obtain ⟨v, hv⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hvi : (v : OrthogonalVector) i ≠ 1 := by
    intro hi
    apply hv
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · change (v : OrthogonalVector) j = 1
      simpa only [hj] using hi
    · exact hA v.property j hj
  intro g hg
  apply (mem_setwise_plane_iff g i).mpr
  by_contra hright
  have hj : g.right * i ≠ i := by
    intro h
    exact hright (mul_right_cancel (h.trans (one_mul i).symm))
  have he := congrFun (hg v v.property) (g.right * i)
  change g.left (g.right * i) • (v : OrthogonalVector) (g.right⁻¹ * (g.right * i)) =
    (v : OrthogonalVector) (g.right * i) at he
  rw [inv_mul_cancel_left, hA v.property _ hj] at he
  exact hvi (MulAction.injective _ (he.trans (smul_one _).symm))

/-- The fixed-line pointwise stabilizer has even index in the actual orthogonal actor. -/
theorem plane_sylow_fixed_line_pointwise_even_index (P : Sylow 2 OrthogonalActor)
    (i : OrthogonalPlaneIndex) :
    2 ∣ (pointwise (orthogonalCoordinatePlane i ⊓ fixedVectors
      ((P : Subgroup OrthogonalActor) ⊓ setwise (orthogonalCoordinatePlane i)))).index := by
  have hne : orthogonalCoordinatePlane i ⊓ fixedVectors
      ((P : Subgroup OrthogonalActor) ⊓ setwise (orthogonalCoordinatePlane i)) ≠ ⊥ := by
    intro h
    have hc := plane_sylow_fixed_line_card P i
    rw [(card_eq_one.mpr h)] at hc
    omega
  have h := index_dvd_of_le (pointwise_le_plane i inf_le_left hne)
  rwa [setwise_plane_index] at h

end OrthogonalGeometry
end CFSG.Quasithin.Chapter15.Section03

end
