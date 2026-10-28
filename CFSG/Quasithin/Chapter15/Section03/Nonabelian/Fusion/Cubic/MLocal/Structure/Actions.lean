module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Marking

/-!
# The orthogonal U-image excludes fixed hyperplanes

The source conclusion 15.3.51(2a) identifies the actual image of U as the
other elementary four-group in the orthogonal Sylow group. Such a group
contains a plane-interchanging actor. Its elements commute with that actor
and have square one. A calculation on the eight-element dihedral model
then shows that none fixes a hyperplane in the sixteen-element module.
Sylow conjugacy and the specified natural action transport this statement
to C_V(u) for each actual u in U = ⟨Z_S^{C_G(Z)}⟩.

This proves the U-action input to `MLocal.local_witnesses_of_symmetric_factor`
from the genuine earlier image conclusion. It does not construct the
symmetric factor or assume the desired fixed-space inequality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.51(2a)
and 15.3.53(1), printed pp.1145–1146; application before 15.3.60, p.1150.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
open OrthogonalGeometry
local instance actionsOrthogonalAction : MulDistribMulAction OrthogonalActor OrthogonalVector :=
  orthogonalAction

set_option maxRecDepth 4000 in
private theorem standard_other_four_fixed : ∀ a b : DihedralGroup 4,
    a ^ 2 = 1 → a * b = b * a →
      (wreathTwoDihedralHom b).right ≠ 1 →
      Fintype.card {v : OrthogonalVector // wreathTwoDihedralHom a • v = v} ≠ 8 := by
  decide +kernel

/-- Conjugate actors have equally many fixed vectors in the same action. -/
theorem card_fixed_conjugate (a g : OrthogonalActor) :
    Nat.card {v : OrthogonalVector // (MulAut.conj g a) • v = v} =
      Nat.card {v : OrthogonalVector // a • v = v} := by
  apply (Nat.card_congr _).symm
  apply Equiv.subtypeEquiv (MulDistribMulAction.toMulEquiv OrthogonalVector g).toEquiv
  intro v
  change a • v = v ↔ (g * a * g⁻¹) • (g • v) = g • v
  rw [mul_smul, mul_smul, inv_smul_smul, (MulAction.injective g).eq_iff]

/-- The non-plane elementary four-group in an orthogonal Sylow group has
no element fixing a hyperplane. This is the action assertion in 15.3.51(2a). -/
theorem other_four_no_hyperplane (P : Sylow 2 OrthogonalActor)
    (R : Subgroup OrthogonalActor) [IsElementaryAbelian 2 R]
    (hRP : R ≤ (P : Subgroup OrthogonalActor)) (hR : Nat.card R = 4)
    (i : OrthogonalPlaneIndex)
    (hne : R ≠ (P : Subgroup OrthogonalActor) ⊓ setwise (orthogonalCoordinatePlane i)) :
    ∀ a ∈ R, Nat.card {v : OrthogonalVector // a • v = v} ≠ 8 := by
  have hnot : ¬ R ≤ setwise (orthogonalCoordinatePlane i) := by
    intro h
    exact hne (eq_of_le_of_card_ge (le_inf hRP h) (by rw [plane_sylow_card, hR]))
  obtain ⟨b, hb, hbout⟩ := SetLike.not_le_iff_exists.mp hnot
  have hbright : b.right ≠ 1 := fun h => hbout ((mem_setwise_plane_iff b i).mpr h)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq OrthogonalActor wreathTwoSylow P
  have hP : (P : Subgroup OrthogonalActor) =
      wreathTwoDihedralHom.range.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, wreathTwoSylow_coe]
    rfl
  have hbP := hRP hb
  rw [hP] at hbP
  obtain ⟨_, ⟨b₀, rfl⟩, rfl⟩ := hbP
  have hb₀right : (wreathTwoDihedralHom b₀).right ≠ 1 := by
    intro h
    apply hbright
    change (g * wreathTwoDihedralHom b₀ * g⁻¹).right = 1
    simp [h]
  intro a ha
  have haP := hRP ha
  rw [hP] at haP
  obtain ⟨_, ⟨a₀, rfl⟩, rfl⟩ := haP
  have hinj := (MulAut.conj g).injective.comp wreathTwoDihedralHom_injective
  have hpow : a₀ ^ 2 = 1 := by
    apply hinj
    change (MulAut.conj g) (wreathTwoDihedralHom (a₀ ^ 2)) =
      (MulAut.conj g) (wreathTwoDihedralHom 1)
    rw [map_pow, map_pow, map_one, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2)
      ((MulAut.conj g) (wreathTwoDihedralHom a₀)) ha
  have hcomm : a₀ * b₀ = b₀ * a₀ := by
    apply hinj
    change (MulAut.conj g) (wreathTwoDihedralHom (a₀ * b₀)) =
      (MulAut.conj g) (wreathTwoDihedralHom (b₀ * a₀))
    rw [map_mul, map_mul, map_mul, map_mul]
    exact congrArg (fun x : R => (x : OrthogonalActor))
      (mul_comm (⟨_, ha⟩ : R) ⟨_, hb⟩)
  change Nat.card {v : OrthogonalVector //
    (MulAut.conj g (wreathTwoDihedralHom a₀)) • v = v} ≠ 8
  rw [card_fixed_conjugate, Nat.card_eq_fintype_card]
  exact standard_other_four_fixed a₀ b₀ hpow hcomm hb₀right

variable {G : Type*} [Group G] {M V : Subgroup G}

/-- The cyclic ambient actor maps to the cyclic subgroup of its actual image. -/
theorem image_zpowers (d : NaturalOrthogonalAction M V) (m : M) :
    d.image (zpowers (m : G)) = zpowers (d.actor m) := by
  have h : (zpowers (m : G)).subgroupOf M = zpowers m := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr m.property), MonoidHom.map_zpowers]
    rfl
  rw [NaturalOrthogonalAction.image, h, MonoidHom.map_zpowers]

/-- Fixed-space cardinality for one ambient element, with the prescribed action. -/
theorem card_fixedPlane_zpowers (d : NaturalOrthogonalAction M V) (m : M) :
    Nat.card (fixedPlane V (zpowers (m : G))) =
      Nat.card {v : OrthogonalVector // d.actor m • v = v} := by
  rw [d.card_fixedPlane (zpowers_le.mpr m.property), image_zpowers]
  apply Nat.card_congr (Equiv.subtypeEquivRight _)
  intro v
  exact ⟨fun h => h _ (mem_zpowers _),
    fun h _ hg => smul_eq_self_of_mem_zpowers hg h⟩

/-- The exact U-image conclusion of 15.3.51(2a) gives the action premise
required by the cubic-centralizer involution construction. -/
theorem closureU_no_hyperplane [Finite G] (d : NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex)
    (Z ZS : Subgroup G) (hUT : closureU Z ZS ≤ (T : Subgroup G))
    [IsElementaryAbelian 2 (d.image (closureU Z ZS))]
    (hcard : Nat.card (d.image (closureU Z ZS)) = 4)
    (hne : d.image (closureU Z ZS) ≠ d.image (planeStabilizer T (d.plane i))) :
    ∀ u ∈ closureU Z ZS, Nat.card (fixedPlane V (zpowers u)) ≠ 8 := by
  have hle : d.image (closureU Z ZS) ≤ (d.sylowImage T hTM : Subgroup OrthogonalActor) :=
    map_mono (comap_mono hUT)
  rw [d.image_planeStabilizer] at hne
  intro u hu
  rw [card_fixedPlane_zpowers d ⟨u, hTM (hUT hu)⟩]
  exact other_four_no_hyperplane (d.sylowImage T hTM) _ hle hcard i hne _
    (mem_map_of_mem d.actor (show (⟨u, hTM (hUT hu)⟩ : M) ∈
      (closureU Z ZS).subgroupOf M from hu))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
