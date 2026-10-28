module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.Definitions
public import Theory.Mathieu.M12.SmallParabolicPair.Centralizers
public import Theory.GroupTheory.CentralBinaryKernelSquares

/-!
# Transport from the symplectic core of an M₁₂ cover

The intermediate `CoreLiftData` specifies the common symplectic-core paragraph
of I.2.2: full preimages, the center of the lifted core, and the residual's
trivial action on that center. It does not assume coordinates, a square form,
or any equality between the two quaternion-axis squares. Its construction
from the quasisimple-cover hypotheses remains a separate obligation.

The results below pull back the marked quotient coordinates along the literal
central quotient map. In particular, exponent four and the square marking
follow from these maps, without any choice of a model for the covering group.

Source: Aschbacher–Smith, I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Theory.LinearAlgebra.BinaryCubicOrbits
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
namespace CoverCoordinates
variable {K : Type*} [Group K]

/-- The actual projection, followed by the supplied M₁₂ identification. -/
def projection (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12) :
    K →* Sporadic.Mathieu.M12 := e.toMonoidHom.comp (QuotientGroup.mk' (center K))

theorem projection_surjective (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12) :
    Function.Surjective (projection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

@[simp] theorem projection_eq_one (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12)
    (x : K) : projection e x = 1 ↔ x ∈ center K := by
  change e (QuotientGroup.mk' (center K) x) = 1 ↔ _
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- Uncoordinatized output of the common symplectic-core argument. This is an
intermediate construction contract, not an additional source hypothesis. -/
structure CoreLiftData (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12) (u : K) : Prop where
  centralizer_image : (centralizer ({u} : Set K)).map (projection e) =
    Sporadic.Mathieu.M12SmallPair.firstParabolic
  core_preimage : centralizerCore u =
    Sporadic.Mathieu.M12SmallPair.core.comap (projection e)
  center_preimage : ∀ r : centralizerCore u, r ∈ center (centralizerCore u) ↔
    projection e r = 1 ∨ projection e r = Sporadic.Mathieu.M12SmallPair.z
  center_square : ∀ r : centralizerCore u, r ∈ center (centralizerCore u) → r ^ 2 = 1
  residual_fixes_center : ∀ (x : centralizerTwoResidual u) (r : centralizerCore u),
    r ∈ center (centralizerCore u) → Commute (x : K) (r : K)

/-- The core is normal in the literal residual, not necessarily in K. -/
theorem core_normalized (u : K) : centralizerTwoResidual u ≤
    normalizer (centralizerCore u : Set K) := by
  let : ((centralizerCore u).subgroupOf (centralizerTwoResidual u)).Characteristic :=
    centralizerResidualCore_characteristic u
  have hle : centralizerCore u ≤ centralizerTwoResidual u := map_subtype_le _
  exact (normal_subgroupOf_iff_le_normalizer hle).mp
    (inferInstance : ((centralizerCore u).subgroupOf (centralizerTwoResidual u)).Normal)

def residualAction (u : K) : centralizerTwoResidual u →* MulAut (centralizerCore u) :=
  (centralizerCore u).normalizerMonoidHom.comp (Subgroup.inclusion (core_normalized u))

theorem residualAction_apply (u : K) (a : centralizerTwoResidual u)
    (r : centralizerCore u) :
    (residualAction u a r : K) = (a : K) * r * (a : K)⁻¹ := rfl

variable {e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12} {u : K}
variable (d : CoreLiftData e u) (m : Sporadic.Mathieu.M12SmallPair.CoverOrbitData)

namespace CoreLiftData
include d

theorem core_image_mem (r : centralizerCore u) :
    projection e r ∈ Sporadic.Mathieu.M12SmallPair.core := by
  exact d.core_preimage.le r.property

def coreMap : centralizerCore u →* Sporadic.Mathieu.M12SmallPair.core :=
  ((projection e).comp (centralizerCore u).subtype).codRestrict _ d.core_image_mem

theorem coreMap_surjective : Function.Surjective d.coreMap := by
  intro r
  obtain ⟨x, hx⟩ := projection_surjective e r.val
  have hxr : x ∈ centralizerCore u := by
    rw [d.core_preimage, mem_comap, hx]
    exact r.property
  exact ⟨⟨x, hxr⟩, Subtype.ext hx⟩

def coordinates : centralizerCore u →* Multiplicative Space :=
  m.coordinates.comp d.coreMap

theorem coordinates_surjective : Function.Surjective (d.coordinates m) :=
  m.coordinates_surjective.comp d.coreMap_surjective

theorem coordinates_ker : (d.coordinates m).ker = center (centralizerCore u) := by
  ext r
  change m.coordinates (d.coreMap r) = 1 ↔ _
  rw [← MonoidHom.mem_ker, m.coordinates_ker,
    Sporadic.Mathieu.M12SmallPair.core_center_mem, d.center_preimage]
  rfl

include m in
theorem square_central (r : centralizerCore u) : r ^ 2 ∈ center (centralizerCore u) := by
  rw [← d.coordinates_ker m, MonoidHom.mem_ker, map_pow]
  have h : ∀ v : Multiplicative Space, v ^ 2 = 1 := by decide +kernel
  exact h _

include m in
theorem fourth_power (r : centralizerCore u) : r ^ 4 = 1 := by
  have h := d.center_square (r ^ 2) (d.square_central m r)
  simpa only [← pow_mul] using h

theorem ambient_center_le : center K ≤ centralizerCore u := by
  intro x hx
  rw [d.core_preimage, mem_comap, (projection_eq_one e x).mpr hx]
  exact one_mem _

theorem involution (hu : projection e u = Sporadic.Mathieu.M12SmallPair.z) :
    orderOf u = 2 := by
  have huR : u ∈ centralizerCore u := by
    rw [d.core_preimage, mem_comap, hu]
    exact Sporadic.Mathieu.M12SmallPair.z_mem_core
  have hs := d.center_square ⟨u, huR⟩ ((d.center_preimage _).mpr (Or.inr hu))
  apply orderOf_eq_prime (congrArg Subtype.val hs)
  intro h
  change u = 1 at h
  have hz : Sporadic.Mathieu.M12SmallPair.z = 1 := by
    rw [h, map_one] at hu
    exact hu.symm
  have ho := Sporadic.Mathieu.M12SmallPair.z_order
  rw [hz, orderOf_one] at ho
  contradiction

theorem square_over_u (hu : projection e u = Sporadic.Mathieu.M12SmallPair.z)
    (r : centralizerCore u) :
    QuotientGroup.mk' (center K) ((r : K) ^ 2) = QuotientGroup.mk' (center K) u ↔
      quaternionSquare ((d.coordinates m r).toAdd) = 1 := by
  rw [← e.injective.eq_iff]
  change projection e ((r : K) ^ 2) = projection e u ↔ _
  rw [map_pow, hu]
  exact m.square_mark (d.coreMap r)

/-- Choose the fourth-orbit root only after pulling back the model coordinates. -/
def root : centralizerCore u :=
  (d.coordinates_surjective m (Multiplicative.ofAdd (rep 3))).choose

theorem root_coordinates : (d.coordinates m (d.root m)).toAdd = rep 3 :=
  congrArg Multiplicative.toAdd
    (d.coordinates_surjective m (Multiplicative.ofAdd (rep 3))).choose_spec

theorem root_square_image : projection e ((d.root m : K) ^ 2) =
    Sporadic.Mathieu.M12SmallPair.z := by
  rw [map_pow]
  apply (m.square_mark (d.coreMap (d.root m))).mpr
  change quaternionSquare ((d.coordinates m (d.root m)).toAdd) = 1
  rw [d.root_coordinates m]
  decide +kernel

theorem center_eq : center (centralizerCore u) =
    zpowers (d.root m ^ 2) ⊔ (center K).subgroupOf (centralizerCore u) := by
  apply le_antisymm
  · intro r hr
    rcases (d.center_preimage r).mp hr with h | h
    · exact (show (center K).subgroupOf (centralizerCore u) ≤ _ from le_sup_right)
        ((projection_eq_one e r).mp h)
    · have hk : r * (d.root m ^ 2)⁻¹ ∈
          (center K).subgroupOf (centralizerCore u) := by
        change (r : K) * ((d.root m : K) ^ 2)⁻¹ ∈ center K
        rw [← projection_eq_one e, map_mul, map_inv, d.root_square_image m, h,
          mul_inv_cancel]
      have hp := (zpowers (d.root m ^ 2) ⊔
        (center K).subgroupOf (centralizerCore u)).mul_mem
        ((show (center K).subgroupOf (centralizerCore u) ≤ _ from le_sup_right) hk)
        ((show zpowers (d.root m ^ 2) ≤ _ from le_sup_left) (mem_zpowers _))
      simpa only [inv_mul_cancel_right] using hp
  · refine sup_le (zpowers_le.mpr (d.square_central m _)) ?_
    intro r hr
    apply mem_center_iff.mpr
    intro s
    exact Subtype.ext (mem_center_iff.mp hr s.val)

theorem ambient_center_card (hZ : Nat.card (center K) = 2) :
    Nat.card ((center K).subgroupOf (centralizerCore u)) = 2 :=
  (Nat.card_congr (subgroupOfEquivOfLe d.ambient_center_le).toEquiv).trans hZ

theorem root_square_not_mem_ambient_center :
    d.root m ^ 2 ∉ (center K).subgroupOf (centralizerCore u) := by
  intro h
  have he := (projection_eq_one e ((d.root m : K) ^ 2)).mpr h
  rw [d.root_square_image m] at he
  have ho := Sporadic.Mathieu.M12SmallPair.z_order
  rw [he, orderOf_one] at ho
  contradiction



theorem residual_image [Finite K] : (centralizerTwoResidual u).map (projection e) =
    Sporadic.Mathieu.M12SmallPair.coverResidual := by
  rw [centralizerTwoResidual, map_embedded_pResidual, d.centralizer_image]
  rfl

omit d in
/-- The order-two kernel is of exponent two, with no finiteness computation. -/
theorem ambient_center_square (hZ : Nat.card (center K) = 2) (z : K)
    (hz : z ∈ center K) : z ^ 2 = 1 := by
  have h := pow_card_eq_one' (x := (⟨z, hz⟩ : center K))
  rw [hZ] at h
  exact congrArg Subtype.val h

/-- A cubic element of the residual image has a cubic lift in that same residual. -/
theorem exists_cubic_lift [Finite K] (hZ : Nat.card (center K) = 2) :
    ∃ a : centralizerTwoResidual u, orderOf a = 3 ∧
      projection e a = Sporadic.Mathieu.M12SmallPair.cubicActor := by
  have hm : Sporadic.Mathieu.M12SmallPair.cubicActor ∈
      Sporadic.Mathieu.M12SmallPair.coverResidual :=
    mem_map.mpr ⟨⟨_, Sporadic.Mathieu.M12SmallPair.cubicActor_mem⟩,
      Sporadic.Mathieu.M12SmallPair.cubicActor_residual, rfl⟩
  rw [← d.residual_image] at hm
  obtain ⟨y, hy, hq⟩ := mem_map.mp hm
  have h3 : Sporadic.Mathieu.M12SmallPair.cubicActor ^ 3 = 1 := by
    rw [← Sporadic.Mathieu.M12SmallPair.cubicActor_order]
    exact pow_orderOf_eq_one _
  have h6 : y ^ 6 = 1 := by
    have hc : y ^ 3 ∈ center K := by
      rw [← projection_eq_one e, map_pow, hq, h3]
    have hs := ambient_center_square hZ (y ^ 3) hc
    simpa only [← pow_mul] using hs
  have h4 : projection e (y ^ 4) = Sporadic.Mathieu.M12SmallPair.cubicActor := by
    rw [map_pow, hq, show 4 = 3 + 1 from rfl, pow_add, h3, one_mul, pow_one]
  refine ⟨⟨y ^ 4, (centralizerTwoResidual u).pow_mem hy 4⟩, ?_, h4⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    change (y ^ 4) ^ 3 = 1
    rw [← pow_mul, show 4 * 3 = 6 * 2 from rfl, pow_mul, h6, one_pow]
  · intro he
    have hv := congrArg (fun a : centralizerTwoResidual u => projection e a) he
    change projection e (y ^ 4) = projection e 1 at hv
    rw [h4, map_one] at hv
    have ho := Sporadic.Mathieu.M12SmallPair.cubicActor_order
    rw [hv, orderOf_one] at ho
    exact (by decide : (1 : ℕ) ≠ 3) ho

/-- The action on the lifted core is conjugation by the lifted cubic element. -/
theorem cubic_equivariance (a : centralizerTwoResidual u)
    (ha : projection e a = Sporadic.Mathieu.M12SmallPair.cubicActor)
    (r : centralizerCore u) :
    (d.coordinates m (residualAction u a r)).toAdd = cubic (d.coordinates m r).toAdd := by
  have he : d.coreMap (residualAction u a r) =
      Sporadic.Mathieu.M12SmallPair.residualCoreAction
        Sporadic.Mathieu.M12SmallPair.residualCubic (d.coreMap r) := by
    apply Subtype.ext
    change projection e ((a : K) * r * (a : K)⁻¹) = _
    rw [map_mul, map_mul, map_inv, ha]
    rfl
  change (m.coordinates (d.coreMap (residualAction u a r))).toAdd = _
  rw [he, m.cubic_equivariance]
  rfl

omit d in
private theorem binary_eq_of_zero_iff (a b : ZMod 2) (h : a = 0 ↔ b = 0) : a = b := by
  have he : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide +kernel
  exact he a b h

include m in
theorem square_preserved (a : centralizerTwoResidual u) (r : centralizerCore u) :
    (residualAction u a r) ^ 2 = r ^ 2 := by
  apply Subtype.ext
  change ((a : K) * r * (a : K)⁻¹) ^ 2 = (r : K) ^ 2
  have hc : (a : K) * (r : K) ^ 2 = (r : K) ^ 2 * (a : K) :=
    (d.residual_fixes_center a (r ^ 2) (d.square_central m r)).eq
  rw [conj_pow, hc, mul_inv_cancel_right]

theorem invariant_of_square_kernel (q : Space → ZMod 2)
    (hq : ∀ r : centralizerCore u,
      q (d.coordinates m r).toAdd = 0 ↔ r ^ 2 ∈ zpowers (d.root m ^ 2))
    (a : centralizerTwoResidual u)
    (ha : projection e a = Sporadic.Mathieu.M12SmallPair.cubicActor) :
    ∀ v, q (cubic v) = q v := by
  intro v
  obtain ⟨r, hr⟩ := d.coordinates_surjective m (Multiplicative.ofAdd v)
  have hv : (d.coordinates m r).toAdd = v := congrArg Multiplicative.toAdd hr
  rw [← hv, ← d.cubic_equivariance m a ha r]
  apply binary_eq_of_zero_iff
  rw [hq, hq, d.square_preserved m]

theorem fusion_of_square_kernel (hZ : Nat.card (center K) = 2)
    (hu : projection e u = Sporadic.Mathieu.M12SmallPair.z)
    (q : Space → ZMod 2)
    (hq : ∀ r : centralizerCore u,
      q (d.coordinates m r).toAdd = 0 ↔ r ^ 2 ∈ zpowers (d.root m ^ 2)) :
    q (rep 0) = q (rep 1) ∧ q (rep 2) = 0 := by
  have hk : (projection e).ker ≤ center K := by
    intro x hx
    exact (projection_eq_one e x).mp hx
  have hk2 : ∀ z ∈ (projection e).ker, z ^ 2 = 1 :=
    fun z hz => ambient_center_square hZ z (hk hz)
  have lift (j : Fin 5) : ∃ r : centralizerCore u,
      (d.coordinates m r).toAdd = rep j := by
    obtain ⟨r, hr⟩ := d.coordinates_surjective m (Multiplicative.ofAdd (rep j))
    exact ⟨r, congrArg Multiplicative.toAdd hr⟩
  obtain ⟨r₀, h₀⟩ := lift 0
  obtain ⟨r₁, h₁⟩ := lift 1
  obtain ⟨r₂, h₂⟩ := lift 2
  have hc₀ := m.noncentral_fusion 0 0 (d.coreMap r₀) (Or.inl rfl) h₀
  have hc₁ := m.noncentral_fusion 1 0 (d.coreMap r₁) (Or.inr rfl) h₁
  have ho₀ : orderOf (projection e r₀) = 2 := by
    exact (m.orbit_order 0 0 (d.coreMap r₀) h₀).trans (by decide)
  have hs₀ : (r₀ : K) ^ 2 ∈ center K := by
    rw [← projection_eq_one e, map_pow, ← ho₀]
    exact pow_orderOf_eq_one _
  have he₀₁ : r₀ ^ 2 = r₁ ^ 2 := by
    apply Subtype.ext
    exact (projection e).square_eq_of_isConj_map_of_central_binary_kernel
      (projection_surjective e) hk hk2 hs₀ (hc₀.symm.trans hc₁)
  have hu2 : u ^ 2 = 1 := by
    rw [← d.involution hu]
    exact pow_orderOf_eq_one _
  have he₂ : r₂ ^ 2 = 1 := by
    apply Subtype.ext
    have hc₂ : IsConj (projection e u) (projection e r₂) := by
      rw [hu]
      exact m.central_fusion 0 (d.coreMap r₂) h₂
    have he := (projection e).square_eq_of_isConj_map_of_central_binary_kernel
      (projection_surjective e) hk hk2 (hu2 ▸ (center K).one_mem) hc₂
    exact he.symm.trans hu2
  constructor
  · apply binary_eq_of_zero_iff
    rw [← h₀, ← h₁, hq, hq, he₀₁]
  · rw [← h₂, hq, he₂]
    exact one_mem _

/-- All marking fields follow from the unmarked core and its genuine square
form. The existence of those two inputs is retained by the source assembly. -/
theorem marked_of_square_form [Finite K] (hZ : Nat.card (center K) = 2)
    (hu : projection e u = Sporadic.Mathieu.M12SmallPair.z)
    (q : QuadraticForm (ZMod 2) Space)
    (hq : ∀ r : centralizerCore u,
      q (d.coordinates m r).toAdd = 0 ↔ r ^ 2 ∈ zpowers (d.root m ^ 2)) :
    orderOf u = 2 ∧ Nonempty (MarkedSquareCoordinates e u m) := by
  obtain ⟨a, ha, hai⟩ := d.exists_cubic_lift hZ
  obtain ⟨hf, hl⟩ := d.fusion_of_square_kernel m hZ hu q hq
  refine ⟨d.involution hu, ⟨{
    coordinates := d.coordinates m
    coordinates_surjective := d.coordinates_surjective m
    coordinates_ker := d.coordinates_ker m
    root := d.root m
    root_coordinates := d.root_coordinates m
    ambient_center_le := d.ambient_center_le
    center_eq := d.center_eq m
    fourth_power := d.fourth_power m
    square_central := d.square_central m
    quadratic := q
    invariant := d.invariant_of_square_kernel m q hq a hai
    square_kernel := hq
    square_over_u := d.square_over_u m hu
    noncentral_fusion := hf
    central_lift := hl
    quotient_mark := hu
    cubic_lift := a
    cubic_lift_order := ha
    cubic_lift_image := hai
    core_action := residualAction u a
    core_action_apply := residualAction_apply u a
    cubic_equivariance := d.cubic_equivariance m a hai
    core_image := d.core_image_mem
    coordinate_compatibility := fun _ => rfl
    centralizer_image := d.centralizer_image
    residual_image := d.residual_image
  }⟩⟩

end CoreLiftData
end CoverCoordinates
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
