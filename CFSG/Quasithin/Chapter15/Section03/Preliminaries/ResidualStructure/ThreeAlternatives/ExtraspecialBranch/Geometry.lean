module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.StarGeometry
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# The center and action kernels in the extraspecial branch of 15.3.7

The exact source equality C_Rc(V) = O₂(M) makes the star actor faithful on
Rc*. On Y*, the action kernel is central by 14.1.17(3); conversely, the
abelian action image kills the derived subgroup, which is the center in
the extraspecial branch. Transport through the intrinsic quotient
isomorphism proves O₂,Z(Y) = C_Y(V), with the literal central preimage.
It also shows that Rc* fixes this center pointwise.

The model hypothesis is the explicit extraspecial output of A.1.24. This
module does not assume cyclicity of Rc or order-three generation in M.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemmas
14.1.17(3) and 15.3.7, printed pp.980 and 1122 (PDF pp.997 and 1139).
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives.ExtraspecialBranch
variable {G : Type*} [Group G] [Finite G]
variable {M Mc V : Subgroup G} {T : Sylow 2 G} {d : NaturalOrthogonalAction M V}

/-- The literal residual has normal image in the star quotient. -/
public instance star_residual_normal (M Mc : Subgroup G) :
    (star M (residualY M Mc)).Normal :=
  (residualY_normal M Mc).map _ (QuotientGroup.mk'_surjective _)

/-- The star action kernel centralizes the entire star residual. -/
public theorem starActor_ker_le_centralizer (h : SourceInputs M Mc V T d) :
    (starActor d h.core_le_kernel).ker ≤
      centralizer (star M (residualY M Mc) : Set (StarGroup M)) := by
  rw [ker_starActor]
  exact h.star_centralizes.trans (centralizer_le
    (show star M (residualY M Mc) ≤ star M (residualY M Mc) ⊔ star M (Rc M Mc)
      from le_sup_left))

/-- The exact intersection-kernel equality makes the actor faithful on Rc*. -/
public theorem star_rc_actor_injective (h : SourceInputs M Mc V T d) :
    Function.Injective ((starActor d h.core_le_kernel).domRestrict (star M (Rc M Mc))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  rintro ⟨x, hx⟩ hk
  obtain ⟨r, hr, rfl⟩ := hx
  have hrk : r ∈ d.actor.ker := hk
  have hrq : r ∈ pCore 2 M := h.core_inter_kernel.le ⟨hr, hrk⟩
  exact mem_bot.mpr (Subtype.ext ((QuotientGroup.eq_one_iff r).mpr hrq))

/-- In the extraspecial branch, the residual action kernel is exactly its center. -/
public theorem star_residual_actor_ker (h : SourceInputs M Mc V T d)
    [IsExtraspecial 3 (star M (residualY M Mc))] :
    ((starActor d h.core_le_kernel).domRestrict (star M (residualY M Mc))).ker =
      center (star M (residualY M Mc)) := by
  let P := star M (residualY M Mc)
  let f := starActor d h.core_le_kernel
  obtain ⟨e⟩ := h.image_model
  have hAb : IsMulCommutative (P.map f) := by
    rw [map_starActor]
    exact ⟨⟨fun a b => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  have hder : ⁅P, P⁆ ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff, map_commutator]
    exact commutator_self_eq_bot_iff.mpr hAb
  apply le_antisymm
  · intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (starActor_ker_le_centralizer h hx)
      y y.property)
  · rw [← IsExtraspecial.commutator_eq_center (p := 3)]
    intro x hx
    apply hder
    rw [← P.map_subtype_commutator]
    exact mem_map_of_mem _ hx

/-- The given Heisenberg model identifies the intrinsic quotient Y/O₂(Y). -/
public theorem extraspecial_quotient_model
    (he : Nonempty (star M (residualY M Mc) ≃* HeisenbergPrime 3)) :
    Nonempty ((residualY M Mc ⧸ pCore 2 (residualY M Mc)) ≃* HeisenbergPrime 3) := by
  obtain ⟨e⟩ := he
  exact ⟨(residualCoreQuotientEquivStar M Mc).trans e⟩

/-- The literal preimage of Z(Y/O₂(Y)) is the centralizer of V in Y. -/
public theorem extraspecial_centralPreimage_eq (h : SourceInputs M Mc V T d)
    [IsExtraspecial 3 (star M (residualY M Mc))] :
    (centralPreimage (pCore 2 (residualY M Mc))).map (residualY M Mc).subtype =
      residualY M Mc ⊓ centralizer (V : Set G) := by
  let Y := residualY M Mc
  let e := residualCoreQuotientEquivStar M Mc
  have hecenter (q : Y ⧸ pCore 2 Y) : q ∈ center (Y ⧸ pCore 2 Y) ↔
      e q ∈ center (star M Y) := by
    constructor
    · intro hc
      apply mem_center_iff.mpr
      intro z
      obtain ⟨w, rfl⟩ := e.surjective z
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hc w)
    · intro hc
      apply mem_center_iff.mpr
      intro z
      apply e.injective
      simpa only [map_mul] using mem_center_iff.mp hc (e z)
  have hy (y : Y) : y ∈ centralPreimage (pCore 2 Y) ↔
      (y : G) ∈ centralizer (V : Set G) := by
    change QuotientGroup.mk' (pCore 2 Y) y ∈ center (Y ⧸ pCore 2 Y) ↔ _
    rw [hecenter, ← star_residual_actor_ker h]
    change starActor d h.core_le_kernel
      ((e (QuotientGroup.mk' (pCore 2 Y) y)) : StarGroup M) = 1 ↔ _
    rw [residualCoreQuotientEquivStar_apply_mk]
    change Subgroup.inclusion (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) y ∈
      d.actor.ker ↔ _
    rw [d.ker_actor]
    rfl
  ext x
  constructor
  · rintro ⟨y, hy', rfl⟩
    exact ⟨y.property, (hy y).mp hy'⟩
  · rintro ⟨hxY, hxc⟩
    exact ⟨⟨x, hxY⟩, (hy ⟨x, hxY⟩).mpr hxc, rfl⟩

/-- A three-group star residual belongs to the ambient three-core. -/
public theorem star_residual_le_threeCore
    (hp : IsPGroup 3 (star M (residualY M Mc))) :
    star M (residualY M Mc) ≤ pCore 3 (StarGroup M) :=
  le_sSup ⟨inferInstance, hp⟩

/-- The actual conjugation action of Rc* fixes Z(Y*) pointwise. -/
public theorem star_residual_center_fixed_by_rc (h : SourceInputs M Mc V T d)
    [IsExtraspecial 3 (star M (residualY M Mc))]
    (r : StarGroup M) (hr : r ∈ star M (Rc M Mc))
    (z : star M (residualY M Mc)) (hz : z ∈ center (star M (residualY M Mc))) :
    MulAut.conjNormal r z = z := by
  have hzker' : z ∈ ((starActor d h.core_le_kernel).domRestrict
      (star M (residualY M Mc))).ker := (star_residual_actor_ker h).symm ▸ hz
  have hzker : (z : StarGroup M) ∈ (starActor d h.core_le_kernel).ker := hzker'
  rw [ker_starActor] at hzker
  have hr' : r ∈ star M (residualY M Mc) ⊔ star M (Rc M Mc) :=
    (le_sup_right : star M (Rc M Mc) ≤ _) hr
  have hcomm := mem_centralizer_iff.mp (h.star_centralizes hzker) r hr'
  apply Subtype.ext
  change r * (z : StarGroup M) * r⁻¹ = z
  exact mul_inv_eq_iff_eq_mul.mpr hcomm

end CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives.ExtraspecialBranch
