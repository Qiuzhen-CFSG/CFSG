module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.Setup
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PCoreRestriction

/-!
# The local residual maps onto the extraspecial center

The inclusion of O²(C_Y(V)) in Y followed by the quotient projection covers
Z(Y/O₂(Y)): residuals commute with surjections and this center has order three.
The projection has a two-group kernel, and its odd-order target kills the
intrinsic two-core. The first isomorphism theorem therefore gives the actual
multiplicative equivalence, with its formula on every representative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7 and
the calculation after 15.3.49(b), printed pp.1122 and 1143.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal
variable {G : Type*} [Group G]

private theorem residual_subgroup_eq [Finite G] (X : Subgroup G) :
    twoResidualSubgroup X = pResidual 2 X := by
  unfold twoResidualSubgroup pResidual
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card hn⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, IsPGroup.iff_card.mp hp⟩

private def centerProjection (Y X : Subgroup G) (hX : X ≤ twoCenter Y) :
    X →* center (Y ⧸ pCore 2 Y) :=
  ((QuotientGroup.mk' (pCore 2 Y)).comp
    (inclusion (hX.trans (map_subtype_le _)))).codRestrict _ (by
      intro x
      obtain ⟨y, hy, he⟩ := hX x.property
      change QuotientGroup.mk' (pCore 2 Y)
        ⟨x, hX.trans (map_subtype_le _) x.property⟩ ∈ center (Y ⧸ pCore 2 Y)
      have heq : (⟨x, hX.trans (map_subtype_le _) x.property⟩ : Y) = y :=
        Subtype.ext he.symm
      rw [heq]
      exact hy)

private theorem centerProjection_ker (Y X : Subgroup G) (hX : X ≤ twoCenter Y) :
    (centerProjection Y X hX).ker =
      (pCore 2 Y).comap (inclusion (hX.trans (map_subtype_le _))) := by
  ext x
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

private theorem centerProjection_core (Y X : Subgroup G)
    [IsExtraspecial 3 (Y ⧸ pCore 2 Y)] (hX : X ≤ twoCenter Y) :
    (centerProjection Y X hX).ker = pCore 2 X := by
  let f := centerProjection Y X hX
  have hk : IsPGroup 2 f.ker := by
    rw [centerProjection_ker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  change f.ker = pCore 2 X
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, hk⟩
  rw [← Subgroup.map_eq_bot_iff]
  have hp : IsPGroup 3 (center (Y ⧸ pCore 2 Y)) :=
    IsPGroup.of_card ((IsExtraspecial.center_order_p 3 _).trans (pow_one 3).symm)
  have hd := (pCore_isPGroup (p := 2) (G := X)).map f |>.disjoint_of_coprime
    (hp.to_subgroup ⊤) (by decide : Nat.Coprime 2 3)
  exact disjoint_top.mp hd

/-- Projection of the local residual into the center of the actual quotient. -/
noncomputable def residualCenterProjection (Y V : Subgroup G)
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y) :
    twoResidualAmbient (Y ⊓ centralizer (V : Set G)) →*
      center (Y ⧸ pCore 2 Y) :=
  centerProjection Y _ ((map_subtype_le _).trans hc.le)

/-- The projection retains inclusion into Y on every representative. -/
theorem residualCenterProjection_coe (Y V : Subgroup G)
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y)
    (y : twoResidualAmbient (Y ⊓ centralizer (V : Set G))) :
    (residualCenterProjection Y V hc y : Y ⧸ pCore 2 Y) =
      QuotientGroup.mk' (pCore 2 Y)
        ⟨y, (map_subtype_le _).trans inf_le_left y.property⟩ := by rfl

/-- Taking the two-residual still covers the odd-order center. -/
theorem residualCenterProjection_surjective [Finite G] (Y V : Subgroup G)
    [IsExtraspecial 3 (Y ⧸ pCore 2 Y)]
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y) :
    Function.Surjective (residualCenterProjection Y V hc) := by
  let X := Y ⊓ centralizer (V : Set G)
  let f := centerProjection Y X hc.le
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (pCore 2 Y) z.val
    have hx : (y : G) ∈ X := hc.ge ⟨y, (show QuotientGroup.mk' (pCore 2 Y) y ∈ center (Y ⧸ pCore 2 Y) by rw [hy]; exact z.property), rfl⟩
    exact ⟨⟨y, hx⟩, Subtype.ext hy⟩
  have ht : pResidual 2 (center (Y ⧸ pCore 2 Y)) = ⊤ := by
    apply top_unique
    intro z _
    apply mem_pResidual_of_orderOf_coprime
    have hd := orderOf_dvd_natCard z
    rw [IsExtraspecial.center_order_p 3 _] at hd
    exact Nat.Coprime.of_dvd_right hd (by decide : Nat.Coprime 2 3)
  have hm : (pResidual 2 X).map f = ⊤ :=
    (map_pResidual_of_surjective 2 f hf).trans ht
  intro z
  obtain ⟨x, hx, he⟩ := hm.ge (mem_top z)
  refine ⟨⟨x, ⟨x, (residual_subgroup_eq X).symm ▸ hx, rfl⟩⟩, ?_⟩
  exact he

/-- The kernel is the intrinsic two-core of the residual. -/
theorem residualCenterProjection_ker (Y V : Subgroup G)
    [IsExtraspecial 3 (Y ⧸ pCore 2 Y)]
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y) :
    (residualCenterProjection Y V hc).ker =
      pCore 2 (twoResidualAmbient (Y ⊓ centralizer (V : Set G))) :=
  centerProjection_core Y _ _

/-- The actual quotient-center equivalence, induced by inclusion and projection. -/
noncomputable def residualCenterEquiv [Finite G] (Y V : Subgroup G)
    [IsExtraspecial 3 (Y ⧸ pCore 2 Y)]
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y) :
    let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    (Y₀ ⧸ pCore 2 Y₀) ≃* center (Y ⧸ pCore 2 Y) :=
  (QuotientGroup.quotientMulEquivOfEq (residualCenterProjection_ker Y V hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (residualCenterProjection_surjective Y V hc))

/-- Formula for the equivalence on each element of the residual. -/
theorem residualCenterEquiv_apply_mk [Finite G] (Y V : Subgroup G)
    [IsExtraspecial 3 (Y ⧸ pCore 2 Y)]
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y)
    (y : twoResidualAmbient (Y ⊓ centralizer (V : Set G))) :
    (residualCenterEquiv Y V hc (QuotientGroup.mk' _ y) : Y ⧸ pCore 2 Y) =
      QuotientGroup.mk' (pCore 2 Y)
        ⟨y, (map_subtype_le _).trans inf_le_left y.property⟩ := by rfl
end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
