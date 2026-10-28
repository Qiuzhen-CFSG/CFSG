module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Adapted
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.ElementaryAbelian.Injective


/-!
# The actual moving subgroup at an adapted nonsingular point

The H.9 commutator space maps to [W,O²(C_L(w))] under the original action
quotient. The corrected marking places the original T-fixed line in this
subgroup. Two-perfect commutator idempotence and the proved A.1.26 then
make the moving subgroup, and hence that line, centralize O(C_G(w)).

These are the movement and odd-core inputs to 12.1.1, without an ambient
Sylow assertion. The original orbit W remains distinct from its moving
subgroup. Source: Aschbacher--Smith, H.9.1 and 12.1.1, pp.389,788.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

omit [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))] in
/-- The literal embedded two-residual is two-perfect. -/
theorem pointResidual_isPPerfect (w : componentOrbit V (T : Subgroup G)) :
    IsPPerfect 2 (B.pointResidual w) := by
  exact (isPPerfect_embedded_pResidual 2 (L ⊓ B.pointCentralizer w)).of_surjective
    (MulEquiv.subgroupCongr (B.pointResidual_eq w).symm).toMonoidHom
    (MulEquiv.subgroupCongr (B.pointResidual_eq w).symm).surjective

omit [Finite G] [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))] in
/-- The residual normalizes the original orbit through N_G(L). -/
theorem pointResidual_normalizes_orbit (w : componentOrbit V (T : Subgroup G)) :
    B.pointResidual w ≤ normalizer (componentOrbit V (T : Subgroup G) : Set G) := by
  apply (B.pointResidual_le_normalizer w).trans
  rw [B.orbit_eq]
  exact le_normalizer_componentOrbit _ _

omit [Finite G] in
/-- The elementary orbit centralizes each of its points. -/
theorem orbit_le_pointCentralizer (w : componentOrbit V (T : Subgroup G)) :
    componentOrbit V (T : Subgroup G) ≤ B.pointCentralizer w := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : componentOrbit V (T : Subgroup G)) w))

/-- A.1.26 applied inside the actual ambient point centralizer. -/
theorem moving_centralizes_oddCore (w : componentOrbit V (T : Subgroup G))
    (hsqt : IsStronglyQuasithin (B.pointCentralizer w)) :
    ⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆ ≤
      centralizer ((pPrimeCore 2 (B.pointCentralizer w)).map (B.pointCentralizer w).subtype : Set G) := by
  let W := componentOrbit V (T : Subgroup G)
  let H := B.pointCentralizer w
  let X := B.pointResidual w
  let U := ⁅W,X⁆
  have hXH : X ≤ H := (B.pointResidual_le w).trans inf_le_right
  have hn := B.pointResidual_normalizes_orbit w
  have hUW : U ≤ W := le_normalizer_iff_commutator_le_left.mp hn
  have hUH : U ≤ H := hUW.trans (B.orbit_le_pointCentralizer w)
  have hXp : IsPPerfect 2 X := B.pointResidual_isPPerfect w
  have hXHp : IsPPerfect 2 (X.subgroupOf H) := hXp.of_surjective
    (subgroupOfEquivOfLe hXH).symm.toMonoidHom (subgroupOfEquivOfLe hXH).symm.surjective
  let i : U.subgroupOf H →* W :=
    (inclusion hUW).comp ((subgroupOfEquivOfLe hUH).toMonoidHom)
  let : IsElementaryAbelian 2 (U.subgroupOf H) :=
    IsElementaryAbelian.of_injective i ((inclusion_injective hUW).comp
      (subgroupOfEquivOfLe hUH).injective)
  have hcomm : ⁅U.subgroupOf H,X.subgroupOf H⁆ = U.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hXH]
    exact commutator_isPPerfect_idempotent X W hXp (IsElementaryAbelian.isPGroup 2 W) hn
  have hc := ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hsqt
    (X.subgroupOf H) (U.subgroupOf H) hXHp hcomm
  have hm := congrArg (map H.subtype) hc
  rw [map_commutator,map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hm
  exact commutator_eq_bot_iff_le_centralizer.mp hm

namespace SourceModel
variable {B} (S : B.SourceModel)
open Representation.BinaryOffender

/-- The residual action has exactly the H.9 residual as its image. -/
theorem pointResidual_action_range (w : componentOrbit V (T : Subgroup G)) :
    (B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w))).range =
      S.setup.residual (Additive.ofMul w) := by
  rw [← S.pointResidual_image w]
  ext a
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨l,hl,he⟩ := x.property
    refine ⟨l,hl,?_⟩
    change B.actionProjection (inclusion L.le_normalizer l) =
      B.actionProjection (inclusion (B.pointResidual_le_normalizer w) x)
    congr 1
    exact Subtype.ext he
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l,mem_map_of_mem _ hl⟩,rfl⟩

/-- The source moving space represents the literal ambient commutator. -/
theorem moving_eq_ambient_commutator (w : componentOrbit V (T : Subgroup G)) :
    (binarySubgroup (S.setup.moving (Additive.ofMul w))).map
      (componentOrbit V (T : Subgroup G)).subtype =
        ⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆ := by
  let W := componentOrbit V (T : Subgroup G)
  have hm := commutator_image_eq S.setup.representation W W (B.pointResidual w)
    (B.pointResidual_normalizes_orbit w) le_rfl
    (B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w)))
    (MonoidHom.id W) (fun x v => by rw [S.representation_eq]; rfl) ⊤ (by
      ext x
      simp [binarySubgroup])
  rw [Subgroup.map_id,S.pointResidual_action_range w,
    subspaceCommutator_top_eq_coinvariants] at hm
  change (⁅W,B.pointResidual w⁆).subgroupOf W =
    binarySubgroup (S.setup.moving (Additive.ofMul w)) at hm
  rw [← hm,map_subgroupOf_eq_of_le]
  exact le_normalizer_iff_commutator_le_left.mp (B.pointResidual_normalizes_orbit w)

/-- The corrected marking places the original fixed line in the moving subgroup. -/
theorem adapted_fixedLine_le_moving (w : componentOrbit V (T : Subgroup G))
    (hw : B.AdaptedPoint S w) :
    B.fixedLine ≤ ⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆ := by
  rw [← S.moving_eq_ambient_commutator w]
  intro z hz
  let zW : componentOrbit V (T : Subgroup G) := ⟨z,hz.1⟩
  have hzfix : Additive.ofMul zW ∈ B.fixedSpace (T : Subgroup G) :=
    (mem_subgroupSpace _ _ _).mpr hz.2
  rw [← hw.fixed_moving] at hzfix
  exact ⟨zW,hzfix.1,rfl⟩

/-- The original fixed line centralizes the full ambient point-centralizer odd core. -/
theorem adapted_fixedLine_centralizes_oddCore
    (w : componentOrbit V (T : Subgroup G)) (hw : B.AdaptedPoint S w)
    (hsqt : IsStronglyQuasithin (B.pointCentralizer w)) :
    B.fixedLine ≤ centralizer
      ((pPrimeCore 2 (B.pointCentralizer w)).map (B.pointCentralizer w).subtype : Set G) :=
  (S.adapted_fixedLine_le_moving w hw).trans (B.moving_centralizes_oddCore w hsqt)

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
