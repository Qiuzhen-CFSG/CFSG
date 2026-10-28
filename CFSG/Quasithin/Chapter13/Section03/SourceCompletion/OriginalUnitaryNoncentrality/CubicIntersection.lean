module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.Applicability
public import Theory.Representation.G2BinaryNondegeneratePlane.Basic
public import Theory.GroupTheory.OddElementLift
public import Theory.Representation.G2BinaryCubicIntersection

/-!
# The original unitary cubic intersection geometry

An odd lift in the original plane residual has exactly the native cubic
action. Its joined seed three-spaces contain an explicit nonorthogonal
pair. The earlier plane-centralizer theorem therefore bounds the actual
join centralizer. That earlier source statement remains explicit.

Source: Aschbacher--Smith 13.3.14(b), printed p.891.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original plane residual contains an odd actor with exactly the marked
cubic action, and its joined three-spaces have controlled centralizer. -/
theorem unitary_odd_cubic_join_centralizer
    (L B U M : Subgroup G)
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hp : pointCoordinateSubspace E B = plane)
    (hs : pointCoordinateSubspace E U = seed)
    (hBV : B ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (hd : commutator (Atlas.G2.Model F) ≤ (inducedAutomizer V L).map rho)
    (hplanes : UnitaryPlaneCentralizers V M) :
    ∃ g : G, g ∈ (pResidual 2 (L ⊓ normalizer (B : Set G) : Subgroup G)).map
      (L ⊓ normalizer (B : Set G)).subtype ∧
      Odd (orderOf g) ∧ g ∈ normalizer (B : Set G) ∧
      centralizer ((U ⊔ U.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤ M := by
  let X := (pResidual 2 (L ⊓ normalizer (B : Set G) : Subgroup G)).map
      (L ⊓ normalizer (B : Set G)).subtype
  have hXB : X ≤ normalizer (B : Set G) := (map_subtype_le _).trans inf_le_right
  have hXL : X ≤ L := (map_subtype_le _).trans inf_le_left
  obtain ⟨i,⟨n,hnX,rfl⟩,hnative⟩ := source_plane_residual_cubic L B rho E he hp hBV hLN hd
  let f : normalizer (V : Set G) →* Atlas.G2.Model F :=
    rho.comp V.normalizerMonoidHom.rangeRestrict
  have hn : f n = Atlas.G2.BinaryParabolicPair.cubicActor := hnative
  obtain ⟨r,hr,hodd,hrf⟩ := f.exists_odd_power_with_image n (by rw [hn,Atlas.G2.BinaryParabolicPair.cubicActor_order]; decide)
  have hrX : r.val ∈ X := (zpowers_le.mpr (show n ∈ X.subgroupOf (normalizer (V : Set G)) from hnX)) hr
  refine ⟨r.val,hrX,?_,hXB hrX,?_⟩
  · simpa only [Subgroup.orderOf_coe] using hodd
  · let J := U ⊔ U.map (MulAut.conj r.val).toMonoidHom
    by_contra hout
    have hiso := UnitaryGeometry.escaping_isotropic_of_plane_centralizers
      (UnitaryGeometry.markedForm E) (UnitaryGeometry.markedForm_alternating E)
      (UnitaryGeometry.plane_centralizers_of_four_subgroups E
        (hplanes rho E he (hd.trans (map_le_range _ _)))) J hout
    let v : Additive V := E.symm (Pi.single 2 1)
    have hv : v.toMul.val ∈ U := by
      apply (mem_pointCoordinateSubspace E U v).mp
      rw [hs]
      simp [v]
    have hw : (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict r) v).toMul.val ∈
        U.map (MulAut.conj r.val).toMonoidHom := ⟨v.toMul.val,hv,rfl⟩
    have hz := hiso v (show v ∈ UnitaryGeometry.ambientSpace J from (show U ≤ J from le_sup_left) hv)
      (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict r) v)
      (show _ ∈ UnitaryGeometry.ambientSpace J from (show U.map (MulAut.conj r.val).toMonoidHom ≤ J from le_sup_right) hw)
    change Atlas.G2.Natural.BinaryNondegeneratePlane.form (E v)
      (E (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict r) v)) = 0 at hz
    rw [he,show rho (V.normalizerMonoidHom.rangeRestrict r) = Atlas.G2.BinaryParabolicPair.cubicActor from hrf.trans hn] at hz
    have hpai : Atlas.G2.Natural.BinaryNondegeneratePlane.form (E v)
        (Atlas.G2.Restricted.NaturalCoordinates.action F Atlas.G2.BinaryParabolicPair.cubicActor (E v)) = 1 := by
      simpa only [v,LinearEquiv.apply_symm_apply,
        Atlas.G2.Natural.BinaryNondegeneratePlane.form_apply,pairing_apply] using
          pairing_plane_cubic_seed
    exact one_ne_zero (hpai.symm.trans hz)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
