module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Setup
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Seeds
public import Theory.SpecificGroups.BinaryLinear.FivePointExtension
public import Theory.SpecificGroups.BinaryLinear.PointStabilizerRank
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.RankOnePerfectResidual

/-!
# The original two-perfect minimal-parabolic seed in degree five

The point marking of M₁ extends X/O₂(X) to a binary-linear quotient of XS.
Its two-group kernel preserves Sylow covers. The actual intersections
NI ∩ XS and MI ∩ XS therefore contain an escaping rank-one parabolic P.
The subgroup Y₁ = O²(P), embedded by the original subtype map, is
S-invariant, lies in NI, escapes MI, and has Y₁S/O₂(Y₁S) ≅ S₃.

This constructs the corrected seed required by 15.2.21(3), without using
SmallActionCaseII or its erroneous two-core field. The earlier residual
escape is supplied by the faithful NI action in the adjoining source
consumer; the corrected small-action exclusion remains with
qt-e-152-char2-small-actions.

Source: Aschbacher--Smith, 15.2.23(a), printed p.1117.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Extend the original point-parabolic marking to XS. Its restriction is
the original X/O₂(X) map and its kernel is a two-group. -/
theorem point_image_extension
    (hI : PlaneEscapes Mc ZS I) (hn : I ≤ normalizer (X : Set G))
    (e : (X ⧸ pCore 2 X) ≃* SL(5,ZMod 2))
    (v : Fin 5 → ZMod 2) (hv : v ≠ 0)
    (hm : (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      e.toMonoidHom = MulAction.stabilizer SL(5,ZMod 2) v) :
    ∃ f : (X ⊔ smallActionS T ZS : Subgroup G) →* LinearGroup 5,
      Function.Surjective f ∧ IsPGroup 2 f.ker ∧
      ∀ x : X, f (inclusion le_sup_left x) =
        slEquivLinear 5 (e (QuotientGroup.mk' (pCore 2 X) x)) := by
  let S := smallActionS T ZS
  have hSI : S ≤ I := (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hSX : S ≤ normalizer (X : Set G) := hSI.trans hn
  have hSM : S ≤ normalizer (M1 X ZS : Set G) :=
    (le_inf hSX ((show S ≤ centralizer (ZS : Set G) from inf_le_right).trans
      (centralizer (ZS : Set G)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hm' : ((M1 X ZS).subgroupOf X).map
      ((e.trans (slEquivLinear 5)).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) =
      BinaryLinear.parabolic (Submodule.span (ZMod 2) {v}) := by
    change ((M1 X ZS).subgroupOf X).map
      ((slEquivLinear 5).toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)))) = _
    rw [←map_map,←map_map,hm,←BinaryLinear.PointStabilizerRank.stabilizer_eq_parabolic]
    ext g
    rw [mem_map_equiv]
    change (slEquivLinear 5 ((slEquivLinear 5).symm g)) v = v ↔ g v = v
    rw [(slEquivLinear 5).apply_symm_apply]
  exact BinaryLinear.exists_point_extension X S (M1 X ZS) hSX
    (T.isPGroup'.to_le inf_le_left) inf_le_left hSM
    (e.trans (slEquivLinear 5)) v hv hm'

/-- The literal minimal-parabolic seed in NI=M∩I, outside MI=Mc∩I.
Only the earlier 15.2.18(3)(ii) residual escape remains explicit. The
parabolic is a cover of S inside XS; its two-residual is mapped into G. -/
theorem minimalParabolic_seed_of_point_image
    (hI : PlaneEscapes Mc ZS I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G))
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hescape : ¬ (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype ≤ Mc ⊓ I)
    (e : (X ⧸ pCore 2 X) ≃* SL(5,ZMod 2))
    (v : Fin 5 → ZMod 2) (hv : v ≠ 0)
    (hm : (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      e.toMonoidHom = MulAction.stabilizer SL(5,ZMod 2) v) :
    ∃ P : Subgroup G, smallActionS T ZS ⋖ P ∧ P ≤ M ⊓ I ∧
      P ≤ X ⊔ smallActionS T ZS ∧
      SmallActionsSource.Seed M I (smallActionS T ZS) ((pResidual 2 P).map P.subtype) ∧
      ¬ (pResidual 2 P).map P.subtype ≤ Mc ⊓ I := by
  let S := smallActionS T ZS
  let J := X ⊔ S
  have hSI : S ≤ I := (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hSM : S ≤ M := (show S ≤ (T : Subgroup G) from inf_le_left).trans hsource.maximal.1.2
  have hSMc : S ≤ Mc := (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_left
  have hJI : J ≤ I := sup_le hXI hSI
  obtain ⟨S0,hS0⟩ := (show Chapter1.IsSylowIn 2 S I from d.sylow_in_escape hI).restrict (show S ≤ J from le_sup_right) hJI
  have hS0' : (S0 : Subgroup J) = S.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hS0,map_subgroupOf_eq_of_le (show S ≤ J from le_sup_right)]
  let C := (M ⊓ I).subgroupOf J
  let D := (Mc ⊓ I).subgroupOf J
  have hSC : (S0 : Subgroup J) ≤ C := by
    rw [hS0']
    exact comap_mono (le_inf hSM hSI)
  have hSD : (S0 : Subgroup J) ≤ D := by
    rw [hS0']
    exact comap_mono (le_inf hSMc hSI)
  have hCD : ¬ C ≤ D := by
    intro h
    apply hescape
    intro x hx
    have hxX : x ∈ X := by
      rw [hX]
      exact embedded_primeToResidual_mono 3 inf_le_right hx
    have hxC : (⟨x,mem_sup_left hxX⟩ : J) ∈ C := by
      change x ∈ M ⊓ I
      exact map_subtype_le _ hx
    exact h hxC
  obtain ⟨f,hf,hk,_⟩ := point_image_extension d hI hn e v hv hm
  obtain ⟨P,hcov,hPC,hY,hYC,hSY,hYS,hYD,hquot⟩ :=
    BinaryLinear.FiveFlagGeometry.exists_rankOne_residual_escaping_of_two_kernel
      f hf hk S0 C D hSC hSD hCD
  let Y := (pResidual 2 P).map P.subtype
  let P0 := P.map J.subtype
  have hP0C : P0 ≤ M ⊓ I := by
    rintro _ ⟨x,hx,rfl⟩
    exact hPC hx
  have hres : Y.map J.subtype = (pResidual 2 P0).map P0.subtype :=
    map_embedded_pResidual 2 P J.subtype
  have hresS : (pResidual 2 P0).map P0.subtype ⊔ S = P0 := by
    have he := congrArg (Subgroup.map J.subtype) hYS
    rwa [Subgroup.map_sup,hres,hS0] at he
  have hcov0 : S ⋖ P0 := by
    have hh := (covBy_map_subtype_iff J _ _).mpr hcov
    rwa [hS0] at hh
  have hnorm : S ≤ normalizer ((pResidual 2 P0).map P0.subtype : Set G) :=
    hcov0.le.trans (P0.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P0 (pResidual 2 P0)))
  have hq : Nonempty ((P0 ⧸ pCore 2 P0) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨ep⟩ := hquot
    rw [hYS] at ep
    let ei := P.equivMapOfInjective J.subtype J.subtype_injective
    exact ⟨(QuotientGroup.congr _ _ ei (pCore_map_iso 2 ei)).symm.trans ep⟩
  refine ⟨P0,hcov0,hP0C,map_subtype_le _,⟨(map_subtype_le _).trans hP0C,
    isPPerfect_embedded_pResidual 2 P0,hnorm,?_⟩,?_⟩
  · rwa [hresS]
  · intro h
    apply hYD
    intro y hy
    exact h (hres ▸ mem_map_of_mem J.subtype hy)

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
