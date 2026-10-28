module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.OriginalSource.Parabolic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.QuotientGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicRecognition
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ResidualCentralizer
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.NormalFourObstruction
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility

/-!
# The original binary derived G₂ branch of 15.3.43

The original normal four-group makes the two-core of M ∩ L nontrivial.
The model's normalizer cover aligns this intersection with a root parabolic;
its Sylow invariance and source minimality promote containment to equality.
The first parabolic has no normal elementary four-group. In the second,
every Sylow-preserving automorphism fixing the three-residual is trivial,
contradicting the original nontrivial V₁ action on L.

The marking retains both the actual component intersection and its Sylow.
The final consumer uses the original 15.3.43(a)--(e) producer. No containment
of the original involution centralizer in M is required.

Source: Aschbacher--Smith, 15.3.43, printed pp.1139--1140; the two G₂(2)′
parabolics and root conventions are those of 14.2.21, printed p.988.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource
open Atlas.G2.BinaryParabolicPair Atlas.G2.SylowParabolicRecognition
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

private theorem component_sylow_preserved (s : G) (hs : s ∈ S) :
    (S.subgroupOf L).map
      (L.normalizerMonoidHom ⟨s, c.normalizes (((sylow_le_local c).trans inf_le_right) hs)⟩).toMonoidHom =
        S.subgroupOf L := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact S.mul_mem (S.mul_mem hs hx) (S.inv_mem hs)
  · let a : MulAut L := L.normalizerMonoidHom
      ⟨s, c.normalizes (((sylow_le_local c).trans inf_le_right) hs)⟩
    change Nat.card (S.subgroupOf L) ≤ Nat.card ((S.subgroupOf L).map a.toMonoidHom)
    rw [card_map_of_injective (f := a.toMonoidHom) a.injective]

/-- The original intersection is one of the two marked binary G₂ parabolics. -/
theorem g2_parabolic_marking (hs : IsSimpleGroup L) (e : L ≃* DerivedModel) :
    ∃ (f : L ≃* DerivedModel) (i : Fin 2),
      (S.subgroupOf L).map f.toMonoidHom = (derivedSylow : Subgroup DerivedModel) ∧
      (M.subgroupOf L).map f.toMonoidHom = rootParabolic i := by
  obtain ⟨Q, hQ⟩ := component_sylow c
  have hQS : (Q : Subgroup L) = S.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hQ, subgroupOf_map_subtype]
  obtain ⟨f, i, hQf, hMP⟩ := exists_aligned_parabolic_of_twoCore e Q (M.subgroupOf L)
    (by rw [hQS]; exact fun x hx => c.sylow_le_M hx)
    (intersection_twoCore_ne_bot c)
  have hSf : (S.subgroupOf L).map f.toMonoidHom =
      (derivedSylow : Subgroup DerivedModel) := by
    rw [← hQS, hQf, derivedSylow_eq]
  have hDcore : pCore 2 DerivedModel = ⊥ := by
    rw [← pCore_map_iso 2 f, ← center_eq_twoCore c,
      BinaryInspection.LinearInspection.component_center_eq_bot c hs, Subgroup.map_bot]
  let P := (rootParabolic (F := ZMod 2) i).map f.symm.toMonoidHom
  let K := P.map L.subtype
  have hKL : K ≤ L := map_subtype_le _
  have hKne : K ≠ L := by
    intro he
    have hP : P = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨y, hy, hxy⟩ := he.ge x.property
      exact (Subtype.ext hxy : y = x) ▸ hy
    exact rootParabolic_ne_top hDcore i
      (f.symm.mapSubgroup.injective (hP.trans f.symm.mapSubgroup.map_top.symm))
  have hMK : M ⊓ L ≤ K := by
    intro x hx
    exact ⟨f.symm (f ⟨x, hx.2⟩), ⟨f ⟨x, hx.2⟩,
      hMP ⟨⟨x, hx.2⟩, hx.1, rfl⟩, rfl⟩,
      congrArg Subtype.val (f.symm_apply_apply ⟨x, hx.2⟩)⟩
  have hSK : S ≤ normalizer (K : Set G) := by
    intro s hsS
    let a := L.normalizerMonoidHom ⟨s, c.normalizes (((sylow_le_local c).trans inf_le_right) hsS)⟩
    let β : MulAut DerivedModel := (f.symm.trans a).trans f
    have htransport (H : Subgroup L) :
        (H.map f.toMonoidHom).map β.toMonoidHom =
          (H.map a.toMonoidHom).map f.toMonoidHom := by
      rw [map_map, map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f (a (f.symm (f x))) = f (a x)
      rw [f.symm_apply_apply]
    have hB : (Atlas.G2.unipotent.subgroupOf DerivedModel).map β.toMonoidHom =
        Atlas.G2.unipotent.subgroupOf DerivedModel := by
      rw [← derivedSylow_eq, ← hSf, htransport, component_sylow_preserved c s hsS]
    have hPi := rootParabolic_invariant β hB i
    have hPa : P.map a.toMonoidHom = P := by
      apply (map_injective (f := f.toMonoidHom) f.injective)
      have hPf : P.map f.toMonoidHom = rootParabolic i := by
        exact (map_symm_eq_iff_map_eq _).mp rfl
      rw [← htransport, hPf, hPi]
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (P.map L.subtype).map (MulAut.conj s).toMonoidHom = P.map L.subtype
    rw [map_map]
    have he : (MulAut.conj s).toMonoidHom.comp L.subtype = L.subtype.comp a.toMonoidHom := by
      ext x
      rfl
    rw [he, ← map_map, hPa]
  have hKM := invariant_component_overgroup_eq c K (lt_of_le_of_ne hKL hKne) hMK hSK
  have hinter : M.subgroupOf L = P := by
    have he := congrArg (fun H : Subgroup G => H.subgroupOf L) hKM
    change (P.map L.subtype).comap L.subtype = (M ⊓ L).subgroupOf L at he
    rw [comap_map_eq_self_of_injective L.subtype_injective, inf_subgroupOf_right] at he
    exact he.symm
  refine ⟨f, i, hSf, ?_⟩
  rw [hinter]
  exact (map_symm_eq_iff_map_eq _).mp rfl

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource
open Atlas.G2.BinaryParabolicPair Atlas.G2.SylowParabolicRecognition
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

private theorem actor_residual_model {D : Type*} [Group D] (f : L ≃* D) :
    (Yplus.subgroupOf L).map f.toMonoidHom =
      threeResidualIn ((M.subgroupOf L).map f.toMonoidHom) := by
  have he : Yplus.subgroupOf L = threeResidualIn (M.subgroupOf L) := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le c.y_le_component, threeResidualIn_map,
      subgroupOf_map_subtype]
    exact ParabolicInspection.residual_on_component c
  rw [he, threeResidualIn_map]

omit [Finite G] in
private theorem g2_not_first (f : L ≃* DerivedModel)
    (hM : (M.subgroupOf L).map f.toMonoidHom = derivedFirst) : False := by
  have hVL := plane_le_component c
  let W := (V₂.subgroupOf L).map f.toMonoidHom
  let : IsElementaryAbelian 2 V₂ := c.plane_two_elementary
  let : IsElementaryAbelian 2 (V₂.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map f.toMonoidHom
  have hW : W ≤ derivedFirst := by
    rw [← hM]
    exact map_mono (fun x hx => c.sylow_le_M (c.plane_two_le hx))
  have hn : derivedFirst ≤ normalizer (W : Set DerivedModel) := by
    rw [← hM]
    apply (map_mono ?_).trans ((V₂.subgroupOf L).le_normalizer_map f.toMonoidHom)
    rw [← subgroupOf_normalizer_eq hVL]
    exact fun x hx => c.plane_two_normalized ⟨hx, c.component_le x.property⟩
  have hc : Nat.card W = 4 := by
    rw [card_map_of_injective f.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv).trans c.plane_two_card
  exact no_normal_four_first W hW hn hc

private theorem g2_not_second (f : L ≃* DerivedModel)
    (hS : (S.subgroupOf L).map f.toMonoidHom = (derivedSylow : Subgroup DerivedModel))
    (hM : (M.subgroupOf L).map f.toMonoidHom = derivedSecond) : False := by
  have hY : (Yplus.subgroupOf L).map f.toMonoidHom = secondResidual := by
    rw [actor_residual_model c f, hM, threeResidualIn_eq_primeToResidual]
    rfl
  apply c.plane_one_acts
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro s hs
  have hsS := c.plane_one_le hs
  let a := L.normalizerMonoidHom ⟨s, c.normalizes (((sylow_le_local c).trans inf_le_right) hsS)⟩
  let β : MulAut DerivedModel := (f.symm.trans a).trans f
  have hB : (derivedSylow : Subgroup DerivedModel).map β.toMonoidHom = derivedSylow := by
    rw [← hS, map_map]
    have he : β.toMonoidHom.comp f.toMonoidHom = f.toMonoidHom.comp a.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change f (a (f.symm (f x))) = f (a x)
      rw [f.symm_apply_apply]
    rw [he, ← map_map, component_sylow_preserved c s hsS]
  have hβ : β = 1 := automorphism_eq_one_of_secondResidual β hB (by
    intro x hx
    rw [← hY] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hsy := (commutator_eq_bot_iff_le_centralizer.mp c.plane_one_centralizes) hs y hy
    change f (a (f.symm (f y))) = f y
    rw [f.symm_apply_apply]
    congr 1
    apply Subtype.ext
    change s * (y : G) * s⁻¹ = y
    rw [← hsy, mul_inv_cancel_right])
  intro y hy
  have hh := DFunLike.congr_fun hβ (f ⟨y, hy⟩)
  change f (a (f.symm (f ⟨y, hy⟩))) = f ⟨y, hy⟩ at hh
  rw [f.symm_apply_apply] at hh
  have hh := congrArg Subtype.val (f.injective hh)
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Exclude the original binary derived G₂ branch using its actual local parabolic. -/
theorem not_g2_derived (hs : IsSimpleGroup L)
    (iso : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  obtain ⟨e⟩ := iso
  obtain ⟨f, i, hS, hM⟩ := g2_parabolic_marking c hs e
  fin_cases i
  · have hF : rootParabolic (F := ZMod 2) 0 = derivedFirst := by
      simp only [rootParabolic, ↓reduceIte, Atlas.G2.LieParabolicSetup.parabolic₁_binary]
      rfl
    exact g2_not_first c f (hM.trans hF)
  · have hF : rootParabolic (F := ZMod 2) 1 = derivedSecond := by
      simp only [rootParabolic, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
      rfl
    exact g2_not_second c f hS (hM.trans hF)
end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The original 15.3.43 consumer excludes G₂(2)′ with its original local data. -/
theorem source_not_symmetricThreeShadow_of_g2_derived
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : ReductionSourceInputs d I L)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S))
    (hs : IsSimpleGroup L)
    (iso : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    ¬ SymmetricThreeShadow d.Yplus d.S := by
  intro hshadow
  exact not_g2_derived (reducedConfiguration_of_source d hI h hshadow halt) hs iso

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource
