module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.Seed
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ModelAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ShadowBounds
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.OvergroupData
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.Coverage
public import Theory.Mathieu.M24.Properties.Order
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.GroupTheory.FourGroupNormalizerOvergroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.Quasithin.EvenCharacteristic

/-!
# Reducing the M₂₄ rank-two exclusion to intrinsic local geometry

The normal elementary catalogue gives the full normalizer of each maximal
Sylow-containing two-local. Containment of that normalizer in an octad,
trio, or sextet candidate is enough: these candidates have characteristic
two, so the maximality clause of 15.3.41 forces equality after transport.
No classification of the smaller normalizers is needed.

The actual component image of Y₊ is solvable and normal in the local
subgroup. Its Sylow join has the complete S₃ × S₃ Frattini shadow, forcing
nine to divide the seed order. Intrinsic normal-seed bounds for the three
geometric families therefore exclude M₂₄. Automorphism innerness supplies
the full component-quotient equivalence without an extension premise.

The two model calculations remain explicit in the conditional assembly.
Source: Aschbacher--Smith, 15.3.41--42, printed p.1138, and 1.1.5(3f),
printed p.502; GLS3, Table 5.3e.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.M24Reduction

private noncomputable def markedSylow : Sylow 2 M24 :=
  Sylow.ofCard SylowNormalizer.candidate (by
    rw [SylowNormalizer.candidate_card, m24_order]
    decide +kernel)

private theorem fixed_catalogue (J : Subgroup M24) (hJ : IsMaximalTwoLocal J)
    (hTJ : SylowNormalizer.candidate ≤ J) :
    ∃ i : Fin 22, J = EvenCatalogue.localGroup i := by
  let T := markedSylow
  obtain ⟨R, hR, hn, he, hJR⟩ :=
    exists_normal_elementary_normalizer_of_sylow_le T hJ hTJ
  let : IsElementaryAbelian 2 R := he
  have hs : ∀ x ∈ R, x * x = 1 := by
    intro x hx
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  obtain ⟨i, hi⟩ := EvenCatalogue.Coverage.catalogue_of_normal_exponent_two R hR hn hs
  exact ⟨i, by rw [hJR, hi]; rfl⟩

/-- Geometric containment suffices: the source maximality forces the
specified local subgroup to equal the pulled-back geometric overgroup. -/
theorem local_equiv_of_overgroups
    (ho : EvenCatalogue.NormalizerOvergroups)
    {H : Type*} [Group H] [Finite H] (e : H ≃* M24)
    (K N Y S : Subgroup H) (d : LocalConfiguration K N Y S) :
    (∃ O : Octad, Nonempty (N ≃* octadStabilizer O)) ∨
      ∃ k : Fin 2, Nonempty (N ≃* EvenCandidates.localGroup k) := by
  obtain ⟨P, hP⟩ := d.sylow
  obtain ⟨J, hNJ, hJ⟩ := Finite.exists_le_maximal d.twoLocal
  let T := markedSylow
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 Q T
  let f : H ≃* M24 := e.trans (MulAut.conj g)
  have hJ' := Theory.Quasithin.isMaximalTwoLocal_map f hJ
  have hTJ : SylowNormalizer.candidate ≤ J.map f.toMonoidHom := by
    have h := (Theory.Quasithin.maximalTwoLocal_overgroup_conj_iff g Q
      (J.map e.toMonoidHom)).mpr
      ⟨Theory.Quasithin.isMaximalTwoLocal_map e hJ,
        map_mono ((hP.symm ▸ d.sylow_le).trans hNJ)⟩
    rw [hg] at h
    simpa [T, markedSylow, f, map_map] using h.2
  obtain ⟨i, hi⟩ := fixed_catalogue _ hJ' hTJ
  have hNi : N.map f.toMonoidHom ≤ EvenCatalogue.localGroup i :=
    hi ▸ map_mono hNJ
  have lift (D : Subgroup M24) (hle : N.map f.toMonoidHom ≤ D)
      (hc : centralizer (pCore 2 D : Set D) ≤ pCore 2 D) : Nonempty (N ≃* D) := by
    let E := D.map f.symm.toMonoidHom
    have hNE : N ≤ E := by
      simpa [E, map_map] using
        map_mono (f := f.symm.toMonoidHom) hle
    have hE := characteristicTwo_of_mulEquiv (f.symm.subgroupMap D).symm
      (generalizedFitting_eq_pCore_of_selfCentralizing 2 hc)
    have hEN := d.maximal E hNE hE
    exact ⟨((f.symm.subgroupMap D).trans (MulEquiv.subgroupCongr hEN)).symm⟩
  rcases ho i with ⟨O, hO⟩ | ⟨k, hk⟩
  · exact Or.inl ⟨O, lift _ (hNi.trans hO) (LinearFourCore.octad_core_selfCentralizing O)⟩
  · exact Or.inr ⟨k, lift _ (hNi.trans hk) (EvenCandidates.localGroup_core_selfCentralizing k)⟩

private theorem nine_dvd_seed_of_shadow
    {H : Type*} [Group H] [Finite H] (P : Sylow 2 H) (D : Subgroup H) [D.Normal]
    (hshadow : RankTwoShadow D (P : Subgroup H)) : 9 ∣ Nat.card D := by
  let U := D ⊔ (P : Subgroup H)
  have ht : D.subgroupOf U ⊔ (P : Subgroup H).subgroupOf U = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self _
  have hp : IsPGroup 2 (U ⧸ D.subgroupOf U) :=
    isPGroup_quotient_of_sup_eq_top _ _ P.isPGroup'.comap_subtype ht
  have h9U : 9 ∣ Nat.card U := by
    have h := (shadow_local_order_bounds P U D (P : Subgroup H) rfl
      le_sup_right le_sup_left hshadow).1
    exact (by decide : 9 ∣ 36).trans h
  rw [(D.subgroupOf U).card_eq_card_quotient_mul_card_subgroup] at h9U
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hc : Nat.Coprime 9 (Nat.card (U ⧸ D.subgroupOf U)) := by
    rw [hn]
    exact Nat.Coprime.pow_right _ (by decide)
  have h9 := hc.dvd_of_dvd_mul_left h9U
  rwa [Nat.card_congr (subgroupOfEquivOfLe (show D ≤ U from le_sup_left)).toEquiv] at h9

/-- The original seed maps to a solvable normal subgroup of the actual
local component image, and the full Frattini shadow preserves a factor of nine. -/
theorem component_normal_seed
    {G : Type*} [Group G] [Finite G] {I L M Y S : Subgroup G}
    [(L.subgroupOf I).Normal] (d : ComponentSetup I L M Y S) :
    ∃ D : Subgroup (componentImage I L M),
      D.Normal ∧ Group.IsSolvable D ∧ 9 ∣ Nat.card D := by
  let N := componentImage I L M
  let X := componentImage I L Y
  let T := componentImage I L S
  have hXN : X ≤ N := d.quotient_local.yplus_le.trans inf_le_left
  have hTN : T ≤ N := d.quotient_local.sylow_le
  have hnormal : (X.subgroupOf N).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hXN).mpr
    rw [componentImage_normalizer I L M Y d.component_le d.yplus_le d.theta_eq d.normalizer_eq]
  let : (X.subgroupOf N).Normal := hnormal
  have hp : IsPGroup 3 (Y ⧸ pCore 2 Y) :=
    isPGroup_iff_pow_pow_eq_one.mpr (fun x => ⟨1, by simpa using d.yplus_exponent x⟩)
  let := hp.isNilpotent
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable Y := (Group.isSolvable_iff_subgroup_quotient (pCore 2 Y)).mpr
    ⟨inferInstance, inferInstance⟩
  let : Group.IsSolvable (Y.subgroupOf I) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (d.yplus_le.trans d.component_le)).toMonoidHom)
    (subgroupOfEquivOfLe (d.yplus_le.trans d.component_le)).injective
  let q := centralizerQuotientMap (L.subgroupOf I)
  let : Group.IsSolvable X := Group.isSolvable_of_surjective
    (f := q.subgroupMap (Y.subgroupOf I)) (q.subgroupMap_surjective _)
  let : Group.IsSolvable (X.subgroupOf N) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hXN).toMonoidHom) (subgroupOfEquivOfLe hXN).injective
  refine ⟨X.subgroupOf N, hnormal, inferInstance, ?_⟩
  obtain ⟨P, hP⟩ := d.quotient_local.sylow
  have hP' : (P : Subgroup (ComponentQuotient I L)) = T := hP
  let Q := P.subtype (hP'.symm ▸ hTN)
  have hQ : (Q : Subgroup N) = T.subgroupOf N := by
    change (P : Subgroup (ComponentQuotient I L)).subgroupOf N = _
    rw [hP]
  apply nine_dvd_seed_of_shadow Q
  rw [hQ]
  exact rankTwoShadow_subgroupOf hXN hTN d.quotient_local.shadow

private theorem no_seed_of_equiv {H A : Type*} [Group H] [Group A]
    (e : H ≃* A) (hb : ∀ D : Subgroup A, D.Normal → Group.IsSolvable D → ¬ 9 ∣ Nat.card D)
    (D : Subgroup H) (hn : D.Normal) (hs : Group.IsSolvable D) (h9 : 9 ∣ Nat.card D) : False := by
  let : D.Normal := hn
  let : Group.IsSolvable D := hs
  let X := D.map e.toMonoidHom
  have hXn : X.Normal := Subgroup.Normal.map hn e.toMonoidHom e.surjective
  have hXs : Group.IsSolvable X := Group.isSolvable_of_surjective
    (f := (e.subgroupMap D).toMonoidHom) (e.subgroupMap D).surjective
  apply hb X hXn hXs
  rwa [card_map_of_injective e.injective]

/-- Conditional source assembly. Both explicit intrinsic model calculations
remain to be discharged before claiming the M₂₄ exclusion. -/
theorem not_m24_of_overgroups_and_seed_bounds
    (ho : EvenCatalogue.NormalizerOvergroups) (hb : EvenCatalogue.NormalSeedBounds)
    {G : Type*} [Group G] [Finite G] {I L M Y S : Subgroup G}
    [(L.subgroupOf I).Normal] (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* M24) : False := by
  let f := wholeModelOfInner d e M24OuterRestriction.conj_surjective
  obtain ⟨D, hn, hs, h9⟩ := component_normal_seed d
  rcases local_equiv_of_overgroups ho f _ _ _ _ d.quotient_local with
    ⟨O, ⟨a⟩⟩ | ⟨k, ⟨a⟩⟩
  · exact no_seed_of_equiv a (hb.1 O) D hn hs h9
  · exact no_seed_of_equiv a (hb.2 k) D hn hs h9

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.M24Reduction
