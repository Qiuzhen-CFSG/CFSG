module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ParabolicSixExclusion
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.GeometricFlags
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.SpecificGroups.BinaryLinear.FourTwoLocalFive

/-!
# Binary-linear C.2.7 exclusion for a normal six-point residual

A factor of five excludes all proper binary four-space flags. In dimension
five it forces the actual flag to be an endpoint. Its two-core quotient is
A₈, while the normal perfect residual has quotient A₆ and no factor seven.
The residual's nontrivial image is normal in the simple A₈ Levi quotient,
which is impossible. All maps retain the literal star intersection and its
solvable kernel; no ambient normality is imposed.

The final theorem also excludes the SL₅(2) star model directly. The original
Sylow intersection maps onto a Sylow of K*, so the proved Sylow-overgroup
classification constructs the flag used by the exclusion. This step needs
no C.2.7 alternative as a premise.

Source: Aschbacher–Smith C.2.7(3)(h), printed pp.145–147, applied in
3.3.22, p.597. The fixed-coset application is in
SourceAlternatingSeven/LocalAnalysisSylowResidualsComponentsBinaryLinear.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open BinaryLinear.OuterCyclic

private theorem binary_flag_map {n k : ℕ} (hn : 0 < n)
    (f : LinearFlag (ZMod 2) n k) :
    (f.stabilizer.map (QuotientGroup.mk' (center SL(n,ZMod 2)))).map
      (projectiveEquivLinear hn).toMonoidHom =
        ⨅ i, BinaryLinear.parabolic (f.space i) := by
  rw [map_map]
  have he : (projectiveEquivLinear hn).toMonoidHom.comp
      (QuotientGroup.mk' (center SL(n,ZMod 2))) = (slEquivLinear n).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact projectiveEquivLinear_mk hn x
  rw [he]
  ext x
  rw [mem_map_equiv]
  simp only [LinearFlag.stabilizer, mem_iInf]
  apply forall_congr'
  intro i
  rw [linearStabilizer, mem_comap, Submodule.stabilizer_coe, MulAction.mem_stabilizer_set]
  change (∀ v, (slEquivLinear n) ((slEquivLinear n).symm x) v ∈ f.space i ↔
    v ∈ f.space i) ↔ _
  rw [MulEquiv.apply_symm_apply]
  rfl

private theorem no_four_parabolic_of_five {A : Type*} [Group A]
    (P : Subgroup A) (hfive : 5 ∣ Nat.card P)
    (hp : IsBinaryPositiveRankParabolic P 4) : False := by
  obtain ⟨e,k,hk,_,f,hf⟩ := hp
  let a := e.trans (projectiveEquivLinear (by decide : 0 < 4))
  have he : P.map a.toMonoidHom = ⨅ i, BinaryLinear.parabolic (f.space i) := by
    rw [show a.toMonoidHom = (projectiveEquivLinear (by decide : 0 < 4)).toMonoidHom.comp
      e.toMonoidHom from rfl, ← map_map, hf, binary_flag_map]
  have hd : 5 ∣ Nat.card (P.map a.toMonoidHom) := by
    rwa [card_map_of_injective a.injective]
  rw [he] at hd
  let i : Fin k := ⟨0,hk⟩
  exact BinaryLinear.FourTwoLocalFive.five_not_dvd_parabolic _ (f.nonzero i) (f.proper i)
    (hd.trans (card_dvd_of_le (iInf_le _ i)))

private theorem five_parabolic_quotient {A : Type*} [Group A]
    (P : Subgroup A) (hfive : 5 ∣ Nat.card P)
    (hp : IsBinaryPositiveRankParabolic P 5) :
    Nonempty ((P ⧸ pCore 2 P) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e,k,hk,_,f,hf⟩ := hp
  let a := e.trans (projectiveEquivLinear (by decide : 0 < 5))
  have he : P.map a.toMonoidHom = ⨅ i, BinaryLinear.parabolic (f.space i) := by
    rw [show a.toMonoidHom = (projectiveEquivLinear (by decide : 0 < 5)).toMonoidHom.comp
      e.toMonoidHom from rfl, ← map_map, hf, binary_flag_map]
  have hd : 5 ∣ Nat.card (⨅ i, BinaryLinear.parabolic (f.space i) : Subgroup (LinearGroup 5)) := by
    rw [←he,card_map_of_injective a.injective]
    exact hfive
  obtain ⟨b,i,hi,hiP⟩ := BinaryLinear.FiveFlagGeometry.GeometricFlags.exists_endpoint_coordinates
    hk f.space f.increasing.monotone f.nonzero f.proper hd
  let t := (a.subgroupMap P).trans (MulEquiv.subgroupCongr (he.trans hiP))
  let q := QuotientGroup.congr _ _ t (pCore_map_iso 2 t)
  let z := Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm
  rcases hi with rfl | rfl
  · exact ⟨q.trans ((BinaryLinear.FiveFlagGeometry.MaximalOvergroups.lineQuotientEquiv b).trans z)⟩
  · exact ⟨q.trans ((BinaryLinear.FiveFlagGeometry.MaximalOvergroups.hyperplaneQuotientEquiv b).trans z)⟩

private theorem no_normal_six_image {B D : Type*} [Group B] [Finite B] [Group D] [Finite D]
    [Group.IsPerfect B] (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (f : B →* D) [f.range.Normal] [Group.IsSolvable f.ker]
    (e8 : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 8)) : False := by
  let q := e8.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := e8.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 D := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e8.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := hqk.symm ▸ inferInstanceAs (Group.IsSolvable (pCore 2 D))
  let g := q.comp f
  let : Group.IsSolvable g.ker := isSolvable_comap_of_solvable_ker f q.ker
  let : g.range.Normal := by
    dsimp only [g]
    rw [MonoidHom.range_comp]
    exact Subgroup.Normal.map inferInstance q hq
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e6.isSimpleGroup
  have hc : Nat.card (B ⧸ pCore 2 B) = 360 := by
    rw [Nat.card_congr e6.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have h7 : ¬ 7 ∣ Nat.card B := by
    obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [←(pCore 2 B).card_mul_index,hr,index_eq_card,hc]
    intro hd
    have hh := ((by decide : Nat.Coprime 7 2).pow_right r).dvd_of_dvd_mul_left hd
    norm_num at hh
  have h5 : 5 ∣ Nat.card g.range := by
    have hB : 5 ∣ Nat.card B := by
      have hd := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 B))
        (QuotientGroup.mk'_surjective _)
      rw [hc] at hd
      exact (by decide : 5 ∣ 360).trans hd
    have hker := pCore_isPGroup.to_le (PerfectCoreTwoExtension.solvable_ker_le_core g)
    obtain ⟨r,hr⟩ := hker.exists_card_eq
    rw [←g.ker.card_mul_index,hr,index_ker] at hB
    exact ((by decide : Nat.Coprime 5 2).pow_right r).dvd_of_dvd_mul_left hB
  rcases (inferInstance : g.range.Normal).eq_bot_or_eq_top with hg | hg
  · rw [hg,card_bot] at h5
    norm_num at h5
  · have hd := card_dvd_of_surjective g (MonoidHom.range_eq_top.mp hg)
    have h7A : 7 ∣ Nat.card (alternatingGroup (Fin 8)) := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact h7 (h7A.trans hd)

variable {G : Type*} [Group G] [Finite G] {H K R M B : Subgroup G}

private theorem no_six_starM_eight_quotient
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) (hn : M ⊓ K ≤ normalizer (B : Set G)) [Group.IsPerfect B]
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (a : (starM K R M ⧸ pCore 2 (starM K R M)) ≃* alternatingGroup (Fin 8)) : False := by
  let q := QuotientGroup.mk' (starKernel K R)
  let D := M ⊓ K
  let d : D →* starM K R M :=
    (q.comp (inclusion (inf_le_right.trans le_sup_left))).codRestrict _
      (fun x => mem_map_of_mem q x.property)
  have hd : Function.Surjective d := by
    intro y
    obtain ⟨x,hx,he⟩ := y.property
    exact ⟨⟨x.val,hx⟩,Subtype.ext he⟩
  let f : B →* starM K R M := d.comp (inclusion hB)
  have hr : f.range = (B.subgroupOf D).map d := by
    dsimp only [f]
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact b.property
    · intro hx
      exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
  let : (B.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer hn
  let : f.range.Normal := hr.symm ▸ Subgroup.Normal.map inferInstance d hd
  let j : f.ker →* (toStarImage K R).ker :=
    { toFun := fun b => ⟨inclusion (hB.trans inf_le_right) b.val, by
        apply Subtype.ext
        exact congrArg (fun a : starM K R M => (a : StarQuotient K R))
          (show f b.val = 1 from b.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) hh))
  let : Group.IsSolvable (toStarImage K R).ker := toStarImage_ker_solvable_from_source h
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  exact no_normal_six_image e6 f a

/-- Normality of the six-point residual excludes both binary-linear parabolic rows. -/
theorem no_binaryLinear_parabolic_of_normal_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) (hn : M ⊓ K ≤ normalizer (B : Set G)) [Group.IsPerfect B]
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    {n : ℕ} (hnn : n = 4 ∨ n = 5)
    (hp : IsBinaryPositiveRankParabolic ((starM K R M).subgroupOf (starImage K R K)) n) :
    False := by
  let t := (subgroupOfEquivOfLe (starM_le K R M)).symm
  have hfive : 5 ∣ Nat.card ((starM K R M).subgroupOf (starImage K R K)) := by
    rw [←Nat.card_congr t.toEquiv]
    exact starM_five_dvd_of_six h hB e6
  rcases hnn with rfl | rfl
  · exact no_four_parabolic_of_five _ hfive hp
  obtain ⟨e8⟩ := five_parabolic_quotient _ hfive hp
  exact no_six_starM_eight_quotient h hB hn e6
    ((QuotientGroup.congr _ _ t (pCore_map_iso 2 t)).trans e8)

/-- The original Sylow intersection excludes the SL₅(2) star model directly,
without assuming the C.2.7 alternatives or a flag placement. -/
theorem no_linearFive_star_of_normal_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) (hn : M ⊓ K ≤ normalizer (B : Set G)) [Group.IsPerfect B]
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    (e5 : starImage K R K ≃* SL(5,ZMod 2)) : False := by
  let e := e5.trans (slEquivLinear 5)
  let D := (starM K R M).subgroupOf (starImage K R K)
  let P := D.map e.toMonoidHom
  obtain ⟨U,hU⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K hTK
  let Q := (U.mapSurjective (toStarImage_surjective K R)).mapSurjective
    (f := e.toMonoidHom) e.surjective
  have hQP : (Q : Subgroup (LinearGroup 5)) ≤ P := by
    rintro x ⟨y,⟨k,hk,rfl⟩,rfl⟩
    apply mem_map_of_mem e.toMonoidHom
    have hkT : (k : G) ∈ (T : Subgroup G) := by
      change k ∈ (U : Subgroup K) at hk
      rw [hU] at hk
      exact hk
    exact mem_map_of_mem (QuotientGroup.mk' (starKernel K R))
      (show (k : G) ∈ M ⊓ K from ⟨hTM hkT,k.property⟩)
  obtain ⟨b,cuts,hP⟩ := BinaryLinear.FiveFlagGeometry.isFlagParabolic_of_sylow_le Q P hQP
  have hproper : P ≠ ⊤ := by
    intro ht
    have hD : D = ⊤ := map_injective e.injective
      (ht.trans (map_top_of_surjective _ e.surjective).symm)
    exact (star_thompson_intersection_from_source h).2.not_ge (subgroupOf_eq_top.mp hD)
  have h5 : 5 ∣ Nat.card (BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts) := by
    rw [←hP,card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe (starM_le K R M)).toEquiv]
    exact starM_five_dvd_of_six h hB e6
  have hp' : BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts ≠ ⊤ :=
    hP ▸ hproper
  rcases BinaryLinear.FiveFlagGeometry.cuts_eq_singleton_end_of_five_dvd b cuts hp' h5
    with hc | hc
  all_goals
    rw [hc] at hP
    let t := ((subgroupOfEquivOfLe (starM_le K R M)).symm.trans
      (e.subgroupMap D)).trans (MulEquiv.subgroupCongr hP)
    let q := QuotientGroup.congr _ _ t (pCore_map_iso 2 t)
    apply no_six_starM_eight_quotient h hB hn e6
  · exact q.trans ((BinaryLinear.FiveFlagGeometry.MaximalOvergroups.lineQuotientEquiv b).trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)
  · exact q.trans ((BinaryLinear.FiveFlagGeometry.MaximalOvergroups.hyperplaneQuotientEquiv b).trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)

end CFSG.Quasithin.ChapterC.C27Source
