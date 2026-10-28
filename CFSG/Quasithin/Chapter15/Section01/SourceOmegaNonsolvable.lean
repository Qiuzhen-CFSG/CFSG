module
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaSolvableExclusion
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SmallSource

/-!
# Full Omega containment in every original local two-core

The actual Sylow action on the local four-space embeds in its Omega action,
so its faithful quotient has order at most four and cubic ratio greater than
one. The intersection residual centralizes that same module. The original
E.2.17 small-action theorem therefore makes any escaping H-star subgroup
solvable, and the proved solvable Omega exclusion finishes the contradiction.
The genuine earlier universal Theorems A and C remain explicit.

Source: Aschbacher--Smith 15.1.11(1), printed p.1089, applying E.2.17,
printed pp.229--230.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Failure of full-Omega core containment forces the original local group to be solvable. -/
theorem source_fullOmega_solvable_of_not_le_core
    (hA : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hout : ¬localModule T M ≤ H.pCoreIn 2) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) → Group.IsSolvable H := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  let d := source_15_1_1_qrcConfiguration hG T hM hH
  let := d.module_elementary
  let V := localModule T M
  let N := M
  let S : Sylow 2 H := T.subtype hH.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := (d.module_le_core.trans (left_core_le_sylow d)).trans hH.1.1.2
  let hE : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let := hE
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) := by
    rw [←subgroupOf_normalizer_eq hVH]
    exact fun _ hs => (le_normalizer_conjugateSpanBy _ _ : M ≤ normalizer (V : Set G)) (hM.1.2 hs)
  let := ChapterE.DihedralCubic.centralizer_normal (S : Subgroup H) W hTV
  let ρ := ChapterE.DihedralCubic.canonicalAction (S : Subgroup H) W hTV
  let σ := imageRepresentation N V (le_normalizer_conjugateSpanBy _ _)
  let q := ChapterE.DihedralCubic.projection (S : Subgroup H) W hTV
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  let i : (S : Subgroup H) →* N :=
    (H.subtype.comp (S : Subgroup H).subtype).codRestrict N (fun s => hM.1.2 s.property)
  let f := (actionHom N V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict.comp i
  have hk : q.ker ≤ f.ker := by
    intro s hs
    have hsC : s ∈ (centralizer (W : Set H)).subgroupOf (S : Subgroup H) :=
      (QuotientGroup.eq_one_iff s).mp hs
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    have hc := congrArg H.subtype (hsC ⟨v,hVH v.property⟩ v.property)
    change (v : G) * (s.val : G) = (s.val : G) * (v : G) at hc
    change (s.val : G) * (v : G) * (s.val : G)⁻¹ = v
    rw [←hc,mul_inv_cancel_right]
  let ψ := q.liftOfSurjective hqs ⟨f,hk⟩
  have hψ (s : (S : Subgroup H)) : ψ (q s) = f s := q.liftOfRightInverse_comp_apply _ _ _ s
  let e := subgroupOfEquivOfLe hVH
  let E : Additive W ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  have he : ∀ a v, E (ρ a v) = σ (ψ a) (E v) := by
    intro a v
    obtain ⟨s,rfl⟩ := hqs a
    rw [hψ]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg H.subtype
      (ChapterE.DihedralCubic.representation_apply (S : Subgroup H) W hTV q hqs
        (QuotientGroup.ker_mk' _) s v)
  have hψi : Function.Injective ψ := by
    intro a b hab
    apply ChapterE.DihedralCubic.representation_injective (S : Subgroup H) W hTV q hqs
      (QuotientGroup.ker_mk' _)
    apply LinearMap.ext
    intro v
    apply E.injective
    change E (ρ a v) = E (ρ b v)
    rw [he,he,hab]
  have hRatio : 1 < cubicRatio ρ := by
    have hm := cubicRatio_le_of_injective_equivariant ρ σ ψ hψi E he
    have hoq : cubicRatio σ = 3 / 2 := ho.2.1
    have hnum : (1 : ℝ≥0∞) < 3 / 2 := by
      rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
      norm_num
    rw [← hoq] at hnum
    exact hnum.trans_le hm
  have hDcard : Nat.card (ChapterE.DihedralCubic.ActionQuotient (S : Subgroup H) W hTV) ≤ 4 := by
    have hwhole : Nat.card (internalActionImage N V (le_normalizer_conjugateSpanBy _ _)) = 36 := by
      obtain ⟨eqv⟩ := ho.2.2.2.1
      rw [Nat.card_congr eqv.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin]
      norm_num
    have hp := S.isPGroup'.of_surjective q hqs
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hd : 2^n ∣ 36 := by
      rw [←hn,←hwhole]
      exact card_dvd_of_injective ψ hψi
    have hnle : n ≤ 2 := by
      by_contra! hh
      have h8 : 2^3 ∣ 2^n := pow_dvd_pow 2 (by omega)
      exact (by decide : ¬8 ∣ 36) (h8.trans hd)
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) hnle
  obtain ⟨_,hP,hmax,hSQ,hfit⟩ := source_centralizing_minimalParabolic hG T hM hJ H hH
  have hB : ChapterB.minimalParabolicMax S hP = (H ⊓ M).subgroupOf H :=
    (ChapterB.minimalParabolicMax_unique S hP hmax (fun x hx => ⟨x.property,hM.1.2 hx⟩)).symm
  have hVT : V ≤ (T : Subgroup G) :=
    d.module_le_core.trans (left_core_le_sylow d)
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => hVT hx
  have hBN : ChapterB.minimalParabolicMax S hP ≤ normalizer (W : Set H) := by
    rw [hB,←subgroupOf_normalizer_eq hVH]
    exact fun _ hx => (le_normalizer_conjugateSpanBy _ _ : M ≤ normalizer (V : Set G)) hx.2
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hP).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W)
      (hWS.trans (ChapterB.minimalParabolicMax_spec S hP).2) hBN
  have hWout : ¬W ≤ ChapterB.minimalParabolicCore S hP := by
    intro hw
    have hc : W ≤ pCore 2 H := by
      rw [←ChapterB.minimalParabolic_sylow_inf_core S hP]
      exact le_inf hWS hw
    apply hout
    have hm := map_mono (f := H.subtype) hc
    change (V.subgroupOf H).map H.subtype ≤ H.pCoreIn 2 at hm
    simpa only [map_subgroupOf_eq_of_le hVH] using hm
  have hWcard : Nat.card W = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv]
    obtain ⟨x,e,hx⟩ := ho.2.2.2.2
    calc
      Nat.card V = Nat.card (Additive V) := rfl
      _ = Nat.card OrthogonalFourBinary.Space := Nat.card_congr x.toEquiv
      _ = 16 := by
        simp [OrthogonalFourBinary.Space, OrthogonalFourBinary.Plane, OrthogonalFourBinary.F]
  have hodd : Odd (Nat.card (pResidual 2 (internalActionImage M V
      (le_normalizer_conjugateSpanBy _ _)))) := by
    obtain ⟨x,e,hx⟩ := ho.2.2.2.2
    exact OrthogonalFourBinary.TerminalLines.odd_twoResidual_of_injective
      (OrthogonalFourBinary.omega.subtype.comp e.toMonoidHom)
      (OrthogonalFourBinary.omega.subtype_injective.comp e.injective)
  have hres := source_15_1_9_4_of_odd_residual hG T hM hH hJ
    (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _) hodd
  have hresH : (pResidual 2 (ChapterB.minimalParabolicMax S hP)).map
      (ChapterB.minimalParabolicMax S hP).subtype ≤ centralizer (W : Set H) := by
    apply map_subtype_le_map_subtype.mp
    rw [map_embedded_pResidual,hB,map_subgroupOf_eq_of_le inf_le_left,
      map_centralizer_subtype,map_subgroupOf_eq_of_le hVH]
    exact le_inf ((map_subtype_le _).trans inf_le_left) hres
  exact ChapterE.Witnesses.source_small_solvable hA hC hSQ S hP W
    hWS ((normal_subgroupOf_iff_le_normalizer hWS).mpr hTV) hWcore hWout hfit hWcard
    (S : Subgroup H) le_rfl hTV q hqs (QuotientGroup.ker_mk' _) hDcard hRatio hresH

/-- The nonsolvable branch of the original full-Omega core-containment assertion. -/
theorem source_fullOmega_nonsolvable_module_le_core
    (hA : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) (hs : ¬Group.IsSolvable H) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) → localModule T M ≤ H.pCoreIn 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  by_contra hout
  exact hs (source_fullOmega_solvable_of_not_le_core hA hC hG T hM hJ hH hout ho)

/-- Both source branches give the original full-Omega containment in O₂(H). -/
theorem source_fullOmega_module_le_core
    (hA : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) → localModule T M ≤ H.pCoreIn 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  by_contra hout
  have hs := source_fullOmega_solvable_of_not_le_core hA hC hG T hM hJ hH hout ho
  exact source_fullOmega_solvable_false hG T hempty hM hJ hH hs hout ho

end CFSG.Quasithin.Chapter15.Section01
