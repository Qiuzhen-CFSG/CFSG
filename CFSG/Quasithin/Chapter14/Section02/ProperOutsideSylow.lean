module
public import CFSG.Quasithin.Chapter14.Section02.ProperChiZeroExclusion
public import Theory.GroupTheory.ConjugateSpanKernel.CubicSupplement
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# Sylow control when the cubic residual escapes the completion component

The actual source residual Y has quotient of order three by its two-core.
If Y is not contained in the canonical normal component L, the intersection
L ∩ YS is a normal two-subgroup of YS. Thus the Sylow intersection S ∩ L
lies in R=O₂(YS), and R is Sylow in LR. The final consumer applies the
proved χ₀ contradiction, retaining the earlier characteristic-two and
quasisimple-quotient conditions.

Source: Aschbacher--Smith 14.2.15, printed pp.985--986.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_residual_twoCore_quotient_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    : Nat.card (sourceResidual M Mc ⧸ pCore 2 (sourceResidual M Mc)) = 3 := by
  let Y := sourceResidual M Mc
  have hYM : Y ≤ M := sourceResidual_le _ _
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  let q := QuotientGroup.mk' C
  let f : Y →* M ⧸ C := q.comp (inclusion hYM)
  obtain ⟨_,_,_,_,⟨eY⟩,hcore,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hf : f.range = (Y.subgroupOf M).map q := by
    rw [MonoidHom.range_comp]
    congr 1
    ext m
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hm
      exact ⟨⟨m,hm⟩,Subtype.ext rfl⟩
  have hk : f.ker = pCore 2 Y := by
    apply map_injective Y.subtype_injective
    change f.ker.map Y.subtype = Y.pCoreIn 2
    rw [hcore]
    ext y
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,(QuotientGroup.eq_one_iff (N := C) (inclusion hYM a)).mp ha⟩
    · rintro ⟨hy,hc⟩
      refine ⟨⟨y,hy⟩,?_,rfl⟩
      exact (QuotientGroup.eq_one_iff (N := C) (inclusion hYM ⟨y,hy⟩)).mpr hc
  calc
    Nat.card (Y ⧸ pCore 2 Y) = (pCore 2 Y).index := rfl
    _ = Nat.card f.range := by rw [←hk,index_ker]
    _ = Nat.card ((Y.subgroupOf M).map q) := by rw [hf]
    _ = 3 := by rw [Nat.card_congr eY.toEquiv]; exact Nat.card_zmod 3


theorem source_proper_core_sylow_of_residual_not_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S)) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    let R := (sourceResidual M Mc ⊔ S).pCoreIn 2
    ¬ sourceResidual M Mc ≤ L → Chapter1.IsSylowIn 2 R (L ⊔ R) := by
  let Y := sourceResidual M Mc
  let X := K ⊔ Y ⊔ S
  let L := (solvableResidual X).map X.subtype
  let B := Y ⊔ S
  let R := B.pCoreIn 2
  change ¬ Y ≤ L → Chapter1.IsSylowIn 2 R (L ⊔ R)
  intro hYL
  obtain ⟨hL,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcore hs
  have hLX : L ≤ X := map_subtype_le _
  have hYX : Y ≤ X := le_sup_right.trans le_sup_left
  have hSX : S ≤ X := le_sup_right
  have hBX : B ≤ X := sup_le hYX hSX
  let C := L.subgroupOf X
  have hC : C = solvableResidual X := comap_map_eq_self_of_injective X.subtype_injective _
  let : C.Normal := hC.symm ▸ inferInstance
  let Y₀ := Y.subgroupOf X
  let S₀ := S.subgroupOf X
  let B₀ := B.subgroupOf X
  have hYp : IsPPerfect 2 Y₀ := (residualY_isPPerfect M Mc).of_surjective
    (subgroupOfEquivOfLe hYX).symm.toMonoidHom (subgroupOfEquivOfLe hYX).symm.surjective
  have hcY : Nat.card (Y₀ ⧸ pCore 2 Y₀) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hYX)
      (pCore_map_iso 2 _)).toEquiv]
    exact source_residual_twoCore_quotient_card hG T hempty hM hu hmany hcard e
  have hSY : S ≤ normalizer (Y : Set G) := (hST.trans hM.1.2).trans
    ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp (residualY_normal M Mc))
  have hS₀Y₀ : S₀ ≤ normalizer (Y₀ : Set X) := by
    rw [←subgroupOf_normalizer_eq hYX]
    exact comap_mono hSY
  have hY₀C : ¬ Y₀ ≤ C := by
    intro hh
    apply hYL
    intro y hy
    exact hh (show (⟨y,hYX hy⟩ : X) ∈ Y₀ from hy)
  have hp := twoGroup_kernel_on_cubic_residual_join Y₀ S₀ C hYp hcY
    ((T.isPGroup'.to_le hST).comap_subtype) hS₀Y₀ hY₀C
  have hB₀ : Y₀ ⊔ S₀ = B₀ := (subgroupOf_sup hYX hSX).symm
  rw [hB₀] at hp
  let f : (L ⊓ B : Subgroup G) →* C.subgroupOf B₀ :=
    { toFun := fun a => ⟨⟨⟨a,hBX a.property.2⟩,a.property.2⟩,a.property.1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hpLB : IsPGroup 2 (L ⊓ B : Subgroup G) := hp.of_injective f (by
    intro a b he
    exact Subtype.ext (congrArg (fun z : C.subgroupOf B₀ => (z.val.val.val : G)) he))
  have hXN : X ≤ normalizer (L : Set G) := by
    have hh := (solvableResidual X).le_normalizer_map X.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hLB : L ⊓ B ≤ R := le_pCoreIn_of_normalizes hpLB inf_le_right
    ((le_inf (hBX.trans hXN) B.le_normalizer).trans
      inf_normalizer_le_normalizer_inf)
  have hSLR : S ⊓ L ≤ R := (le_inf inf_le_right (inf_le_left.trans le_sup_right)).trans hLB
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs hLX hL.2.subnormal
  exact (isPGroup_pCoreIn 2 B).exists_sylow_sup_of_coprime_index L R
    (((pCoreIn_le 2 B).trans hBX).trans hXN) P P.not_dvd_index (hP ▸ hSLR)


/-- The literal contradiction in the `Y ⊄ L` branch, retaining the source quotient condition. -/
theorem source_proper_completion_false_of_residual_not_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S))
    (hXe : (K ⊔ sourceResidual M Mc ⊔ S) ∈ Chapter1.He G)
    (hq : IsQuasisimple (((solvableResidual (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G)).map
      (K ⊔ sourceResidual M Mc ⊔ S).subtype) ⧸
      pCore 2 ((solvableResidual (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G)).map
      (K ⊔ sourceResidual M Mc ⊔ S).subtype)))
    (hnot : ¬ sourceResidual M Mc ≤
      (solvableResidual (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G)).map
        (K ⊔ sourceResidual M Mc ⊔ S).subtype) : False := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  let R := (sourceResidual M Mc ⊔ S).pCoreIn 2
  have hsR : Chapter1.IsSylowIn 2 R (L ⊔ R) := by
    exact source_proper_core_sylow_of_residual_not_le hG T hempty hM hu hmany hcard e
      K S hST hK hSN hcore hs hnot
  exact source_proper_completion_sylow_core_false hG T hempty hM hu hmany hcard e H hH
    K S hST hi hgen hK hSN hcore hs hXe hq hsR

end CFSG.Quasithin.Chapter14.Section02
