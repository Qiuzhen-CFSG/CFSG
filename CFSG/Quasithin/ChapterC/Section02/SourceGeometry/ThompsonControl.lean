module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleThompsonNormalizer
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.Relative
public import Theory.GroupTheory.CharacteristicNormalizerRestriction

/-!
# The original marked Thompson-normalizer restriction

For a relatively normal component in C.2.7, retain the literal star quotient
and the original subgroup M. The kernel and offender source theorem supplies
the action kernel, and radical saturation puts O₂(KR) inside R. Restrict
characteristic-normalizer control to KR and lift through the two-core and
remaining odd central kernel. The component normalizer of J(R)* lies in the
proper marked intersection M_K*. This is the source's displayed (*), without
a parabolic marking or a classification premise.

Source: Aschbacher–Smith C.2.7, printed p.146; the original 14.7.68 application
has the required normality inside its fixed centralizer.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

private theorem source_join_core_le (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    (K ⊔ R).pCoreIn 2 ≤ R := by
  let KH := K.subgroupOf H
  let RH := R.subgroupOf H
  have hKm : KH.map H.subtype = K := map_subgroupOf_eq_of_le h.component.1
  have hRm : RH.map H.subtype = R := map_subgroupOf_eq_of_le h.setup.radical_le
  have hJm : (KH ⊔ RH).map H.subtype = K ⊔ R := by rw [Subgroup.map_sup,hKm,hRm]
  have hQm : ((KH ⊔ RH).pCoreIn 2).map H.subtype = (K ⊔ R).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,hJm]
  rw [←hQm,←hRm]
  exact map_mono (joinCore_le_radical KH RH h.setup.radical)

theorem star_thompson_intersection_of_normal_input (h : Input κ H R M K)
    [(K.subgroupOf H).Normal] :
    starImage K R K ⊓ normalizer
        (starImage K R (elementaryAbelianMaxJ R) : Set (StarQuotient K R)) ≤ starM K R M ∧
      starM K R M < starImage K R K := by
  let J := K ⊔ R
  let K₀ := K.subgroupOf J
  let R₀ := R.subgroupOf J
  let M₀ := M.subgroupOf J
  let i : J →* H := inclusion h.join_le
  let q := QuotientGroup.mk' (starKernel K R)
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let e : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : IsQuasisimple (K₀ ⧸ pCore 2 K₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hK : K₀.IsCComponent := h.component.2.subgroupOf_of_le le_sup_left h.join_le
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hne : R₀ ≠ ⊥ := by
    intro hh
    have hRbot : R = ⊥ := by
      have hm := congrArg (map J.subtype) hh
      rwa [map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right),Subgroup.map_bot] at hm
    apply h.setup.radical.1
    rw [hRbot,bot_subgroupOf]
  have hgen : K₀ ⊔ R₀ = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left) (show R ≤ J from le_sup_right),subgroupOf_self]
  have hQR : pCore 2 J ≤ R₀ := fun x hx => source_join_core_le h
    (mem_map_of_mem J.subtype hx)
  have hRi : R₀.map i = R.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x,mem_sup_right hx⟩,hx,rfl⟩
  have hcontrol : R₀.characteristicNormalizerClosure ≤ M₀ := by
    intro x hx
    have hh := map_characteristicNormalizerClosure_le i (inclusion_injective h.join_le) R₀
    rw [hRi] at hh
    exact h.setup.characteristic_control (hh (mem_map_of_mem i hx))
  have hout : ¬K₀ ≤ M₀ := by
    intro hh
    exact h.outside (fun k hk => hh (show (⟨k,mem_sup_left hk⟩ : J) ∈ K₀ from hk))
  have hkernel := (kernel_offender_of_normal_input h).1
  have hmove : ¬K₀ ≤ starKernel K R := by
    intro hh
    apply starImage_ne_bot_of_bound h.normalizes h.quasisimple hkernel.upper
    exact (Subgroup.map_eq_bot_iff K₀).mpr (by simpa only [QuotientGroup.ker_mk'] using hh)
  have hs := QuasisimpleThompson.component_thompson_intersection_control K₀ R₀ M₀
    (starKernel K R) hK hR.comap_subtype hne hgen hQR hkernel.lower hmove hcontrol hout
  have hJR : elementaryAbelianMaxJ R ≤ J :=
    (sSup_le fun _ hA => hA.1).trans (show R ≤ J from le_sup_right)
  have hJ : elementaryAbelianMaxJ R₀ = (elementaryAbelianMaxJ R).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right),
      map_subgroupOf_eq_of_le hJR]
  simpa only [hJ,K₀,M₀,starImage,starM,subgroupOf,comap_inf,inf_comm] using hs
end CFSG.Quasithin.ChapterC.C27Source
