module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieve
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceInspectionRankOne
public import Theory.GroupTheory.PRadical.NormalComponentImages
public import Theory.GroupTheory.SylowKernelIntersectionImage

/-!
# Radicality on the literal secondary action

The original source normalizer control and the Sylow subgroup inside H
force the relative normalizer two-core to equal R₂. Intersecting with the
normal component and passing through its two-core and odd central kernel
then proves radicality of the actual inner image. The kernel Sylow keeps
the image of the component intersection equal to the whole radical image.

Source: Aschbacher--Smith 4.3.14--16, printed pp.617--618. This supplies
the radical-normalizer hypothesis for the remaining proper-local rows.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

omit [Finite G] in
/-- The actual secondary action lies in the full inner component. -/
theorem SecondaryActionData.secondaryImage_le_componentImage (s : SecondaryActionData c n) :
    SecondaryActionData.secondaryImage s ≤ SecondaryActionData.componentImage s := by
  rw [SecondaryActionData.componentImage_eq_inner]
  let := s.normal
  exact SourceImages.secondary_inner c s.component s.secondary_le

/-- The central quotient identifies with the literal inner action image. -/
def SecondaryActionData.centralQuotientEquiv (s : SecondaryActionData c n) :
    (s.component ⧸ pCore 2 s.component) ⧸ center (s.component ⧸ pCore 2 s.component) ≃*
      SecondaryActionData.componentImage s :=
  innerEquivCentralQuotient.symm.trans
    (MulEquiv.subgroupCongr (SecondaryActionData.componentImage_eq_inner s).symm)

omit [Finite G] in
/-- The source Sylow and normalizer control identify the relative normalizer core. -/
theorem SecondaryActionData.radical_relative_normalizer_core (s : SecondaryActionData c n)
    (J : Subgroup G) (hJ : secondary c ⊔ S c ≤ J) :
    (normalizer ((R₂ c).subgroupOf J : Set J)).pCoreIn 2 = (R₂ c).subgroupOf J := by
  let N := normalizer ((R₂ c).subgroupOf J : Set J)
  let U := (N.pCoreIn 2).map J.subtype
  have hRJ : R₂ c ≤ J := (pCoreIn_le 2 _).trans hJ
  have hUN : U ≤ normalizer (R₂ c : Set G) := by
    have hh := map_mono (f := J.subtype) (pCoreIn_le 2 N)
    have hn : N.map J.subtype ≤ normalizer (R₂ c : Set G) := by
      rw [show N = (normalizer (R₂ c : Set G)).subgroupOf J from
        (subgroupOf_normalizer_eq hRJ).symm, subgroupOf_map_subtype]
      exact inf_le_left
    exact hh.trans hn
  have hJN : secondary c ⊔ S c ≤ normalizer (R₂ c : Set G) :=
    (secondary c ⊔ S c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hnU : secondary c ⊔ S c ≤ normalizer (U : Set G) := by
    intro x hx
    have hxN : (⟨x,hJ hx⟩ : J) ∈ N := by
      rw [show N = (normalizer (R₂ c : Set G)).subgroupOf J from
        (subgroupOf_normalizer_eq hRJ).symm]
      exact hJN hx
    exact (N.pCoreIn 2).le_normalizer_map J.subtype
      (mem_map_of_mem J.subtype
        ((N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N
          (pCore 2 N))) hxN))
  have hpU : IsPGroup 2 U := (isPGroup_pCoreIn 2 N).map J.subtype
  have hp : IsPGroup 2 (U ⊔ S c : Subgroup G) := hpU.to_sup_of_normal_left'
    (T.isPGroup'.to_le inf_le_left) (le_sup_right.trans hnU)
  have hUH : U ⊔ S c ≤ c.H :=
    sup_le (hUN.trans (s.radical_normalizer.trans inf_le_left)) inf_le_right
  obtain ⟨P,hP⟩ := c.sylow
  have he : (U ⊔ S c).subgroupOf c.H = (P : Subgroup c.H) :=
    P.is_maximal' hp.comap_subtype (by
      intro x hx
      exact (le_sup_right : S c ≤ U ⊔ S c) (hP.le (mem_map_of_mem _ hx)))
  have hm := congrArg (map c.H.subtype) he
  rw [map_subgroupOf_eq_of_le hUH,hP] at hm
  have hUS : U ≤ S c := le_sup_left.trans_eq hm
  have hUR : U ≤ R₂ c := le_pCoreIn_of_normalizes hpU
    (hUS.trans le_sup_right) hnU
  apply le_antisymm
  · intro x hx
    exact hUR (mem_map_of_mem J.subtype hx)
  · exact le_map_pCore_normalizer
      (isPGroup_pCoreIn 2 (secondary c ⊔ S c)).comap_subtype

omit [Finite G] in
/-- The original nontrivial radical is radical in the root normalizer. -/
theorem SecondaryActionData.root_radical (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ((R₂ c).subgroupOf (rootNormalizer c)).IsPRadical 2 := by
  refine ⟨?_,SecondaryActionData.radical_relative_normalizer_core s _ ?_⟩
  · intro he
    have hh := congrArg (map s.action) he
    rw [Subgroup.map_bot] at hh
    exact s.radical_action hh
  · exact sup_le (s.secondary_le.trans (map_subtype_le _))
      (inf_le_left.trans (root_normalized c D))

/-- The two quotient stages preserve the normalizer core on the literal inner image. -/
theorem SecondaryActionData.inner_radical_normalizer_core (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hRI : SecondaryActionData.radicalImage s ≤ SecondaryActionData.componentImage s) :
    (normalizer ((SecondaryActionData.radicalImage s).subgroupOf
      (SecondaryActionData.componentImage s) : Set (SecondaryActionData.componentImage s))).pCoreIn 2 =
        (SecondaryActionData.radicalImage s).subgroupOf (SecondaryActionData.componentImage s) := by
  let := s.normal
  let R := (R₂ c).subgroupOf (rootNormalizer c)
  let C := s.component
  let U := R.subgroupOf C
  let q := QuotientGroup.mk' (pCore 2 C)
  let z := QuotientGroup.mk' (center (C ⧸ pCore 2 C))
  let e := SecondaryActionData.centralQuotientEquiv s
  have hpU : IsPGroup 2 U :=
    ((isPGroup_pCoreIn 2 (secondary c ⊔ S c)).comap_subtype).comap_subtype
  have hc : (normalizer (U : Set C)).pCoreIn 2 = U :=
    normal_intersection_relative_core C R (SecondaryActionData.root_radical s D)
  have hk : q.ker ≤ U := by
    rw [QuotientGroup.ker_mk']
    exact pCore_le_of_pCore_normalizer_le U hpU hc.le
  have hq := map_normalizer_core_of_p_kernel U hpU hc q
    (QuotientGroup.mk'_surjective _) hk
  have hz : Nat.Coprime 2 (Nat.card z.ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mpr
      (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
        (pCore_quotient_pCore_eq_bot 2) _ le_rfl)
  have hzc : z.ker ≤ center (C ⧸ pCore 2 C) := by
    rw [QuotientGroup.ker_mk']
  have hcz := map_normalizer_core_of_central_coprime_kernel (U.map q) (hpU.map q) hq z
    (QuotientGroup.mk'_surjective _) hzc hz
  have hce := congrArg (map e.toMonoidHom) hcz
  rw [map_pCoreIn_of_injective 2 _ _ e.injective,map_equiv_normalizer_eq] at hce
  let f : C →* SecondaryActionData.componentImage s := s.action.subgroupMap C
  have hf : e.toMonoidHom.comp (z.comp q) = f := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change MulAut.conj (q x) = s.action x
    exact (normalQuotientAction_inner C (pCore 2 C) x).symm
  have he : ((U.map q).map z).map e.toMonoidHom = U.map f := by
    rw [map_map,map_map,MonoidHom.comp_assoc,hf]
  rw [he] at hce
  have himage : U.map f = (SecondaryActionData.radicalImage s).subgroupOf
      (SecondaryActionData.componentImage s) := by
    apply map_injective (SecondaryActionData.componentImage s).subtype_injective
    have hf' : (SecondaryActionData.componentImage s).subtype.comp f = s.action.comp C.subtype := rfl
    rw [map_map,hf',←map_map,subgroupOf_map_subtype,subgroupOf_map_subtype,
      inf_eq_left.mpr hRI]
    obtain ⟨P,hP⟩ := SourceImages.action_kernel_sylow_le c C s.isComponent.perfect D
      s.enlarged_core_le
    exact Subgroup.map_inf_eq_map_of_kernel_sylow_le R C
      (isPGroup_pCoreIn 2 (secondary c ⊔ S c)).comap_subtype s.action P hP hRI
  rwa [himage] at hce

/-- An inner radical image is nontrivial and radical in the component image. -/
theorem SecondaryActionData.inner_radical (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hRI : SecondaryActionData.radicalImage s ≤ SecondaryActionData.componentImage s) :
    ((SecondaryActionData.radicalImage s).subgroupOf (SecondaryActionData.componentImage s)).IsPRadical 2 := by
  refine ⟨?_,SecondaryActionData.inner_radical_normalizer_core s D hRI⟩
  intro he
  have hh := congrArg (map (SecondaryActionData.componentImage s).subtype) he
  rw [map_subgroupOf_eq_of_le hRI,Subgroup.map_bot] at hh
  exact s.radical_action hh

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
