module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowAction
public import Theory.SpecificGroups.Alternating.SevenSolvablePrimeActors
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSeven
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeHallRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentOverlapRank

/-!
# The alternating containing cases of the smaller changed Sylow

For X = G₀T₀ the original prime actor survives in X/O₂(X) and acts
faithfully on its normal containing component. The literal subgroup DT₀
is solvable. If that component has central quotient A₇, the quintic
actor is excluded by the solvable Sylow-overgroup theorem for A₇.
Thus both the A₇ and central triple-cover alternatives force p = 3.

When the selected right factor is an actual C-component of H with A₅
quotient, its Hall intersection has order three. Two different conjugate
component images would put two three-directions in the original overlap,
contradicting its rank bound in the presence of the escaping cubic actor.
Hence T would normalize the factor, contradicting the nonzero-core branch.
Combining the arguments excludes these two containing models for an actual
A₅ component. The parabolic case retains its separate source obligations.

Source: Aschbacher--Smith 5.1.10--13 and 5.2.2, pp.634--638,648--649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- A normal overcomponent with central quotient A₇ forces the original escaping actor to be cubic. -/
theorem LocalData.source_overcomponent_seven_central_quotient_prime
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* alternatingGroup (Fin 7)) :
    p = 3 := by
  rcases hd.prime with hp | hp
  · exact hp
  subst p
  exfalso
  let X := generated L H D R ⊔ normalizingSylow T R
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  let Dbar := (D.subgroupOf X).map q
  have hRX : R ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  have hTX : normalizingSylow T R ≤ X := le_sup_right
  obtain ⟨hc,hdis,_⟩ := d.right_quotient_prime_orbit h hH c hd hz hRX hDX hSyl
  obtain ⟨S,hS⟩ := hSyl
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  let : (K.subgroupOf X).Normal := hKn
  let : Kbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let : Group.IsPerfect Kbar := (hK.map_quotient (pCore 2 X)).perfect
  have hdC : Disjoint Dbar (centralizer (Kbar : Set (X ⧸ pCore 2 X))) :=
    hdis.mono_right ((centralizer_le (map_mono (comap_mono hRK))).trans
      (centralizer_le_normalizer (Rbar : Set (X ⧸ pCore 2 X))))
  have hsol : Group.IsSolvable (Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) : Subgroup _) := by
    let := d.actor_join_solvable h hH c hd
    let : Group.IsSolvable ((D ⊔ normalizingSylow T R).subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (sup_le hDX hTX)).toMonoidHom)
        (subgroupOfEquivOfLe (sup_le hDX hTX)).injective
    have hs : Group.IsSolvable (((D ⊔ normalizingSylow T R).subgroupOf X).map q) :=
      Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
    change Group.IsSolvable (Dbar ⊔ (S : Subgroup X).map q : Subgroup _)
    rw [heS]
    rw [subgroupOf_sup hDX hTX,Subgroup.map_sup] at hs
    exact hs
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  let eZ : (Kbar ⧸ center Kbar) ≃* ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) :=
    QuotientGroup.congr _ _ eK (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr eK ⟨x,hx⟩).property
      · intro y hy
        exact ⟨eK.symm y,(centerCongr eK.symm ⟨y,hy⟩).property,eK.apply_symm_apply y⟩)
  exact Theory.SpecificGroups.Alternating.SevenSolvablePrimeActors.no_five_actor
    Kbar Dbar (eZ.trans e) P hc hdC hsol

/-- The actual A₇ and central triple-cover alternatives both force p = 3. -/
theorem LocalData.source_overcomponent_alternating_seven_prime
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hm : Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) : p = 3 := by
  have he : Nonempty (((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃*
      alternatingGroup (Fin 7)) := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      have hzK : center (K ⧸ pCore 2 K) = ⊥ := by
        apply eq_bot_iff.mpr
        intro x hx
        have hh := (centerCongr e ⟨x,hx⟩).property
        change e x ∈ center (alternatingGroup (Fin 7)) at hh
        rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
        exact e.map_eq_one_iff.mp hh
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hzK).trans QuotientGroup.quotientBot).trans e⟩
    · exact hm.2.2
  exact d.source_overcomponent_seven_central_quotient_prime h hH c hd hz hSyl hRK hKX hK hKn he.some

/-- An actual moved A₅ component of H is incompatible with a cubic escaping actor. -/
theorem LocalData.cubic_component_not_A5
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H 3 D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : False := by
  let C := R.subgroupOf H
  let M := (normalizer (L : Set G)).subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let Cbar := C.map q
  let Mbar := M.map q
  have hRH : R ≤ H := d.right_le_residual.trans (map_subtype_le _)
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hRH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hRH))
  let eC : Cbar ≃* (R ⧸ pCore 2 R) := (cComponentTwoCoreQuotientEquiv hC).symm.trans ec
  have hA5copy := hA5
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hA5
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let e := eC.trans (eF.trans e5)
  have hcenter : center Cbar = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (alternatingGroup (Fin 5)) at hh
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hCb := hC.map_quotient (pCore 2 H)
  let : Group.IsPerfect Cbar := hCb.perfect
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup Cbar := e.isSimpleGroup
  let : IsQuasisimple Cbar := ⟨((QuotientGroup.quotientMulEquivOfEq hcenter).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hcomp : IsComponent (H ⧸ pCore 2 H) Cbar := ⟨hCb.subnormal,inferInstance⟩
  have hrM : primeRank 3 M ≤ 1 := by
    have he : (normalizer (L : Set G) ⊓ H).subgroupOf H = M := inf_subgroupOf_right _ _
    rw [←he,primeRank_equiv 3 (subgroupOfEquivOfLe inf_le_right)]
    exact c.overlap_primeRank_le_one h hd hH.1.1.1
  have hr : primeRank 3 Mbar ≤ 1 := by
    apply (primeRank_le_of_surjective_of_coprime 3 (q.subgroupMap M)
      (q.subgroupMap_surjective M) ?_).trans hrM
    have hk : IsPGroup 2 (q.subgroupMap M).ker := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    obtain ⟨k,hk⟩ := hk.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  let E := (B ⊓ R).subgroupOf H
  have hEH : B ⊓ R ≤ H := inf_le_right.trans hRH
  have hEc : Nat.card E = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv]
    have hh := d.right_cartan_card c (m := 2) hA5copy
    norm_num at hh
    exact hh
  have hk : IsPGroup 2 (q.subgroupMap E).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hkc : Nat.card (q.subgroupMap E).ker ∣ 3 :=
    hEc ▸ (q.subgroupMap E).ker.card_subgroup_dvd_card
  have hki : Function.Injective (q.subgroupMap E) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply card_eq_one.mp
    apply hk.card_eq_or_dvd.resolve_right
    intro ht
    have hh := ht.trans hkc
    norm_num at hh
  have hEbc : Nat.card (E.map q) = 3 :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap E)
      ⟨hki,q.subgroupMap_surjective E⟩).toEquiv).symm.trans hEc
  let : IsCyclic (E.map q) := isCyclic_of_prime_card hEbc
  let : CommGroup (E.map q) := IsMulCommutative.instCommGroup
  have hEr : 1 ≤ primeRank 3 (E.map q) := primeRank_ge_of_elementary_embedding
    (fun x : E.map q => by simpa only [hEbc] using pow_card_eq_one' (x := x))
    (by simpa using hEbc) (MonoidHom.id (E.map q)) Function.injective_id
  have hEM : E.map q ≤ Mbar ⊓ Cbar := le_inf
    (map_mono (comap_mono (inf_le_left.trans (c.right_le.trans inf_le_left))))
    (map_mono (comap_mono inf_le_right))
  have hl := hEr.trans (primeRank_mono 3 hEM)
  have hnorm := hcomp.normalizes_of_overlap_primeRank (M := Mbar) hcenter 3 (by omega)
  have hT : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    intro t ht
    let tH : H := ⟨t,hH.1.1.2 ht⟩
    have hh : q tH ∈ normalizer (Cbar : Set (H ⧸ pCore 2 H)) :=
      hnorm (mem_map_of_mem q (show tH ∈ M from h.sylow_normalizes ht))
    have htC : tH ∈ normalizer (C : Set H) := by
      rw [←normalizer_cComponent_quotient hC (pCore 2 H)]
      exact hh
    rw [←subgroupOf_normalizer_eq hRH] at htC
    exact htC
  exact (d.normalizingSylow_lt hH.1.1.2 c hd hz).ne (inf_eq_left.mpr hT)

/-- A moved actual A₅ component forces the escaping actor to be quintic,
independently of its later containing-component model. -/
theorem LocalData.A5_component_actor_prime
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : p = 5 := by
  rcases hd.prime with hp | hp
  · subst p
    exact (d.cubic_component_not_A5 h hH c hd hz hC hA5).elim
  · exact hp

/-- For an actual A₅ component, both alternating overcomponent cases are impossible.
The same original actor is cubic by the local quotient argument and excluded by
its right Hall rank. No equality between a parabolic and an H-component is used. -/
theorem LocalData.A5_component_not_alternating_seven_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hm
  have hp := d.source_overcomponent_alternating_seven_prime h hH c hd hz hSyl hRK hKX hK hKn hm
  have hf := d.A5_component_actor_prime h hH c hd hz hC hA5
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
