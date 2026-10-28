module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLinearFive
public import Theory.SpecificGroups.SL2.OddKernelQuinticGeneration

/-!
# Excluding both noncentral-Fitting containers

In the smaller-Sylow A₅ branch the original prime actor is quintic.
Both remaining noncentral-Fitting alternatives have an odd Fitting
kernel and a genuine SL₂ quotient. Apply the fixed-involution generation
obstruction inside the literal X/O₂(X), retaining the selected right
image, the normal containing image and the original actor–Sylow join.

The A₅ containing catalogue therefore reduces to an actual simple J₄
component. Its exclusion, the other containing and changed-Sylow cases,
zero-core recognition and higher-field generation remain with the global
normalization argument. No residual equality is inferred from the
insufficient larger-Sylow local hypotheses.

Source: Aschbacher–Smith A.3.6(3–4), 5.1.13 and 5.2.2,
printed pp.43–45,637–638 and648–649 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
open Chapter1.Section02 LocalModels

/-- The actual smaller-Sylow A₅ branch excludes both noncentral-Fitting
alternatives, retaining their odd kernels and the literal containing image. -/
theorem LocalData.changedSylow_A5_noncentral_exclusion
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (P₀ : Sylow 2 (extension T L H B D R))
    (hP : (P₀ : Subgroup (extension T L H B D R)).map
      (extension T L H B D R).subtype = normalizingSylow T R)
    (_hKX : K ≤ generated L H D R ⊔ normalizingSylow T R) (hRK : R ≤ K)
    (_hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hcommon : let X := generated L H D R ⊔ normalizingSylow T R
      A36Common ((K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))))
    (hm : let X := generated L H D R ⊔ normalizingSylow T R
      let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      A36Natural I ∨ A36Nilpotent I) : False := by
  have hp5 := d.selected_A5_actor_prime h hH hgen c hd hz hs hthree hA5
  subst p
  have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R) :=
    Chapter1.IsSylowIn.restrict ⟨P₀,hP⟩ le_sup_right le_sup_left
  let X := generated L H D R ⊔ normalizingSylow T R
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  let Dbar := (D.subgroupOf X).map q
  have hRX : R ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  have hTX : normalizingSylow T R ≤ X := le_sup_right
  obtain ⟨S,hS⟩ := hSyl
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  let : (K.subgroupOf X).Normal := hKn
  let : Kbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  have hPR : (P : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (Rbar : Set (X ⧸ pCore 2 X)) := by
    change (S : Subgroup X).map q ≤ _
    rw [heS]
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
  have hjoin : Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) =
      ((D ⊔ normalizingSylow T R).subgroupOf X).map q := by
    change Dbar ⊔ (S : Subgroup X).map q = _
    rw [heS,subgroupOf_sup hDX hTX,Subgroup.map_sup]
  obtain ⟨a,ha⟩ := d.actor_join_order h hH c hd
  have hdiv : Nat.card (Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) : Subgroup _) ∣
      2^a * 5 := by
    rw [hjoin]
    apply (((D ⊔ normalizingSylow T R).subgroupOf X).card_map_dvd q).trans
    rwa [Nat.card_congr (subgroupOfEquivOfLe (sup_le hDX hTX)).toEquiv]
  have hsol : Group.IsSolvable (Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) : Subgroup _) := by
    rw [hjoin]
    let := d.actor_join_solvable h hH c hd
    let : Group.IsSolvable ((D ⊔ normalizingSylow T R).subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (sup_le hDX hTX)).toMonoidHom)
        (subgroupOfEquivOfLe (sup_le hDX hTX)).injective
    exact Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  let : Group.IsPerfect (R.subgroupOf X) := Chapter1.mem_L_isPerfect hlocal
  let r := q.subgroupMap (R.subgroupOf X)
  let : Group.IsPerfect Rbar := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective _)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eRX := subgroupOfEquivOfLe hRX
  let e₁ := QuotientGroup.congr _ _ eRX (pCore_map_iso 2 eRX)
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  obtain ⟨E,_,_,hE,⟨eE⟩⟩ := hA5
  let e5 := (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hE).some
  let eR : (Rbar ⧸ pCore 2 Rbar) ≃* alternatingGroup (Fin 5) :=
    e₂.symm.trans (e₁.trans (eE.trans e5))
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (Rbar ⧸ pCore 2 Rbar) := eR.isSimpleGroup
  have heven : 2 ∣ Nat.card Rbar := by
    have hh := (pCore 2 Rbar).card_quotient_dvd_card
    rw [Nat.card_congr eR.toEquiv,nat_card_alternatingGroup] at hh
    norm_num at hh
    exact (by decide : 2 ∣ 60).trans hh
  obtain ⟨F,_,_,ho,⟨eF⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Odd (Nat.card F) ∧ Nonempty ((Kbar ⧸ fittingSubgroup Kbar) ≃* SL(2,F)) := by
    rcases hm with hn | hn
    · obtain ⟨p,hp,hp3,F,_,_,hF,v,e,_⟩ := hn.2
      exact ⟨F,inferInstance,inferInstance,hF ▸ hp.eq_two_or_odd'.resolve_left (by omega),
        ⟨(QuotientGroup.quotientMulEquivOfEq hn.1.symm).trans e⟩⟩
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hn.2.2.1
      exact ⟨F,inferInstance,inferInstance,by rw [hF]; decide,
        ⟨(QuotientGroup.quotientMulEquivOfEq hn.1.symm).trans e⟩⟩
  let f := eF.toMonoidHom.comp (QuotientGroup.mk' (fittingSubgroup Kbar))
  have hf : Function.Surjective f := eF.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = fittingSubgroup Kbar := by
    rw [MonoidHom.ker_comp_of_injective _ _ eF.injective,QuotientGroup.ker_mk']
  have hcop : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hker,hcommon.1]
    exact pPrimeCore_coprime_card
  let : Group.IsSolvable f.ker := by rw [hker]; infer_instance
  have hXeq : R ⊔ (D ⊔ normalizingSylow T R) = X := by
    apply le_antisymm (sup_le hRX (sup_le hDX hTX))
    exact sup_le (sup_le (le_sup_left.trans le_sup_right)
      (sup_le le_sup_left ((d.sourceS_le_normalizingSylow h hH).trans
        (le_sup_right.trans le_sup_right)))) (le_sup_right.trans le_sup_right)
  have hgenerate : Rbar ⊔ (Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X))) = ⊤ := by
    change (R.subgroupOf X).map q ⊔ ((D.subgroupOf X).map q ⊔ (S : Subgroup X).map q) = ⊤
    rw [heS,←Subgroup.map_sup,←Subgroup.map_sup,←subgroupOf_sup hDX hTX,
      ←subgroupOf_sup hRX (sup_le hDX hTX),hXeq,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact Theory.SpecificGroups.SL2.OddKernel.not_generated_by_five_actor Kbar Rbar Dbar (map_mono (comap_mono hRK)) P hPR
    f hf hcop ho heven (pCore_quotient_pCore_eq_bot 2) hgenerate hsol hdiv

/-- After excluding both odd-radical alternatives, the actual A₅ containing
image is a simple J₄ component. This does not assert ambient maximality. -/
theorem LocalData.changedSylow_A5_remaining_janko
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (P : Sylow 2 (extension T L H B D R))
    (hP : (P : Subgroup (extension T L H B D R)).map
      (extension T L H B D R).subtype = normalizingSylow T R)
    (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R) (hRK : R ≤ K)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hm : RemainingSourceContainer (generated L H D R ⊔ normalizingSylow T R) K) :
    let X := generated L H D R ⊔ normalizingSylow T R
    let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    A36Common I ∧ IsComponent (X ⧸ pCore 2 X) I ∧ IsSimpleGroup I ∧
      Nonempty (I ≃* Janko4.Model) := by
  obtain ⟨hc,hcases⟩ := d.changedSylow_A5_remaining_nonternary h hH hgen hthree c hd hz hs
    P hP hKX hRK hK hKn hA5 hm
  refine ⟨hc,?_⟩
  rcases hcases with hj | hn | hn
  · exact hj
  · exact (d.changedSylow_A5_noncentral_exclusion h hH hgen hthree c hd hz hs
      P hP hKX hRK hK hKn hA5 hc (.inl hn)).elim
  · exact (d.changedSylow_A5_noncentral_exclusion h hH hgen hthree c hd hz hs
      P hP hKX hRK hK hKn hA5 hc (.inr hn)).elim

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
