module
public import CFSG.Quasithin.Chapter14.Section02.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import Theory.GroupTheory.PlaneCoreNormalClosure
public import Theory.GroupTheory.PCoreFrattiniTransport
/-!
# The actual residual--Sylow quotient in the plane source

Inside M, the residual image is cyclic of order three and its kernel is
O₂(Y). Its product with the original Sylow has two-group kernel, because
the cubic and Sylow images are disjoint. The product maps onto S₃, so that
kernel is exactly O₂(YT). All maps use the original local centralizer and
original normal-closure residual. No quotient or kernel conclusion is assumed.
Source: Aschbacher--Smith14.1.18 and14.2.20, printed pp.980--981,988.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual YT quotient is S₃; its action kernel is precisely its two-core. -/
theorem source_residualSylow_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3)) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    X.pCoreIn 2 = X ⊓ centralizer (localModule T M : Set G) ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) := by
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  let f := e.toMonoidHom.comp (QuotientGroup.mk' C)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective C)
  have hk : f.ker = C := by
    ext x
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ C
    rw [←e.map_one,e.injective.eq_iff,QuotientGroup.eq_one_iff]
  let Y := (sourceResidual M Mc).subgroupOf M
  let S := T.subtype hM.1.2
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  let J := Y ⊔ (S : Subgroup M)
  have hJ : J = X.subgroupOf M := (subgroupOf_sup (sourceResidual_le _ _) hM.1.2).symm
  let : Y.Normal := residualY_normal M Mc
  obtain ⟨_,_,_,_,heY,hcore,rest⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  obtain ⟨eY⟩ := heY
  have hYc : Nat.card (Y.map f) = 3 := by
    change Nat.card (Y.map (e.toMonoidHom.comp (QuotientGroup.mk' C))) = 3
    rw [←Subgroup.map_map,Nat.card_congr
      ((Y.map (QuotientGroup.mk' C)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm]
    rw [Nat.card_congr eY.toEquiv]
    exact Nat.card_zmod 3
  have hSc : Nat.card ((S : Subgroup M).map f) = 2 := by
    let P := S.mapSurjective hf
    have hd : Nat.card P ∣ 2*3 := by
      have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
      simpa only [hc] using P.toSubgroup.card_subgroup_dvd_card
    have hc : Nat.Coprime (Nat.card P) 3 := by
      obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 2 3).pow_left n
    rcases (Nat.dvd_prime Nat.prime_two).mp (hc.dvd_mul_right.mp hd) with h | h
    · have hn := P.ne_bot_of_dvd_card (by simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
      exact (hn (card_eq_one.mp h)).elim
    · exact h
  have hYk : IsPGroup 2 (Y ⊓ f.ker : Subgroup M) := by
    have he : Y ⊓ f.ker =
        (sourceResidual M Mc ⊓ centralizer (localModule T M : Set G)).subgroupOf M := by
      rw [hk]
      rfl
    rw [he,←hcore]
    exact (isPGroup_pCoreIn 2 _).comap_subtype
  have hker : IsPGroup 2 (J ⊓ f.ker : Subgroup M) :=
    join_inf_ker_isPGroup_of_disjoint_images f Y (S : Subgroup M)
      le_normalizer_of_normal hYk S.isPGroup'
      ((IsPGroup.of_card (p := 3) (n := 1) (by simpa using hYc)).disjoint_of_ne
        3 2 (by decide) _ _ (S.isPGroup'.map f))
  obtain ⟨hQ,⟨eJ⟩⟩ := product_twoCore_of_permThree f J
    (permThree_join_image_eq_top f Y (S : Subgroup M) hYc hSc) hker
  have hJmap : J.map M.subtype = X := by rw [hJ,map_subgroupOf_eq_of_le hXM]
  have hCmap : C.map M.subtype = M ⊓ centralizer (localModule T M : Set G) := by
    rw [subgroupOf_map_subtype,inf_comm]
  have hQmap := congrArg (Subgroup.map M.subtype) hQ
  rw [map_pCoreIn_of_injective 2 J M.subtype M.subtype_injective,hJmap,
    Subgroup.map_inf _ _ _ M.subtype_injective,hJmap,hk,hCmap,←inf_assoc,inf_eq_left.mpr hXM] at hQmap
  let a : X ≃* J := (subgroupOfEquivOfLe hXM).symm.trans (MulEquiv.subgroupCongr hJ.symm)
  let b := a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
    (IsPGroup.ker_isPGroup_of_injective a.injective)
  exact ⟨hQmap,⟨b.trans eJ⟩⟩

end CFSG.Quasithin.Chapter14.Section02
