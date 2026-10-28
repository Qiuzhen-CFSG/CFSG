module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.Contracts
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicNormalizer
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The second cubic normalizer from relative root normality

Let U be the selected root four-group and let y be a cubic element of the
actual component E(C_G(t)). If U is normal in C_G(⟨y⟩), then that centralizer
lies in the marked N_G(U) ≃ A₄ × A₅. The cubic centralizer in A₅ has order
three, while every two-subgroup of A₄ lies in its Klein four-group. Thus
U is precisely the embedded O₂(C_G(⟨y⟩)), and the full N_G(⟨y⟩) preserves U.

The component marking places ⟨y⟩ wholly in the A₅ factor. Restricting the
actual normalizer equivalence, and using the intrinsic cubic-normalizer
isomorphism in A₅, gives the full ambient normalizer S₃ × A₄. No ambient
normalizer containment or characteristicity is assumed. The source producer
of relative root normality remains with the parent assembly.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3(2), printed pp.261–262.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer
open InvolutionGeometry

private theorem model_cubic_centralizer_card (b : A5) (hb : orderOf b = 3) :
    Nat.card (centralizer (zpowers b : Set A5)) = 3 := by
  let P := zpowers b
  have hP : Nat.card P = 3 := by rw [Nat.card_zpowers, hb]
  have hPC : P ≤ centralizer (P : Set A5) := P.le_centralizer
  have hCN := centralizer_le_normalizer (P : Set A5)
  have hn := alternatingGroup.FiveLocalGeometry.cubic_normalizer_card (MulEquiv.refl A5) P hP
  have hd := card_dvd_of_le hCN
  rw [hn] at hd
  have hle := Nat.le_of_dvd (by omega : 0 < 6) hd
  have hp := card_dvd_of_le hPC
  rw [hP] at hp
  have hpos : 0 < Nat.card (centralizer (P : Set A5)) := Nat.card_pos
  have hne : Nat.card (centralizer (P : Set A5)) ≠ 6 := by
    intro hc
    have he := eq_of_le_of_card_ge hCN (by omega)
    obtain ⟨a, ha, x, hx, hm⟩ :=
      alternatingGroup.FiveLocalGeometry.exists_noncommuting_normalizer (MulEquiv.refl A5) P hP
    have haC : a ∈ centralizer (P : Set A5) := he.symm ▸ ha
    exact hm (haC x hx).symm
  change Nat.card (centralizer (P : Set A5)) = 3
  omega

private theorem model_two_subgroup_le_core (b : A5) (hb : orderOf b = 3)
    (Q : Subgroup (A4 × A5)) (hQ : IsPGroup 2 Q)
    (hC : Q ≤ (⊤ : Subgroup A4).prod (centralizer (zpowers b : Set A5))) :
    Q ≤ (pCore 2 A4).prod (⊥ : Subgroup A5) := by
  apply le_prod_iff.mpr
  constructor
  · obtain ⟨T, hT⟩ := (hQ.map (MonoidHom.fst A4 A5)).exists_le_sylow
    rw [alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by norm_num) T,
      ← AlternatingFourPair.twoCore_eq_kleinFour] at hT
    exact hT
  · have hR := (le_prod_iff.mp hC).2
    have hd := card_dvd_of_le hR
    rw [model_cubic_centralizer_card b hb] at hd
    obtain ⟨n, hn⟩ := (hQ.map (MonoidHom.snd A4 A5)).exists_card_dvd_pow
    exact (card_eq_one.mp (Nat.eq_one_of_dvd_coprimes
      ((by norm_num : Nat.Coprime 3 2).pow_right n) hd hn)).le

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private theorem component_coordinate (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3) :
    ∃ b : A5, orderOf b = 3 ∧ (S.normalizerEquiv.symm (1, b) : G) = y := by
  rw [← S.normalizer_component] at hy
  obtain ⟨⟨a, b⟩, hab, he⟩ := hy
  have ha : a = 1 := hab.1
  subst a
  refine ⟨b, ?_, he⟩
  let f : A5 →* G := (normalizer (rootCore S.t : Set G)).subtype.comp
    (S.normalizerEquiv.symm.toMonoidHom.comp (MonoidHom.inr A4 A5))
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (S.normalizerEquiv.symm.injective.comp
      (fun a b h => congrArg Prod.snd h))
  have ho := orderOf_injective f hf b
  change orderOf ((S.normalizerEquiv.symm (1, b) : normalizer (rootCore S.t : Set G)) : G) = _ at ho
  change (S.normalizerEquiv.symm (1, b) : G) = y at he
  rw [he, hyo] at ho
  exact ho.symm

/-- Relative normality makes the root the actual two-core of the cubic centralizer. -/
theorem rootCore_eq_cubicCentralizer_pCoreIn (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3) (hU : RootNormal S y) :
    rootCore S.t = (cubicCentralizer y).pCoreIn 2 := by
  let U := rootCore S.t
  let C := cubicCentralizer y
  let N := normalizer (U : Set G)
  have hUC : U ≤ C := rootCore_le_cubicCentralizer S hy
  have hCN : C ≤ N := (normal_subgroupOf_iff_le_normalizer hUC).mp hU
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) hUC hCN
  · obtain ⟨b, hb, hby⟩ := component_coordinate S hy hyo
    let f : C →* (A4 × A5) := S.normalizerEquiv.toMonoidHom.comp (inclusion hCN)
    let Q := (pCore 2 C).map f
    have hQ : IsPGroup 2 Q := pCore_isPGroup.map f
    have hQC : Q ≤ (⊤ : Subgroup A4).prod (centralizer (zpowers b : Set A5)) := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨mem_top _, ?_⟩
      change (f x).2 ∈ centralizer (zpowers b : Set A5)
      rw [Subgroup.zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
      have hxy := x.property y (mem_zpowers y)
      have he : S.normalizerEquiv.symm (1,b) * inclusion hCN x =
          inclusion hCN x * S.normalizerEquiv.symm (1,b) := by
        apply Subtype.ext
        change (S.normalizerEquiv.symm (1,b) : G) * (x : G) =
          (x : G) * (S.normalizerEquiv.symm (1,b) : G)
        rw [hby]
        exact hxy
      have hm := congrArg (fun a : N => (S.normalizerEquiv a).2) he
      simpa only [map_mul, S.normalizerEquiv.apply_symm_apply, Prod.snd_mul,
        f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hm.symm
    have hQcore := model_two_subgroup_le_core b hb Q hQ hQC
    rintro _ ⟨x, hx, rfl⟩
    rw [← S.normalizer_core]
    refine ⟨f x, hQcore (mem_map_of_mem f hx), ?_⟩
    change (S.normalizerEquiv.symm (S.normalizerEquiv (inclusion hCN x)) : G) = (x : G)
    simp only [MulEquiv.symm_apply_apply, coe_inclusion]

/-- The full cubic normalizer preserves the intrinsic root four-group. -/
theorem normalizer_le_rootCore_normalizer_of_rootNormal (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3) (hU : RootNormal S y) :
    normalizer (zpowers y : Set G) ≤ normalizer (rootCore S.t : Set G) := by
  rw [rootCore_eq_cubicCentralizer_pCoreIn S hy hyo hU]
  exact (normalizer_le_normalizer_centralizer (zpowers y)).trans
    (normalizer_le_normalizer_characteristic_image (cubicCentralizer y)
      (pCore 2 (cubicCentralizer y)))

private theorem pure_zpowers (b : A5) :
    zpowers ((1 : A4), b) = (⊥ : Subgroup A4).prod (zpowers b) := by
  apply le_antisymm
  · exact zpowers_le.mpr ⟨rfl, mem_zpowers b⟩
  · rintro ⟨a,c⟩ ⟨ha,hc⟩
    have ha' : a = 1 := ha
    subst a
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hc
    exact mem_zpowers_iff.mpr ⟨n, by simp⟩

private theorem pure_normalizer (P : Subgroup A5) :
    normalizer ((⊥ : Subgroup A4).prod P : Set (A4 × A5)) =
      (⊤ : Subgroup A4).prod (normalizer (P : Set A5)) := by
  ext g
  simp only [mem_normalizer_iff, mem_prod, mem_bot, mem_top, true_and]
  constructor
  · intro h x
    simpa using h (1, x)
  · intro h x
    simpa using Iff.and (Iff.rfl : x.1 = 1 ↔ x.1 = 1) (h x.2)

/-- The normal-root branch of Aschbacher 47.3(2), for the actual component
representative and full ambient normalizer. -/
theorem normalizer_equiv_of_rootNormal (S : SelectedGeometry D) {y : G}
    (hy : y ∈ rootComponent S.t) (hyo : orderOf y = 3) (hU : RootNormal S y) :
    Nonempty (normalizer (zpowers y : Set G) ≃*
      (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))) := by
  let N := normalizer (rootCore S.t : Set G)
  let Y := zpowers y
  have hNN : normalizer (Y : Set G) ≤ N :=
    normalizer_le_rootCore_normalizer_of_rootNormal S hy hyo hU
  have hYN : Y ≤ N := Y.le_normalizer.trans hNN
  obtain ⟨b, hb, hby⟩ := component_coordinate S hy hyo
  have hY : Y.subgroupOf N = zpowers (S.normalizerEquiv.symm (1,b)) := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hYN, MonoidHom.map_zpowers]
    change zpowers y = zpowers (S.normalizerEquiv.symm (1,b) : G)
    rw [hby]
  have hmap : (Y.subgroupOf N).map S.normalizerEquiv.toMonoidHom =
      (⊥ : Subgroup A4).prod (zpowers b) := by
    rw [hY, MonoidHom.map_zpowers]
    change zpowers (S.normalizerEquiv (S.normalizerEquiv.symm (1,b))) = _
    rw [S.normalizerEquiv.apply_symm_apply, pure_zpowers]
  have hnmap : ((normalizer (Y : Set G)).subgroupOf N).map
      S.normalizerEquiv.toMonoidHom =
      (⊤ : Subgroup A4).prod (normalizer (zpowers b : Set A5)) := by
    rw [subgroupOf_normalizer_eq hYN, map_equiv_normalizer_eq, hmap, pure_normalizer]
  obtain ⟨eb⟩ := alternatingGroup.FiveLocalGeometry.cubic_normalizer_equiv
    (MulEquiv.refl A5) (zpowers b) (by rw [Nat.card_zpowers, hb])
  exact ⟨(subgroupOfEquivOfLe hNN).symm.trans
    ((((normalizer (Y : Set G)).subgroupOf N).equivMapOfInjective
      S.normalizerEquiv.toMonoidHom S.normalizerEquiv.injective).trans
      ((MulEquiv.subgroupCongr hnmap).trans
        ((prodEquiv _ _).trans ((MulEquiv.prodCongr topEquiv eb).trans
          MulEquiv.prodComm))))⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer
