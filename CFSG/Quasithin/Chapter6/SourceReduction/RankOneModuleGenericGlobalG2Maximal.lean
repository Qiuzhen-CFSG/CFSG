module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2MaximalModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalBlockMaximal

/-!
# Right maximality for the prepared G₂ pair above field order four

The compatible full-overlap comparison identifies both residual factors,
fixes the field order as 2^n, and places the original source S inside each
factor. For n > 2, the short local core dichotomy and characteristic two
force every local overcomponent to have exactly the right residual's core.
Binary component embedding selection then gives right maximality. Applying
the normalizer construction discharges its maximality, common-Sylow and
enlarged-core premises for this row.

The comparison remains an explicit input. The G₂(4) row, exhaustive
comparison and actual ambient completion are not supplied by this module.
The Chapter12 companion applies these results to the literal chosen-module
pair. Source: Aschbacher–Smith 5.2.7–8, printed pp.651–653, and F.1.12,
pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem g2_factor_equiv
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R) (i : Fin 2)
    {X : Type*} [Group X] (P K : Subgroup X)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃* P)
    (hr : (solvableResidual P).map P.subtype = K) :
    Nonempty (![L,R] i ≃* K) := by
  let Q := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  let a : solvableResidual Q ≃* ![L,R] i :=
    ((solvableResidual Q).equivMapOfInjective Q.subtype Q.subtype_injective).trans
      (MulEquiv.subgroupCongr (d.parabolic_residuals h hTH hp i))
  let b : solvableResidual P ≃* K :=
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hr)
  exact ⟨a.symm.trans (e.solvableResidualEquiv.trans b)⟩

private theorem sourceS_le_factor_of_model_sylow
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R) (i : Fin 2)
    {X : Type*} [Group X] [Finite X] (P K : Subgroup X)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃* P)
    (hr : (solvableResidual P).map P.subtype = K)
    (U : Sylow 2 X) (hU : (U : Subgroup X) ≤ K) : sourceS L H ≤ ![L,R] i := by
  have hKP : K ≤ P := hr ▸ map_subtype_le _
  let U0 := U.subtype (hU.trans hKP)
  have hU0 : (U0 : Subgroup P) ≤ solvableResidual P := by
    intro x hx
    have hh := hU hx
    rw [←hr] at hh
    obtain ⟨y,hy,he⟩ := hh
    exact (Subtype.ext he : y=x) ▸ hy
  have hindex : ¬ 2 ∣ (solvableResidual P).index := fun hd =>
    U0.not_dvd_index (hd.trans (index_dvd_of_le hU0))
  let Q := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  have hSQ : sourceS L H ≤ Q := le_sup_right.trans le_sup_left
  let V := ((sourceS L H).subgroupOf Q).map e.toMonoidHom
  have hV : IsPGroup 2 V :=
    ((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map e.toMonoidHom
  have he : V ≤ solvableResidual P := by
    obtain ⟨k,hk⟩ := hV.exists_card_eq
    apply relIndex_eq_one.mp
    exact Nat.eq_one_of_dvd_coprimes
      (by rw [hk]; exact Nat.prime_two.coprime_pow_of_not_dvd hindex)
      ((solvableResidual P).relIndex_dvd_index_of_normal V)
      ((solvableResidual P).relIndex_dvd_card V)
  change ((sourceS L H).subgroupOf Q).map e.toMonoidHom ≤ _ at he
  rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,
    map_le_map_iff_of_injective e.injective] at he
  have hh := map_mono (f := Q.subtype) he
  rwa [map_subgroupOf_eq_of_le hSQ,d.parabolic_residuals h hTH hp i] at hh

/-- The actual G₂ comparison fixes the field and both residual factors.
The source S lies in both factors; both whole-overlap orientations are retained. -/
theorem Preparation.g2_local_structure
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    Nat.card F = 2^n ∧ Nonempty (L ≃* local₂ (F := F)) ∧
      Nonempty (R ≃* local₁ (F := F)) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^n) ∧
      (∀ i : Fin 2, sourceS L H ≤ ![L,R] i) := by
  rcases he with he | he
  · exact (d.not_g2_short_left_parabolic h hTH hp (he.map fun e => e.left)).elim
  obtain ⟨e⟩ := he
  have hq : 2 < Nat.card F := by
    by_contra hn
    have hF : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
    let := G2Short.parabolic_solvable_of_card_two hF
    exact d.parabolics_not_solvable h hp 1
      (Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective)
  obtain ⟨a⟩ := g2_factor_equiv d h hTH hp 0 (parabolic₂ (F := F)) local₂ e.left
    (HigherFieldResiduals.parabolic₂_residual hq)
  obtain ⟨b⟩ := g2_factor_equiv d h hTH hp 1 (parabolic₁ (F := F)) local₁ e.right
    (HigherFieldResiduals.parabolic₁_residual hq)
  let aq := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans local₂CoreQuotientEquivPSL
  let bq := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans local₁CoreQuotientEquivPSL
  have hF : Nat.card F = 2^n := by
    obtain ⟨E,_,_,hE,⟨c⟩⟩ := h.linear
    let := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hE)
    exact (binary_psl_field_card_eq (c.symm.trans aq)).symm.trans hE
  refine ⟨hF,⟨a⟩,⟨b⟩,⟨F,inferInstance,inferInstance,hF,⟨bq⟩⟩,?_⟩
  intro i
  fin_cases i
  · exact sourceS_le_factor_of_model_sylow d h hTH hp 0 _ _ e.left
      (HigherFieldResiduals.parabolic₂_residual hq)
      (Atlas.G2.LieParabolicSetup.sylow (F := F)) sylow_le_local₂
  · exact sourceS_le_factor_of_model_sylow d h hTH hp 1 _ _ e.right
      (HigherFieldResiduals.parabolic₁_residual hq)
      (Atlas.G2.LieParabolicSetup.sylow (F := F)) sylow_le_local₁

private theorem dichotomy_residual_overcomponent_core
    {T : Sylow 2 G} {H J : Subgroup G}
    (hE : IsEvenCharacteristicAt T) (hTH : (T : Subgroup G) ≤ H)
    (hcore : H.pCoreIn 2 = (residual H).pCoreIn 2)
    (hp : Group.IsPerfect (residual H)) (hne : residual H ≠ ⊥)
    (hD : ∀ N : Subgroup (residual H), N.Normal → N ≤ pCore 2 (residual H) →
      N ≤ center (residual H) ∨ N = pCore 2 (residual H))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H ≤ J) :
    J.pCoreIn 2 = (residual H).pCoreIn 2 := by
  have hHJ : H ≤ J ⊔ (T : Subgroup G) := by
    rw [← residual_sup_sylow T H hTH]
    exact sup_le_sup hKJ le_rfl
  have hle : J.pCoreIn 2 ≤ (residual H).pCoreIn 2 :=
    (pCoreAmbient_mono_of_isSubnormalIn J (J ⊔ (T : Subgroup G)) 2
      le_sup_left hJ.1.subnormal).trans
        ((Chapter3.twoCore_le_of_sylow_le T hTH hHJ).trans_eq hcore)
  have hRK : J.pCoreIn 2 ≤ residual H := hle.trans (map_subtype_le _)
  let N := (J.pCoreIn 2).subgroupOf (residual H)
  have hn : N.Normal := normal_subgroupOf_of_le_normalizer
    (hKJ.trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))
  have hN : N ≤ pCore 2 (residual H) := by
    intro x hx
    have hh := hle hx
    exact (mem_map_iff_mem (residual H).subtype_injective).mp hh
  have hnot : ¬ N ≤ center (residual H) := by
    intro hc
    have hchar := Chapter1.mem_He_iff.mpr
      (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T hE hJ)
    have hKR : residual H ≤ J.pCoreIn 2 := by
      intro k hk
      apply hchar
      refine ⟨hKJ hk,mem_centralizer_iff.mpr ?_⟩
      intro r hr
      exact congrArg Subtype.val
        (mem_center_iff.mp (hc (show (⟨r,hRK hr⟩ : residual H) ∈ N from hr)) ⟨k,hk⟩).symm
    let := hp
    let : Nontrivial (residual H) := (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isNilpotent (residual H)
      ((isPGroup_pCoreIn 2 J).to_le hKR).isNilpotent
  have he : N = pCore 2 (residual H) := (hD N hn hN).resolve_left hnot
  apply le_antisymm hle
  rintro _ ⟨x,hx,rfl⟩
  exact (show x ∈ N from he.symm ▸ hx)


/-- In the G₂ row above field order four, every local overcomponent has
exactly the original special two-core. -/
theorem Preparation.g2_overcomponent_core
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect (residual H)) (hn : 2 < n)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J) : J.pCoreIn 2 = (residual H).pCoreIn 2 := by
  obtain ⟨hF,_,⟨a⟩,_,hs⟩ := d.g2_local_structure h hTH hp F he
  have hq : 4 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  apply dichotomy_residual_overcomponent_core (h.qtke.evenCharacteristic T) hTH
    (residual_core_eq_of_sourceS_le h.sylow_normalizes hTH (hs 1)) hp
    (fun hh => d.right_outside (hh ▸ bot_le)) ?_ hJ hKJ
  intro N hnN hN
  let D := N.map a.toMonoidHom
  let : D.Normal := Normal.map hnN a.toMonoidHom a.surjective
  have hD : D ≤ pCore 2 (local₁ (F := F)) := by
    rw [←pCore_map_iso 2 a]
    exact map_mono hN
  rcases G2Maximal.local_core_dichotomy hq D hD with hc | he
  · left
    rw [←center_map_equiv a] at hc
    exact (map_le_map_iff_of_injective a.injective).mp hc
  · right
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [pCore_map_iso]
    exact he

/-- The actual G₂ row has maximal right residual for original n > 2.
The exceptional binary-embedding exponent is excluded using that same n. -/
theorem Preparation.g2_right_maximal
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (hn : 2 < n)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hbinary := (d.g2_local_structure h hH.1.1.2 hp F he).2.2.2.1
  exact residual_binary_maximal_of_overcomponent_core h.qtke hH.1.1 hp h.exponent
    (by omega) hbinary (fun J hJ hKJ => d.g2_overcomponent_core h hH.1.1.2 hp hn F he hJ hKJ)

/-- The literal normalizer pair satisfies the local conditions of 5.3
for G₂ with n > 2, with maximality and both enlarged cores discharged. -/
theorem Preparation.g2_normalizer_local_conditions
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (hn : 2 < n)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  have hc : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := .g2 F he
  exact d.normalizer_local_conditions h hH (d.g2_right_maximal h hH hp hn F he) rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hc)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hc)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
