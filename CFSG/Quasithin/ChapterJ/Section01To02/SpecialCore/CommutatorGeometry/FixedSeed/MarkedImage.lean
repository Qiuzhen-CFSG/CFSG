module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.FixedSeed.Action
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.CoreEquality.ParabolicImage
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Alternating
public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Theory.GroupTheory.PCoreSurjective
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# The actual natural Sylow image in the fixed-seed calculation

The Ru1 parabolic quotient is S₄, so its two-core has order four.
Lifting that core gives |R₁|=8192. The preceding equality R₁=QS and
|Q|=2048 then give an image of order four for S in H/Q. Since S lies
in the two-residual L₁, this image lies in the original marked A₅.
Under the given Ru2 SL₂(4) marking, it is therefore a Sylow two-subgroup.

The two core equalities from J.2.2(1) remain explicit premises; no
J.2.3 conclusion is assumed. Source: Aschbacher–Smith, printed
pp.432–433 (PDF pp.443–444), assertion (!) in the proof of J.2.3.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry.FixedSeed
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

private theorem card_R₁
    (hcore : (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 = d.toTypeRuSetup.R₁) :
    Nat.card d.toTypeRuSetup.R₁ = 8192 := by
  let f := d.parabolicMap.rangeRestrict
  have hk : f.ker = d.toTypeRuSetup.S.subgroupOf d.parabolic := by
    rw [MonoidHom.ker_rangeRestrict]
    exact d.parabolicMap_kernel
  have hSpar : d.toTypeRuSetup.S ≤ d.parabolic := le_inf (pCoreIn_le 2 _) d.S_le_H
  have hkc : Nat.card f.ker = 2048 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hSpar).toEquiv, d.ru1.card_S]
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact (isPGroup_pCoreIn 2 d.L).comap_subtype
  have hc := f.card_pCore_of_ker_isPGroup d.parabolicMap.rangeRestrict_surjective hkp
  have hpc : Nat.card (pCore 2 d.parabolicMap.range) = 4 := by
    have h := (symmetric_four_model_twoCore_data (Or.inl ⟨d.parabolicImageEquivS4⟩)).2
    have ho : Nat.card d.parabolicMap.range = 24 := by
      rw [Nat.card_congr d.parabolicImageEquivS4.toEquiv, Nat.card_eq_fintype_card]
      decide
    rcases h with h | h <;> omega
  rw [hkc, hpc] at hc
  have hp : d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G) = d.parabolic := by
    rw [← d.H_inf_L, inf_comm]
  rw [← hcore, hp, pCoreIn, card_map_of_injective d.parabolic.subtype_injective, hc]

private theorem coreMap_card
    (hprod : d.toTypeRuSetup.R₁ = d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S)
    (hcore : (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 = d.toTypeRuSetup.R₁) :
    Nat.card (coreMap d).range = 4 := by
  have hR_H : d.toTypeRuSetup.R₁ ≤ d.toTypeRuSetup.H :=
    (pCoreIn_le 2 _).trans ((map_subtype_le _).trans inf_le_right)
  have hQR : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.R₁ := by rw [hprod]; exact le_sup_left
  let f := d.ru2.quotientMap.comp (inclusion hR_H)
  have hk : f.ker = d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.R₁ := by
    ext x
    change inclusion hR_H x ∈ d.ru2.quotientMap.ker ↔ _
    rw [d.ru2.quotient_kernel]
    rfl
  have hc := f.ker.card_mul_index
  rw [index_ker, hk, Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv,
    d.ru2.card_Q d.card_Z, card_R₁ d hcore] at hc
  have hr : f.range = (coreMap d).range := by
    change (d.ru2.quotientMap.comp (inclusion hR_H)).range = _
    rw [MonoidHom.range_comp, inclusion_range, hprod,
      subgroupOf_sup (pCoreIn_le 2 _) d.S_le_H, Subgroup.map_sup,
      ← d.ru2.quotient_kernel, Subgroup.map_ker_self, bot_sup_eq]
    change _ = (d.ru2.quotientMap.comp (inclusion d.S_le_H)).range
    rw [MonoidHom.range_comp, inclusion_range]
  rw [hr] at hc
  omega

/-- J.2.2(1) identifies the image of S with a Sylow in the original
SL₂(4) marking; both literal two-core equalities are retained as inputs. -/
theorem hasNaturalSylowImage
    (hprod : d.toTypeRuSetup.R₁ = d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S)
    (hcore : (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 = d.toTypeRuSetup.R₁) :
    HasNaturalSylowImage d := by
  have hSL₁ : d.toTypeRuSetup.S ≤ d.toTypeRuSetup.L₁ := by
    apply le_trans _ (pCoreIn_le 2 _)
    change d.toTypeRuSetup.S ≤ d.toTypeRuSetup.R₁
    rw [hprod]
    exact le_sup_right
  have hL₁K : d.toTypeRuSetup.L₁ ≤ d.toTypeRuSetup.K := by
    rintro x ⟨a, ha, rfl⟩
    exact mem_map.mpr ⟨inclusion inf_le_right a,
      map_pResidual_le 2 (inclusion inf_le_right) (mem_map.mpr ⟨a, ha, rfl⟩), rfl⟩
  have hm (s : d.toTypeRuSetup.S) : coreMap d s ∈ alternatingGroup (Fin 5) := by
    rw [← d.toTypeRuSetup.quotientMap_K]
    exact mem_map.mpr ⟨inclusion d.S_le_H s, hL₁K (hSL₁ s.property), rfl⟩
  let f : d.toTypeRuSetup.S →* SL2FourNatural.SL :=
    d.ru2.naturalAction.marking.symm.toMonoidHom.comp ((coreMap d).codRestrict _ hm)
  have he (s : d.toTypeRuSetup.S) : markingMap d (f s) = coreMap d s := by
    change (d.ru2.naturalAction.marking (d.ru2.naturalAction.marking.symm _)).val = _
    rw [d.ru2.naturalAction.marking.apply_symm_apply]
    rfl
  have himg : f.range.map (markingMap d) = (coreMap d).range := by
    rw [← MonoidHom.range_comp]
    congr 1
    exact MonoidHom.ext he
  have hi : Function.Injective (markingMap d) :=
    (alternatingGroup (Fin 5)).subtype_injective.comp d.ru2.naturalAction.marking.injective
  have hcard : Nat.card f.range = 4 := by
    rw [← card_map_of_injective hi, himg]
    exact coreMap_card d hprod hcore
  have hfp : IsPGroup 2 f.range :=
    (isPGroup_pCoreIn 2 d.L).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hfp.exists_le_sylow
  have hPc : Nat.card P = 4 := by
    calc
      Nat.card P = Nat.card (Matrix.SpecialLinearGroup.upperUnipotentSylow SL2FourNatural.F 2) :=
        Nat.card_congr (P.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow SL2FourNatural.F 2)).toEquiv
      _ = Nat.card SL2FourNatural.F := Matrix.SpecialLinearGroup.card_upperUnipotent _
      _ = 4 := (Nat.card_eq_fintype_card).trans SL2FourNatural.card_field
  have hr : f.range = (P : Subgroup SL2FourNatural.SL) :=
    eq_of_le_of_card_ge hP (by rw [hcard, hPc])
  exact ⟨P, himg.symm.trans (congrArg (fun A : Subgroup SL2FourNatural.SL => A.map (markingMap d)) hr)⟩

end CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry.FixedSeed
