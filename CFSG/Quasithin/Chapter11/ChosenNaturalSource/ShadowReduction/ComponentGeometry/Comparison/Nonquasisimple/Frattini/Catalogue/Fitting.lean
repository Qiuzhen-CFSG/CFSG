module
public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.GroupTheory.Fitting.TwoCorePreimage
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement

/-!
# Identifying the Fitting kernel in the nonquasisimple catalogue

For a finite group with trivial two-core, its Fitting subgroup has odd
order. In a normal nilpotent extension of an odd-field SL₂ group, the
image of the Fitting subgroup lies in the center of order two, hence is
trivial. Thus the displayed extension kernel is exactly the Fitting
subgroup. Applying this to Kz/O₂(Kz) identifies the literal O₂,F quotient.

Both nilpotent and elementary-plane rows are retained. The elementary
row supplies the fitting-model premise of the Frattini product and
residual-quotient consumers in the companion Kernel module. The complete
catalogue still has to be reduced to these rows.
Source: Aschbacher--Smith, 11.1.1 and 11.4.2, printed pp.761 and 777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
open Chapter1.Section02.LocalModels
variable {A : Type*} [Group A] [Finite A]

/-- The normal nilpotent kernel of an odd SL₂ extension is the literal
Fitting subgroup when the original two-core is trivial. -/
theorem fitting_eq_extension_kernel (hcore : pCore 2 A = ⊥)
    (N : Subgroup A) [N.Normal] [Group.IsNilpotent N]
    {p : ℕ} (hp : 3 < p) (ho : Odd p) (hm : Source.IsSL (A ⧸ N) 2 p) :
    fittingSubgroup A = N := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let B := SL(2,F)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective N)
  let : IsQuasisimple B :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by omega) (MulEquiv.refl _)
  have hcent : (fittingSubgroup A).map q ≤ center B :=
    ((map_mono (le_solvableRadical (fittingSubgroup A) inferInstance inferInstance)).trans
      (map_solvableRadical_le_of_surjective q hq)).trans IsQuasisimple.solvableRadical_le_center
  have hcard : Nat.card (center B) = 2 :=
    (GorensteinWalter.sl2ProjectiveProjection_ker F) ▸
      GorensteinWalter.sl2ProjectiveProjection_ker_card F (hF ▸ ho)
  have hodd : Odd (Nat.card (fittingSubgroup A)) :=
    Nat.coprime_two_left.mp ((pPrimeCore_coprime_card (p := 2) (G := A)).of_dvd_right
      (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore)))
  have hdiv : Nat.card ((fittingSubgroup A).map q) ∣ Nat.card (fittingSubgroup A) :=
    card_dvd_of_surjective (q.subgroupMap (fittingSubgroup A)) (q.subgroupMap_surjective _)
  have hc : Nat.card ((fittingSubgroup A).map q) = 1 := by
    have hd := card_dvd_of_le hcent
    rw [hcard] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact he
    · have hh := hodd.of_dvd_nat hdiv
      rw [he] at hh
      norm_num at hh
  have hz : (fittingSubgroup A).map q = ⊥ := Subgroup.card_eq_one.mp hc
  have hk : q.ker = N := by
    ext a
    change e (QuotientGroup.mk' N a) = 1 ↔ a ∈ N
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff a
  exact le_antisymm (hk ▸ (Subgroup.map_eq_bot_iff _).mp hz)
    (le_sSup ⟨inferInstance,inferInstance⟩)

/-- A normal nilpotent extension in the actual two-core quotient determines
the source SL₂ quotient above the actual two-Fitting preimage. -/
theorem twoFitting_sl2_of_nilpotent_extension {p : ℕ} (hp : 3 < p) (ho : Odd p)
    (hm : HasExtension (A ⧸ pCore 2 A)
      (fun N _ => Group.IsNilpotent N ∧ Odd (Nat.card N))
      (fun Q _ => Source.IsSL Q 2 p)) : Source.IsSL (A ⧸ twoFittingCore A) 2 p := by
  obtain ⟨N,hN,hNil,model⟩ := hm
  let : N.Normal := hN
  let : Group.IsNilpotent N := hNil.1
  have hfit := fitting_eq_extension_kernel (pCore_quotient_pCore_eq_bot 2) N hp ho model
  let q := (QuotientGroup.mk' N).comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective N).comp (QuotientGroup.mk'_surjective _)
  have hk : twoFittingCore A = q.ker := by
    change (fittingSubgroup (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' _) = _
    rw [hfit]
    ext x
    exact (QuotientGroup.eq_one_iff (QuotientGroup.mk' (pCore 2 A) x)).symm
  let a := QuotientGroup.liftEquiv (twoFittingCore A) hq hk
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := model
  exact ⟨F,inferInstance,inferInstance,hF,⟨a.trans e⟩⟩

/-- The elementary-plane row supplies the actual Fitting-quotient model,
so it is not an independent recognition premise. -/
theorem twoFitting_sl2_of_elementary_extension {p : ℕ} [Fact p.Prime]
    (hp : 3 < p)
    (hm : HasExtension (A ⧸ pCore 2 A) (ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p)) : Source.IsSL (A ⧸ twoFittingCore A) 2 p := by
  classical
  have ho := (Fact.out : p.Prime).odd_of_ne_two (by omega : p ≠ 2)
  apply twoFitting_sl2_of_nilpotent_extension hp ho
  obtain ⟨N,hN,⟨v⟩,hQ⟩ := hm
  let : N.Normal := hN
  let : IsMulCommutative N := ⟨⟨fun x y => v.injective (by simp only [map_mul,mul_comm])⟩⟩
  have hc : Nat.card N = p ^ 2 := by
    rw [Nat.card_congr v.toEquiv]
    simp [Nat.card_eq_fintype_card]
  exact ⟨N,inferInstance,⟨inferInstance,hc ▸ ho.pow⟩,hQ⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
