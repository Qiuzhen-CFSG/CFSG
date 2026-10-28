module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Solvable
public import Theory.SpecificGroups.SL2.OddAbelianSubgroups
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The literal odd prime image in the multiplicity plane

For the original subgroup P≤O²(H)≤Y, nontriviality and the order of Y
make p coprime to q−1. The faithful embedding of the actual action
quotient C/C_C(W/V₁) restricts to an embedding of the literal P-image.
Its determinant is trivial. Odd prime subgroups in SL₂ are cyclic,
and the SL₂ order formula removes the coprime q(q−1) factors, giving
an order dividing q+1. Centralization of X₁ uses the existing residual
image theorem and exactly the same quotient action.

Source: Aschbacher--Smith 11.5.7, printed p.782.
-/

public section
open Subgroup
noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open CFSG.Quasithin.Chapter12.Section02
private theorem cyclic_plane_image {F A : Type*} [Field F] [Finite F] [CharP F 2]
    [Group A] [Finite A] {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hpn : Nat.Coprime p (2 ^ n - 1))
    (hF : Nat.card F = 2 ^ n) (hA : IsPGroup p A)
    (ρ : A →* GL (Fin 2) F) (hi : Function.Injective ρ) :
    IsCyclic A ∧ Nat.card A ∣ 2 ^ n + 1 := by
  have hpcard : Nat.Coprime (Nat.card A) (2 ^ n - 1) := by
    obtain ⟨k,hk⟩ := hA.exists_card_eq
    rw [hk]
    exact hpn.pow_left k
  have hdet (a : A) : Matrix.GeneralLinearGroup.det (ρ a) = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hda : orderOf (Matrix.GeneralLinearGroup.det (ρ a)) ∣ Nat.card A :=
      (orderOf_map_dvd (Matrix.GeneralLinearGroup.det.comp ρ) a).trans (orderOf_dvd_natCard a)
    have hdf : orderOf (Matrix.GeneralLinearGroup.det (ρ a)) ∣ 2 ^ n - 1 := by
      simpa only [Nat.card_units,hF] using orderOf_dvd_natCard
        (Matrix.GeneralLinearGroup.det (ρ a))
    simpa only [hpcard.gcd_eq_one] using Nat.dvd_gcd hda hdf
  let σ : A →* Matrix.SpecialLinearGroup (Fin 2) F := {
    toFun := fun a => ⟨(ρ a).val,Units.ext_iff.mp (hdet a)⟩
    map_one' := by apply Subtype.ext; exact congrArg Units.val ρ.map_one
    map_mul' := fun a b => by apply Subtype.ext; exact congrArg Units.val (ρ.map_mul a b) }
  have hσ : Function.Injective σ := by
    intro a b he
    apply hi
    apply Units.ext
    exact congrArg Subtype.val he
  have hp2 : p ≠ 2 := by intro he; subst p; exact ho.not_two_dvd_nat (dvd_refl 2)
  have hc : IsCyclic A := Matrix.SL2.odd_pGroup_isCyclic_of_injective hA hp2 σ hσ
  refine ⟨hc,?_⟩
  have hd := card_dvd_of_injective σ hσ
  rw [Atlas.card_sl_two,hF] at hd
  have hqpos : 1 ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by decide))
  have hfactor : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    nlinarith [Nat.sub_add_cancel hqpos,
      Nat.sub_add_cancel (show 1 ≤ (2 ^ n) ^ 2 from Nat.one_le_iff_ne_zero.mpr
        (pow_ne_zero 2 (pow_ne_zero n (by decide))))]
  rw [hfactor] at hd
  have hcop2 : Nat.Coprime (Nat.card A) (2 ^ n) := by
    obtain ⟨k,hk⟩ := hA.exists_card_eq
    rw [hk]
    exact ((Nat.coprime_two_right.mpr ho).pow_left k).pow_right n
  exact hpcard.dvd_of_dvd_mul_left (hcop2.dvd_of_dvd_mul_left hd)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- The literal image of an odd prime subgroup of Y is cyclic of order
 dividing q+1, through the faithful multiplicity embedding of the actual
 quotient C/C_C(W/V₁). -/
theorem residual_subgroup_image_cyclic
    (hCG : C E ≤ E.G₁)
    (ι : ((C E) ⧸ actionCentralizer E (C E) hCG) →* GL (Fin 2) E.input.field.Carrier)
    (hι : Function.Injective ι)
    (hY : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (P : Subgroup G) (hP : IsPGroup p P) (hPR : P ≤ outsideResidual E)
    (hRY : outsideResidual E ≤ E.Y) (hne : P ≠ ⊥) :
    Nat.Coprime p (2 ^ E.input.field.degree - 1) ∧
      IsCyclic ((P.subgroupOf (C E)).map (quotientAction E (C E) hCG)) ∧
      Nat.card ((P.subgroupOf (C E)).map (quotientAction E (C E) hCG)) ∣
        2 ^ E.input.field.degree + 1 := by
  have hpd : p ∣ Nat.card P := hP.card_eq_or_dvd.resolve_left
    (fun he => hne (card_eq_one.mp he))
  have hpn : Nat.Coprime p (2 ^ E.input.field.degree - 1) :=
    hY.coprime_dvd_left (hpd.trans (card_dvd_of_le (hPR.trans hRY)))
  let α := quotientAction E (C E) hCG
  let A := (P.subgroupOf (C E)).map α
  let e := QuotientGroup.quotientKerEquivRange α
  let ρ : A →* GL (Fin 2) E.input.field.Carrier :=
    ι.comp (e.symm.toMonoidHom.comp (inclusion (map_le_range _ _)))
  have hi : Function.Injective ρ :=
    hι.comp (e.symm.injective.comp (inclusion_injective _))
  obtain ⟨hc,hd⟩ := cyclic_plane_image ho hpn E.input.field.card_eq
    ((hP.comap_subtype (K := C E)).map α) ρ hi
  exact ⟨hpn,hc,hd⟩

/-- Centralization is inherited from the residual's actual image, keeping
 the same quotient action and the same X₁. -/
theorem residual_subgroup_image_centralizes_X₁
    (hCG : C E ≤ E.G₁)
    (hab : IsMulCommutative (quotientAction E (C E) hCG).range)
    (P : Subgroup G) (hPR : P ≤ outsideResidual E) :
    (P.subgroupOf (C E)).map (quotientAction E (C E) hCG) ≤
      centralizer (((X₁ E).subgroupOf (C E)).map (quotientAction E (C E) hCG) :
        Set (MulAut (E.W ⧸ E.V₁.subgroupOf E.W))) :=
  (map_mono (f := quotientAction E (C E) hCG)
    (comap_mono (f := (C E).subtype) hPR)).trans (residual_image_centralizes_X₁ E hCG hab)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
