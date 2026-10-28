module

public import Theory.SpecificGroups.GL2.HomocyclicCentralizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive.PrimaryNormalizers
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FittingActions.HigherHomocyclic

/-!
# Normalizers on the full homocyclic primary core

The actual conjugation action on a homocyclic prime core has kernel F(B).
Its reduction modulo p has the same kernel: an element in the reduction kernel
fixes omega, so the faithful omega--Frattini action places it in F(B).
Thus both images are the original SL₂(5) quotient. The scalar-centralizer
calculation over Z/p^a and the two-group Out(SL₂(5)) make the full normalizer
quotient nilpotent. No exponent-one assumption or splitting is used.

Source: Aschbacher--Smith A.3.6(4), pp.43--45, and 11.4.3, p.778.
-/

public noncomputable section
open Subgroup Matrix HomocyclicCentralizer
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive

theorem primePower_normalizer_nilpotent {p a : ℕ} [Fact p.Prime] (ha : 1 ≤ a)
    (U : Subgroup (GL (Fin 2) (ZMod (p ^ a))))
    (e : U ≃* SL(2, ZMod 5))
    (hn : ¬ IsMulCommutative (U.map (GeneralLinearGroup.map
      (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt ha)) (ZMod p))))) :
    Group.IsNilpotent (Subgroup.NormalizerOuterQuotient.Quotient U) := by
  apply Subgroup.NormalizerOuterQuotient.nilpotent_of_centralizer_le_center U
  · exact centralizer_le_center_of_noncommutative_reduction _
      (unit_of_primePower_reduction_ne_zero ha) U hn
  · exact CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive.slFive_outer_two.of_equiv
      (MulAut.outerCongr e).symm

open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open scoped IsMulCommutative

private theorem omegaAction_one_of_fixes_torsion
    {B : Type*} [Group B] {p : ℕ} [IsMulCommutative (pCore p B)]
    (b : B) (hb : ∀ x : pCore p B, x ^ p = 1 → MulAut.conjNormal b x = x) :
    RadicalActions.omegaFrattiniAction p B b = 1 := by
  have hw : RadicalActions.omegaCoreAction p B b = 1 := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y, hy, he⟩ := x.property
    have hyp : y ^ p = 1 := by
      rw [OmegaAction.omega_eq_pow_ker] at hy
      change y ^ (p ^ 1) = 1 at hy
      simpa only [pow_one] using hy
    apply Subtype.ext
    change b * (x : B) * b⁻¹ = (x : B)
    rw [← he]
    exact congrArg Subtype.val (hb y hyp)
  change quotientAut (frattini (RadicalActions.omegaCore p B))
    (RadicalActions.omegaCoreAction p B b) = 1
  rw [hw, map_one]

/-- Full homocyclic coordinates, including the centralizer needed for mixed primes. -/
theorem homocyclic_primary_coordinates
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (h : A36Nilpotent B) (hc : A36Common B) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup B))
    (hs : LocalModels.HomocyclicTwo p (pCore p B)) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ f : MulAut (pCore p B) →* GL (Fin 2) (ZMod (p ^ a)),
      Function.Injective f ∧
      (f.comp (MulAut.conjNormal : B →* MulAut (pCore p B))).ker = fittingSubgroup B ∧
      centralizer ((f.comp (MulAut.conjNormal : B →* MulAut (pCore p B))).range :
        Set (GL (Fin 2) (ZMod (p ^ a)))) ≤ center (GL (Fin 2) (ZMod (p ^ a))) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hs
  let : IsMulCommutative (pCore p B) :=
    ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  let f := (homocyclicAutEquiv e).toMonoidHom
  let ρ : B →* MulAut (pCore p B) := MulAut.conjNormal
  let r := ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt ha)) (ZMod p)
  let τ := (GeneralLinearGroup.map r).comp (f.comp ρ)
  have hρ : ρ = FittingActions.coreAction p B := by
    ext b x
    rfl
  have hk : ρ.ker = fittingSubgroup B := by
    rw [hρ]
    exact FittingActions.abelian_coreAction_ker_eq_fitting h hc hd
  have hτ : τ.ker = fittingSubgroup B := by
    apply le_antisymm
    · intro b hb
      rw [← omegaAction_kernel h hd]
      apply omegaAction_one_of_fixes_torsion
      intro x hx
      exact homocyclic_fixes_torsion_of_reduction_one ha e (ρ b) hb x hx
    · intro b hb
      change GeneralLinearGroup.map r (f (ρ b)) = 1
      have hb' : ρ b = 1 := show b ∈ ρ.ker from hk.symm ▸ hb
      rw [hb', map_one, map_one]
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by
    intro he
    have hp := (h.2.2.2 p Fact.out (h.1.symm ▸ hd)).1
    norm_num [he] at hp)
  obtain ⟨E, _⟩ := CenterFrattiniSource.nilpotent_exists_inverting_quotient h hp hd
  let Eτ : τ.range ≃* SL(2, ZMod 5) :=
    (QuotientGroup.quotientKerEquivRange τ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hτ.trans h.1.symm)).trans E)
  have hn : ¬ IsMulCommutative τ.range := by
    let : Group.IsPerfect τ.range :=
      Group.IsPerfect.ofSurjective (f := τ.rangeRestrict) τ.rangeRestrict_surjective
    let : Nontrivial SL(2, ZMod 5) := ⟨⟨1, -1, by
      intro he
      have hh := congrArg (fun g : SL(2, ZMod 5) => g 0 0) he
      exact (by decide : (1 : ZMod 5) ≠ -1) hh⟩⟩
    let : Nontrivial τ.range := Eτ.symm.injective.nontrivial
    exact Group.IsPerfect.not_isMulCommutative τ.range
  refine ⟨a, ha, f, (homocyclicAutEquiv e).injective, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective ρ f (homocyclicAutEquiv e).injective]
    exact hk
  · apply centralizer_le_center_of_noncommutative_reduction r
      (unit_of_primePower_reduction_ne_zero ha)
    rw [← MonoidHom.range_comp]
    exact hn

/-- The full homocyclic prime core, with arbitrary positive exponent. -/
theorem homocyclic_primary_normalizer_nilpotent
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (h : A36Nilpotent B) (hc : A36Common B) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup B))
    (hs : LocalModels.HomocyclicTwo p (pCore p B)) :
    Group.IsNilpotent (NormalizerOuterQuotient.Quotient
      (CharacteristicOuterRestriction.innerActionImage (pCore p B))) := by
  obtain ⟨a, ha, f, hf, hk, hcentral⟩ := homocyclic_primary_coordinates h hc hd hs
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by
    intro he
    have hp := (h.2.2.2 p Fact.out (h.1.symm ▸ hd)).1
    norm_num [he] at hp)
  obtain ⟨E, _⟩ := CenterFrattiniSource.nilpotent_exists_inverting_quotient h hp hd
  let ρ := f.comp (MulAut.conjNormal : B →* MulAut (pCore p B))
  let Eρ : ρ.range ≃* SL(2, ZMod 5) :=
    (QuotientGroup.quotientKerEquivRange ρ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hk.trans h.1.symm)).trans E)
  apply NormalizerOuterQuotient.nilpotent_of_map f _
    (by rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]; exact bot_le)
  change Group.IsNilpotent (NormalizerOuterQuotient.Quotient
    (((MulAut.conjNormal : B →* MulAut (pCore p B)).range).map f))
  rw [← MonoidHom.range_comp]
  exact NormalizerOuterQuotient.nilpotent_of_centralizer_le_center ρ.range hcentral
    (slFive_outer_two.of_equiv (MulAut.outerCongr Eρ).symm)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive
