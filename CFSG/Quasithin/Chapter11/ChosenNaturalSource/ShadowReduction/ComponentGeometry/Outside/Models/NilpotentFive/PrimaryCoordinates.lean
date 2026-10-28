module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive.HomocyclicNormalizers

/-!
# Compatible primary coordinates for the original Fitting action

Each primary core supplies a two-dimensional matrix action with kernel F(B)
on the original group B and scalar centralizer. For an extraspecial core the
Frattini quotient kills exactly its inner automorphisms. For a homocyclic core
the full automorphism coordinates are faithful and retain its entire exponent.
The finite modulus permits both branches to be assembled in one product.

Every field of `PrimaryCoordinates` is constructed from A.3.6 and the proved
primary actions; the record is an internal construction, not a source hypothesis.
Source: Aschbacher--Smith A.3.6(4), pp.43--45; 11.4.3, p.778.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive

/-- Prime coordinates retain the full homocyclic core and kill exactly inner
extraspecial automorphisms. The kernels refer to the original B-action. -/
structure PrimaryCoordinates (B : Type*) [Group B] (p : ℕ) where
  modulus : ℕ
  positive : 0 < modulus
  action : MulAut (pCore p B) →* GL (Fin 2) (ZMod modulus)
  inner_kernel : action.ker ≤ MulAut.innerSubgroup (pCore p B)
  action_kernel : (action.comp (MulAut.conjNormal : B →* MulAut (pCore p B))).ker =
    fittingSubgroup B
  centralizer : centralizer
    ((action.comp (MulAut.conjNormal : B →* MulAut (pCore p B))).range :
      Set (GL (Fin 2) (ZMod modulus))) ≤ center (GL (Fin 2) (ZMod modulus))

theorem exists_primaryCoordinates
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (h : A36Nilpotent B) (hc : A36Common B) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup B)) : Nonempty (PrimaryCoordinates B p) := by
  rcases (h.2.2.2 p Fact.out (h.1.symm ▸ hd)).2 with hs | hs
  · let : IsExtraspecial p (pCore p B) := hs.1.1
    let E := FittingActions.coreOmegaEquiv (Or.inr h) hd
    let := (RadicalActions.Nilpotent.frattini_shape h hd).1
    obtain ⟨l, hl⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
      (RadicalActions.omegaCore p B ⧸ frattini (RadicalActions.omegaCore p B))
      (RadicalActions.Nilpotent.frattini_shape h hd).2.le
    let g := l.comp (MulAut.congr E).toMonoidHom
    have hg : Function.Injective g := hl.comp (MulAut.congr E).injective
    let f := g.comp (quotientAut (frattini (pCore p B)))
    have hf : f.ker ≤ MulAut.innerSubgroup (pCore p B) := by
      rw [MonoidHom.ker_comp_of_injective _ _ hg]
      exact (IsExtraspecial.quotientAut_frattini_ker_eq_range_conj (p := p)).le
    have he : f.comp (MulAut.conjNormal : B →* MulAut (pCore p B)) =
        g.comp (FittingActions.coreFrattiniAction p B) := by
      apply MonoidHom.ext
      intro b
      change g (quotientAut (frattini (pCore p B)) (MulAut.conjNormal b)) =
        g (quotientAut (frattini (pCore p B))
          (MulAut.characteristic (pCore p B) (MulAut.conj b)))
      rw [characteristic_conj_eq_conjNormal]
    have hk : (f.comp (MulAut.conjNormal : B →* MulAut (pCore p B))).ker = fittingSubgroup B := by
      rw [he, MonoidHom.ker_comp_of_injective _ _ hg,
        FittingActions.core_action_ker_eq_omega (Or.inr h) hd, omegaAction_kernel h hd]
    have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by
      intro he
      have hp := (h.2.2.2 p Fact.out (h.1.symm ▸ hd)).1
      norm_num [he] at hp)
    obtain ⟨EQ, _⟩ := CenterFrattiniSource.nilpotent_exists_inverting_quotient h hp hd
    let ρ := f.comp (MulAut.conjNormal : B →* MulAut (pCore p B))
    let ER : ρ.range ≃* SL(2, ZMod 5) :=
      (QuotientGroup.quotientKerEquivRange ρ).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq (hk.trans h.1.symm)).trans EQ)
    have hn : ¬ IsMulCommutative ρ.range := by
      let : Group.IsPerfect ρ.range :=
        Group.IsPerfect.ofSurjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
      let : Nontrivial SL(2, ZMod 5) := ⟨⟨1, -1, by
        intro he
        have hh := congrArg (fun g : SL(2, ZMod 5) => g 0 0) he
        exact (by decide : (1 : ZMod 5) ≠ -1) hh⟩⟩
      let : Nontrivial ρ.range := ER.symm.injective.nontrivial
      exact Group.IsPerfect.not_isMulCommutative ρ.range
    have hcentral : centralizer (ρ.range : Set (GL (Fin 2) (ZMod p))) ≤
        center (GL (Fin 2) (ZMod p)) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact Matrix.GeneralLinearGroup.centralizer_le_scalar_of_noncommutative ρ.range hn
    refine ⟨{ modulus := p
              positive := (Fact.out : p.Prime).pos
              action := f
              inner_kernel := ?_
              action_kernel := ?_
              centralizer := ?_ }⟩
    · exact hf
    · exact hk
    · exact hcentral
  · obtain ⟨a, ha, f, hf, hk, hcentral⟩ := homocyclic_primary_coordinates h hc hd hs
    exact ⟨{ modulus := p ^ a
             positive := pow_pos (Fact.out : p.Prime).pos a
             action := f
             inner_kernel := by rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]; exact bot_le
             action_kernel := hk
             centralizer := hcentral }⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive
