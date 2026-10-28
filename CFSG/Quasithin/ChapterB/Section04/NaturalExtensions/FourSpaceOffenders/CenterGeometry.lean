module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.Reduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.ThreeCovers.Offenders
public import Theory.Representation.GeneralLinearNatural

/-!
# Common-center subgroups of the natural binary three-space

The full displacement group into a line is Klein four, by its displacement
isomorphism with Hom(W/P,P). Inclusion and equal orders show that an elementary
four-group is the full-center group precisely when all its nonidentity
natural displacement ranges are the same line. No four-space offender
conclusion is assumed.

Source: Aschbacher–Smith, B.4.8(2), printed p.91, combined manuscript
of 1 March 2004. This criterion is applied to the literal natural quotient
by `central_best_iff_fullCenter`.
-/

public section
open Subgroup Representation Representation.BinaryOffender BinaryLinearThree
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.FourSpaceOffenders

def centerGroup (P : Submodule (ZMod 2) BinaryLinearThree.Vector) :
    Subgroup BinaryLinearThree.Group where
  carrier := {g | ∀ v, W g v - v ∈ P}
  one_mem' := by intro v; simp
  mul_mem' {g h} hg hh := by
    intro v
    simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using
      P.add_mem (hg (W h v)) (hh v)
  inv_mem' {g} hg := by
    intro v
    have hm := P.neg_mem (hg (W g⁻¹ v))
    simpa only [W.self_inv_apply, neg_sub] using hm

theorem centerGroup_full (P : Submodule (ZMod 2) BinaryLinearThree.Vector)
    (hP : Module.finrank (ZMod 2) P = 1) :
    IsFullCenterGroup BinaryField.two 3 (centerGroup P) := ⟨P, hP, fun _ => Iff.rfl⟩

theorem fullCenter_elementary_rank {A : Subgroup BinaryLinearThree.Group}
    (hA : IsFullCenterGroup BinaryField.two 3 A) : IsElementaryTwo A ∧ rank A = 2 := by
  obtain ⟨e⟩ := fullCenter_klein A hA
  have hc : Nat.card A = 4 := by rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]; decide
  let _ : IsElementaryAbelian 2 (Multiplicative (Fin 2 → ZMod 2)) :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide) }
  have he : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  refine ⟨⟨?_, he⟩, ?_⟩
  · intro hb
    simp [hb] at hc
  · rw [rank, hc]; decide

theorem natural_involution_range_finrank (a : BinaryLinearThree.Group)
    (ha : orderOf a = 2) : Module.finrank (ZMod 2) (LinearMap.range (W a - LinearMap.id)) = 1 := by
  obtain ⟨he, _, _, hb⟩ := involution_actor_rank_and_fixedCodim W a ha
  have hp := fixedCodim_pos_of_faithful W (specialLinearNatural_injective 3) he.1
  have hd : Module.finrank (ZMod 2) BinaryLinearThree.Vector = 3 := Module.finrank_fin_fun _
  rw [hd] at hb
  rw [← fixedCodim_zpowers_eq_displacement_rank]
  omega

theorem fullCenter_iff_common_range (A : Subgroup BinaryLinearThree.Group) :
    IsFullCenterGroup BinaryField.two 3 A ↔
      IsElementaryTwo A ∧ rank A = 2 ∧
        ∃ P : Submodule (ZMod 2) BinaryLinearThree.Vector,
          Module.finrank (ZMod 2) P = 1 ∧
            ∀ a ∈ A, a ≠ 1 → LinearMap.range (W a - LinearMap.id) = P := by
  constructor
  · intro hA
    obtain ⟨he, hr⟩ := fullCenter_elementary_rank hA
    let _ : IsElementaryAbelian 2 A := he.2
    obtain ⟨P, hP, hmem⟩ := hA
    refine ⟨he, hr, P, hP, ?_⟩
    intro a ha hne
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, rfl⟩
      exact (hmem a).mp ha v
    · exact (natural_involution_range_finrank a
        (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hne)).trans hP.symm
  · rintro ⟨he, hr, P, hP, hRanges⟩
    have hle : A ≤ centerGroup P := by
      intro a ha v
      by_cases hne : a = 1
      · simp [hne]
      · rw [← hRanges a ha hne]
        exact ⟨v, rfl⟩
    have hc := he.card_eq_two_pow_rank
    have hcP := (fullCenter_elementary_rank (centerGroup_full P hP)).1.card_eq_two_pow_rank
    rw [hr] at hc
    rw [(fullCenter_elementary_rank (centerGroup_full P hP)).2] at hcP
    have heq : A = centerGroup P := eq_of_le_of_card_ge hle (by omega)
    exact heq ▸ centerGroup_full P hP
end CFSG.Quasithin.ChapterB.NaturalExtensions.FourSpaceOffenders
