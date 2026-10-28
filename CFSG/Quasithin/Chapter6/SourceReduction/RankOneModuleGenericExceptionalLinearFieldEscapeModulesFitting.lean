module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourcePrime
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import CFSG.Quasithin.ChapterD.Section02.StarredConjugacy

/-!
# The Fitting-centralization step for a strict cubic offender

In a faithful binary action with trivial two-core, a minimum cubic offender
of ratio strictly below two centralizes the Fitting subgroup of every normal
three-prime subgroup. D.2.13 excludes all odd prime cores other than three
and five; the three-prime condition removes three, and strictness removes
five. No solvability or generalized-Fitting identity is assumed.

Finite minimum selection and Sylow conjugacy place such an offender in the
specified Sylow image. The Chapter 12 consumer uses the actual quotient
centralizer of O²(H)/O₂(O²(H)) and the G.2.2 action on the centralizer span.
The geometric strict cubic bound remains to be proved by this task.
Source: Aschbacher--Smith D.2.13(1--2) and 5.1.23, printed pp.184--185,645.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {X W : Type*} [Group X] [Finite X]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem starred_centralizes_three_prime_fitting
    (ρ : Representation (ZMod 2) X W) (hf : Function.Injective ρ)
    (hcore : pCore 2 X = ⊥) (hsmall : cubicRatio ρ < 2)
    (N : Subgroup X) [N.Normal] (h3 : Nat.Coprime 3 (Nat.card N))
    {A : Subgroup X} (hA : A ∈ ChapterD.QhatStar ρ) :
    (fittingSubgroup N).map N.subtype ≤ centralizer (A : Set X) := by
  have hmap (p : ℕ) : (pCore p N).map N.subtype ≤ pCore p X :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map N.subtype⟩
  rw [fitting_eq_sup_pCore, Subgroup.map_iSup]
  apply iSup_le
  intro p
  have hp : p.1.1.Prime := Fact.out
  by_cases hp2 : p.1.1 = 2
  · exact (hmap p.1.1).trans (by rw [hp2, hcore]; exact bot_le)
  by_cases hp3 : p.1.1 = 3
  · have htriv : pCore 3 N = ⊥ := by
      apply (eq_bot_iff_card _).mpr
      obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 3) (G := N)).exists_card_eq
      have hd := (pCore 3 N).card_subgroup_dvd_card
      rw [hk] at hd ⊢
      exact Nat.eq_one_of_dvd_coprimes (h3.pow_left k) dvd_rfl hd
    rw [hp3, htriv, Subgroup.map_bot]
    exact bot_le
  apply (hmap p.1.1).trans
  apply commutator_eq_bot_iff_le_centralizer.mp
  by_contra hm
  have hs := ChapterD.source_lemma_D_2_13_one_two ρ hf hA (hp.odd_of_ne_two hp2) hm
  have hp5 : p.1.1 = 5 := hs.1.resolve_left hp3
  exact (ne_of_lt hsmall) (hs.2 hp5).1


theorem exists_starred_in_sylow_centralizes_three_prime_fitting
    (ρ : Representation (ZMod 2) X W) (hf : Function.Injective ρ)
    (hcore : pCore 2 X = ⊥) (hsmall : cubicRatio ρ < 2)
    (N : Subgroup X) [N.Normal] (h3 : Nat.Coprime 3 (Nat.card N))
    (P : Sylow 2 X) :
    ∃ A : Subgroup X, A ≤ P ∧ A ∈ ChapterD.QhatStar ρ ∧
      (fittingSubgroup N).map N.subtype ≤ centralizer (A : Set X) := by
  obtain ⟨B, hB⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr hsmall.le
  let : IsElementaryAbelian 2 B := hB.1.2.1.2
  obtain ⟨S, hBS⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S P
  have hA := ChapterD.QhatStar.map_conj ρ hB g
  refine ⟨B.map (MulAut.conj g).toMonoidHom, ?_, hA,
    starred_centralizes_three_prime_fitting ρ hf hcore hsmall N h3 hA⟩
  rw [← hg]
  exact map_mono hBS

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
