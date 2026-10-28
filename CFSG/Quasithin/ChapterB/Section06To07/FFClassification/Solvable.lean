module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SourceTheorems
public import CFSG.Quasithin.ChapterB.Section06To07.OffenderGeneration
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Solvable FF factors in a minimal parabolic

The proved solvable classification B.1.8 constructs the internal natural
SL₂(2) factors. The normal closure of a factor contains an involution,
so B.6.8 forces it to contain the two-residual. Every factor's cubic core
lies in that residual. Coordinate independence then puts every factor
in one ambient orbit, and H = J(H,V)T makes this the original Sylow orbit.
The same cubic-core argument proves that each stable offender family
generates all factors; no saturation equality is assumed.

Source: Aschbacher–Smith, B.6.9, printed pp.115–116 (1 March 2004).
The final theorem constructs its witness from the faithful solvable
FF action; all maps and natural intertwiners remain those of B.1.8.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

namespace SolvableFFFactors

theorem factorOddCore_le_residual (d : SolvableFFFactors ρ) (i : Fin d.count) :
    d.factorOddCore i ≤ pResidual 2 G := by
  have hp : IsPGroup 3 (d.factorOddCore i) :=
    IsPGroup.of_card (n := 1) (by simpa using d.factorOddCore_card i)
  intro x hx
  have ho := hp.orderOf_coprime (by decide : Nat.Coprime 3 2)
    (⟨x, hx⟩ : d.factorOddCore i)
  rw [← Subgroup.orderOf_coe] at ho
  exact mem_pResidual_of_orderOf_coprime ho.symm

/-- Minimal-parabolic uniqueness forces one orbit on the actual direct factors. -/
theorem factor_transitive (d : SolvableFFFactors ρ)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hcore : pCore 2 G = ⊥)
    (hgen : offenderSubgroup ρ ⊔ (T : Subgroup G) = ⊤)
    (i j : Fin d.count) :
    ∃ t : T, (d.factor i).map (MulAut.conj (t : G)).toMonoidHom = d.factor j := by
  classical
  let N := conjugateSpanBy (d.factor i) ⊤
  have hn : N.Normal := normalizer_eq_top_iff.mp
    (top_unique (le_normalizer_conjugateSpanBy (d.factor i) ⊤))
  let := hn
  let S : Sylow 2 (d.factor i) := Classical.choice inferInstance
  have hr := (minimalParabolic_normal_contains_two_supplements T hP hcore N
    (d.factorSylow i S) (S.isPGroup'.map (d.factor i).subtype)
    (d.factorSylow_ne_bot i S)
    ((d.factorSylow_le i S).trans (le_conjugateSpanBy _ _))).1
  let I : Set (Fin d.count) := {k | ∃ g : G,
    (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor k}
  have hnI : N ≤ ⨆ k ∈ I, d.factor k := by
    rw [show N = conjugateSpanBy (d.factor i) ⊤ from rfl, conjugateSpanBy_eq_iSup_conj]
    refine iSup_le fun g => ?_
    obtain ⟨k, hk⟩ := d.exists_factor_map_conj (g : G) i
    rw [hk]
    exact le_iSup_of_le k (le_iSup_of_le ⟨(g : G), hk⟩ le_rfl)
  obtain ⟨g, hg⟩ := d.mem_of_factorOddCore_le_subproduct I
    ((d.factorOddCore_le_residual j).trans (hr.trans hnI))
  let := offenderSubgroup_normal ρ
  obtain ⟨y, hy, t, ht, rfl⟩ := mem_sup_of_normal_left.mp
    (show g ∈ offenderSubgroup ρ ⊔ (T : Subgroup G) by rw [hgen]; trivial)
  obtain ⟨k, hk⟩ := d.exists_factor_map_conj t i
  have hyk : y ∈ normalizer (d.factor k : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (d.factor_le_offenderSubgroup k)).mp
      (d.factor_normal_in_offenderSubgroup k) hy
  have hc : (MulAut.conj (y * t)).toMonoidHom =
      (MulAut.conj y).toMonoidHom.comp (MulAut.conj t).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hyke : (d.factor k).map (MulAut.conj y).toMonoidHom = d.factor k :=
    mem_normalizer_iff_map_conj_eq.mp hyk
  rw [hc, ← map_map, hk, hyke] at hg
  exact ⟨⟨t, ht⟩, hk.trans hg⟩

end SolvableFFFactors

variable [FiniteDimensional (ZMod 2) V]
namespace ThreeConjugates.SolvableFFStructure

/-- Every stable family selects every factor in a minimal parabolic. -/
theorem stable_generated_eq (d : ThreeConjugates.SolvableFFStructure ρ)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hcore : pCore 2 G = ⊥) (hfaith : Function.Injective ρ)
    {P : Set (Subgroup G)} (hst : IsStable ρ P) :
    generatedBy P ⊤ = offenderSubgroup ρ := by
  have hr := (stable_offender_generation T hP ρ hst hcore).1
  have he := d.toSolvableFFFactors.stable_generatedBy_eq hfaith d.ratio_one hst
  have hall (i : Fin d.count) : i ∈ d.toSolvableFFFactors.stableFactorSet P :=
    d.toSolvableFFFactors.mem_of_factorOddCore_le_subproduct _
      ((d.toSolvableFFFactors.factorOddCore_le_residual i).trans (hr.trans he.le))
  rw [he, ← d.toSolvableFFFactors.iSup_factor]
  exact le_antisymm (iSup_le fun i => iSup_le fun _ => le_iSup d.factor i)
    (iSup_le fun i => le_iSup_of_le i (le_iSup_of_le (hall i) le_rfl))

end ThreeConjugates.SolvableFFStructure

/-- The solvable B.6.9 factor and stability conclusions from the original action. -/
theorem source_solvable_minimalParabolic_factors
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hff : IsFFModule ρ) :
    ∃ d : ThreeConjugates.SolvableFFStructure ρ,
      (∀ i j, ∃ t : T,
        (d.factor i).map (MulAut.conj (t : G)).toMonoidHom = d.factor j) ∧
      (∀ P, IsStable ρ P → generatedBy P ⊤ = offenderSubgroup ρ) ∧
      pResidual 2 G ≤ offenderSubgroup ρ ∧
      offenderSubgroup ρ ⊔ (T : Subgroup G) = ⊤ := by
  obtain ⟨d⟩ := solvableFFStructure_nonempty ρ hsolv hcore hfaith hff
  obtain ⟨hr, hg⟩ := offender_generation T hP ρ hff hcore
  exact ⟨d, d.toSolvableFFFactors.factor_transitive T hP hcore hg,
    fun P hst => d.stable_generated_eq T hP hcore hfaith hst, hr, hg⟩

end CFSG.Quasithin.ChapterB
