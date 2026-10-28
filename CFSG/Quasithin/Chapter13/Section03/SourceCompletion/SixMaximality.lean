module

public import CFSG.Quasithin.Chapter13.Section01.RadicalQuotient
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup
public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Chains
public import CFSG.Quasithin.ChapterA.Section04.SourceChains.Applications

/-!
# The quasisimple upper component in the original A₆ maximality argument

A local component containing the original A₆ two-core section cannot have
nonquasisimple two-core quotient. The proved A.3.6 consequence would make
its quotient by the solvable radical PSL₂(p), with p > 3 prime. Removing
the solvable kernel preserves the A₆ section; Dickson's prime-field theorem
leaves only an A₅ numerator or the whole PSL₂(p), both impossible by order.

Consequently the original natural A₆ setup has a maximal faithful overgroup
with quasisimple two-core quotient and the actual Hypothesis 12.2.1. This
specialization discharges the 13.1.7 step in 13.3.2 for that overgroup. It
does not identify the upper component with the original L: the earlier
13.1.2(3) model classification is still needed for the existing rigidity
lemma. In particular, no maximality or normalizer bound for L is assumed
or asserted here.

Source: Aschbacher–Smith, 13.3.2(1–2,4), printed pp.884–885, using the
A.3.6/13.1.4(3) radical quotient. The actual consumer is the normal A₆
case of 13.5.15, whose exceptional quotient uses N_G(O₂(LT)) ≤ N_G(L).
-/

public section
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality

private theorem six_not_solvable : ¬ Group.IsSolvable (alternatingGroup (Fin 6)) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
  exact Group.IsPerfect.not_isSolvable _

/-- No subgroup of prime-field PSL₂(p), p > 3, has an A₆ quotient. This
also eliminates the smaller prime-field image in the quadratic-field
A.3.12 branch for the original local chain. -/
theorem prime_psl_no_six_section
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hlarge : 3 < p) (hF : Nat.card F = p)
    (U : Subgroup (PSL2MatrixGroup F)) (f : U →* alternatingGroup (Fin 6))
    (hf : Function.Surjective f) : False := by
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num
  by_cases hU : U = ⊤
  · subst U
    let f₀ : PSL2MatrixGroup F →* alternatingGroup (Fin 6) :=
      f.comp topEquiv.symm.toMonoidHom
    have hf₀ : Function.Surjective f₀ := hf.comp topEquiv.symm.surjective
    let : IsSimpleGroup (PSL2MatrixGroup F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let e := MulEquiv.ofBijective f₀
      ⟨f₀.injective_of_surjective_of_simple hf₀, hf₀⟩
    have hc : Nat.card (PSL2MatrixGroup F) = 360 :=
      (Nat.card_congr e.toEquiv).trans hcardA
    have he := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF.symm ▸ ho)
    rw [hc, hF] at he
    have hple : p ≤ 9 := by
      by_contra h
      have hp10 : 10 ≤ p := by omega
      have hs₀ : 100 ≤ p ^ 2 := by
        simpa only [pow_two] using Nat.mul_le_mul hp10 hp10
      have hs : 99 ≤ p ^ 2 - 1 := by omega
      have hm := Nat.mul_le_mul hp10 hs
      omega
    have hp : p.Prime := Fact.out
    interval_cases p <;> norm_num at *
  · obtain ⟨_, _, ⟨e⟩⟩ := Theory.PSL2.prime_nonsolvable_proper_is_alternating_five
      ho hF U hU (fun hs => by
        let := hs
        exact six_not_solvable (Group.isSolvable_of_surjective hf))
    have hcardU : Nat.card U = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hd := Subgroup.card_dvd_of_surjective f hf
    rw [hcardA, hcardU] at hd
    norm_num at hd

/-- An actual local component containing an A₆ two-core section has quasisimple
two-core quotient. This discharges the nonquasisimple-overgroup branch in the
original 13.3.2 maximality argument for the normal A₆ consumer. -/
theorem local_overgroup_quasisimple_of_six
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L I : Subgroup G} (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hLI : L ≤ I)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    IsQuasisimple (I ⧸ pCore 2 I) := by
  classical
  by_contra hn
  obtain ⟨p, hp, hlarge, F, _, _, hF, ⟨eI⟩⟩ :=
    Section01.nonquasisimple_local_radical_quotient hG T hI hn
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let m : Group.SolvableKernelModel I (PSL2MatrixGroup F) := {
    kernel := solvableRadical I
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := eI }
  let U := L.subgroupOf I
  let eL : U ≃* L := subgroupOfEquivOfLe hLI
  let f : U →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp eL.toMonoidHom)
  have hf : Function.Surjective f :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eL.surjective)
  obtain ⟨W, g, hg⟩ := m.simple_section six_not_solvable U f hf
  exact prime_psl_no_six_section ho hlarge hF W g hg

open Section08.SourceCompletion

/-- Apply the preceding source reduction to every overgroup of the original
marked A₆ block, retaining its actual quotient by O₂(L). -/
theorem NaturalSetup.local_overgroup_quasisimple
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {I : Subgroup G} (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hLI : L ≤ I) :
    IsQuasisimple (I ⧸ pCore 2 I) :=
  local_overgroup_quasisimple_of_six d.counterexample.qtke T hI hLI e

/-- The actual upper component to which 13.1.2 and its Chapter 12 source
classification apply. Its faithfulness and quasisimplicity are proved from
the original natural A₆ setup; they are not additional hypotheses. -/
theorem NaturalSetup.exists_maximal_quasisimple_overgroup
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    ∃ I : Subgroup G, L ≤ I ∧
      Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T I ∧
      (T : Subgroup G) ≤ normalizer (I : Set G) := by
  have hL := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
    d.counterexample.local_component
  obtain ⟨I, hI, hLI⟩ := Chapter1.exists_mem_LStar_ge hL.1
  have hTI := Chapter1.Section02.Adequate.local_chain_normalizes
    hL.1 hI.1 hLI d.normalizes_L
  have hnormalizers : (T : Subgroup G) ⊓ normalizer (L : Set G) =
      (T : Subgroup G) ⊓ normalizer (I : Set G) := by
    rw [inf_of_le_left d.normalizes_L, inf_of_le_left hTI]
  have hf := (Chapter1.Section02.Adequate.faithful_chain_of_A410_of_normalizer_eq
    T (d.counterexample.qtke.evenCharacteristic T)
    ChapterA.Section04.SourceChains.adequate_source d.counterexample.local_component
    hI.1 hLI hnormalizers).2
  refine ⟨I, hLI, ⟨d.counterexample.qtke, ⟨hI, ?_⟩,
    NaturalSetup.local_overgroup_quasisimple d e hI.1 hLI⟩, hTI⟩
  exact ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T I).mp hf).2

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality
