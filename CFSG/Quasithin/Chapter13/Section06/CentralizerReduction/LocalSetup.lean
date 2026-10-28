module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Preliminaries
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.ModuleMarking
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Centralizer reductions from the earlier local setup

The normalizer-uniqueness argument in 13.6.3 uses the earlier assertion that
an outside local subgroup centralizes Z = Ω₁(Z(T)). If C_Z(L) were nontrivial,
its normalizer would lie in the unique maximal two-local overgroup of LT,
contradicting that outside subgroup. A normal subgroup of a finite two-group
meets its central involutions, so this also gives C_T(L) = 1 when T normalizes L.

These are deductions from the explicit earlier 13.3.2 and 13.3.5 inputs;
they do not postulate either centralizer conclusion. The marked binary-module
construction and the remaining local setup are assembled in extensions.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.3,
printed p.926, and its use in the S₆ branch on p.927.
-/

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction

open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- The uniqueness step in 13.6.3(2), with the outside centralizing
subgroup supplied by the genuine earlier source results. -/
public theorem centralizer_omega_eq_bot_of_earlier_source (T L M H : Subgroup G) (hT : IsPGroup 2 T)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hout : ¬ H ≤ M) (hH : H ≤ centralizer (omegaOneCenterAmbient T : Set G)) :
    omegaOneCenterAmbient T ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hne
  let A := omegaOneCenterAmbient T ⊓ centralizer (L : Set G)
  have hAT : A ≤ T := fun x hx => ((mem_omegaOneCenterAmbient_iff T x).mp hx.1).1
  have hLC : L ≤ centralizer (A : Set G) := by
    intro l hl
    exact mem_centralizer_iff.mpr fun a ha => (mem_centralizer_iff.mp ha.2 l hl).symm
  have hTC : T ≤ centralizer (A : Set G) := by
    intro t ht
    exact mem_centralizer_iff.mpr fun a ha =>
      (((mem_omegaOneCenterAmbient_iff T a).mp ha.1).2.2 t ht).symm
  have hN := normalizer_le_of_unique_maximalTwoLocal hunique
    (hT.to_le hAT) hne ((sup_le hLC hTC).trans (Subgroup.centralizer_le_normalizer _))
  exact hout ((hH.trans (centralizer_le inf_le_left)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN))


/-- The C_T(L) = 1 consequence used later in the S₆ branch. Normality
is relative to T, obtained from its actual normalization of L. -/
public theorem centralizer_T_eq_bot_of_omega (T L : Subgroup G) (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G))
    (hZ : omegaOneCenterAmbient T ⊓ centralizer (L : Set G) = ⊥) :
    T ⊓ centralizer (L : Set G) = ⊥ := by
  let D := (centralizer (L : Set G)).subgroupOf T
  let : D.Normal :=
    (inferInstance : ((centralizer (L : Set G)).subgroupOf
      (normalizer (L : Set G))).Normal).comap (inclusion hTL)
  have hD : D = ⊥ := by
    by_contra hne
    let : Fact (IsPGroup 2 T) := ⟨hT⟩
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨A, _, hAD, hcard, hAC⟩ :=
      exists_central_subgroup_card_eq_prime_in_normal (p := 2) D
        ((nontrivial_iff_ne_bot D).mpr hne)
    have hAbot : A = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hx2 : x ^ 2 = 1 := by
        have he : (⟨x, hx⟩ : A) ^ 2 = 1 := by
          rw [← hcard]
          exact pow_card_eq_one'
        exact congrArg Subtype.val he
      have hxZ : (x : G) ∈ omegaOneCenterAmbient T :=
        (mem_omegaOneCenterAmbient_iff T x).mpr ⟨x.property,
          congrArg Subtype.val hx2, fun t ht =>
            congrArg Subtype.val (mem_center_iff.mp (hAC hx) ⟨t, ht⟩)⟩
      have hh : (x : G) ∈ (⊥ : Subgroup G) := hZ ▸ ⟨hxZ, hAD hx⟩
      exact Subtype.ext (show (x : G) = 1 from hh)
    simp [hAbot] at hcard
  apply eq_bot_iff.mpr
  intro x hx
  have hd : (⟨x, hx.1⟩ : T) ∈ D := hx.2
  rw [hD] at hd
  exact congrArg Subtype.val (show (⟨x, hx.1⟩ : T) = 1 from hd)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
