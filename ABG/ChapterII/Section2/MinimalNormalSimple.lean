module
public import FeitThompson.ChiefFactors.Core
public import FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.Subgroup.Simple
public import Theory.GroupTheory.CyclicSylowCenterNormalIntersection

/-!
# Minimal normal simplicity from a cyclic Sylow center

A nontrivial minimal normal subgroup N of a finite group with trivial odd
core is simple if the center of a Sylow two-subgroup of N is cyclic. The
minimal-normal API does not itself assert nontriviality, so this is retained
as a separate hypothesis.

The odd core of N is characteristic in N and hence normal in the ambient
group, so it is trivial. Every nontrivial normal subgroup of N therefore has
even order. Choose a minimal normal subgroup A inside N. Its image under any
automorphism intersects A nontrivially by the cyclic-Sylow-center intersection
theorem. Minimality and equal orders make that image equal A, so A is
characteristic in N and normal in the ambient group. Ambient minimality now
forces A=N, which proves simplicity.

This is the simplicity reduction for ABG Chapter II Section 2 Proposition 2,
article pp.15-16, `refs/latex/alperin-brauer-gorenstein-pages/page-016.tex` and
`page-017.tex`. It proves the source's conclusion directly through intersecting
normal subgroups, without constructing the full decomposition into simple
factors. The reusable intersection result lives in Theory; this adapter uses
the existing chief-factor minimality interface.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

/-- An odd-core-free minimal normal subgroup with cyclic Sylow center is simple. -/
public theorem minimal_normal_simple_of_cyclic_sylow_center
    (hcore : pPrimeCore 2 G = ⊥) (N : Subgroup G) [N.Normal]
    [IsMinimalNormal N] (hN : N ≠ ⊥)
    (S : Sylow 2 N) (hZ : IsCyclic (Subgroup.center S)) : IsSimpleGroup N := by
  classical
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  have hcoreN : pPrimeCore 2 N = ⊥ := by
    have hmap : (pPrimeCore 2 N).map N.subtype = ⊥ := by
      apply pPrimeCore_eq_bot_iff.mp hcore
      · infer_instance
      · rw [Subgroup.card_map_of_injective N.subtype_injective]
        exact pPrimeCore_coprime_card
    exact Subgroup.map_injective N.subtype_injective (by simpa using hmap)
  have heven (A : Subgroup N) (hA : A.Normal) (hne : A ≠ ⊥) : 2 ∣ Nat.card A := by
    by_contra h
    exact hne (pPrimeCore_eq_bot_iff.mp hcoreN A hA
      (Nat.prime_two.coprime_iff_not_dvd.mpr h))
  obtain ⟨A, hA, _, hAne, hminA⟩ := exists_minimal_normal_le
    (⊤ : Subgroup N) inferInstance (by exact top_ne_bot)
  let := hA
  have hchar : A.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro e
    have hmapnormal : (A.map e.toMonoidHom).Normal := hA.map e.toMonoidHom e.surjective
    let := hmapnormal
    have hcard : Nat.card (A.map e.toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective e.injective
    have hmeet := Subgroup.inf_ne_bot_of_even_of_cyclic_sylow_center S hZ A
      (A.map e.toMonoidHom) (heven A hA hAne) (hcard ▸ heven A hA hAne)
    have heq : A ⊓ A.map e.toMonoidHom = A :=
      hminA _ inferInstance inf_le_left hmeet
    have hle : A ≤ A.map e.toMonoidHom := inf_eq_left.mp heq
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  let := hchar
  have hmapnormal : (A.map N.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  let := hmapnormal
  have hmapN : A.map N.subtype = N :=
    IsMinimalNormal.eq_of_ne_bot N (A.map N.subtype) (Subgroup.map_subtype_le A)
      (by intro h; apply hAne; exact Subgroup.map_injective N.subtype_injective (by simpa using h))
  have hAtop : A = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [← MonoidHom.range_eq_map, N.range_subtype]
    exact hmapN
  refine ⟨fun B hB => ?_⟩
  by_cases hb : B = ⊥
  · exact Or.inl hb
  · exact Or.inr ((hminA B hB (hAtop ▸ le_top) hb).trans hAtop)

end ABG
