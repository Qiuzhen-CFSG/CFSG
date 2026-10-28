module

public import Theory.GroupTheory.ConjugatePairCentralizerBound

/-!
# The treatment of Â₆ on a six-dimensional module: terminal deduction

The target is Theorem 12.7.1: under Hypothesis 12.2.3, if the faithful
quotient `L/C_L(V)` is the triple cover of A₆, then `G` is isomorphic to
M₂₄ or He. The local setup and the two identification branches are still
required; no classification theorem is asserted here.

This module proves the group-theoretic deduction in Lemma 12.7.22(5) from
the two vector orbits and the actual element-centralizer core containments.
It then proves the final contradiction: a subgroup `B` of order sixteen
and a centralizer index at most four force a nonidentity fixed point for
the second conjugate, making the generated pair a two-group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §12.7, printed pp.838–849 (PDF pp.855–866).
The last paragraph is on p.849, beyond the nominal section page range.
`conjBy g` denotes left conjugation `g * x * g⁻¹` throughout.
-/

open Subgroup

namespace CFSG.Quasithin.Chapter12.Section07
variable {G : Type*} [Group G]

/-- The deduction in 12.7.22(5) once `V ≤ O₂(C_G(v))` is known for every
nonidentity `v ∈ V`. The literal ambient images of the local cores are used. -/
public theorem conjugate_join_isTwoGroup_of_local_cores (V : Subgroup G)
    (hV : IsPGroup 2 V)
    (hcore : ∀ v ∈ V, v ≠ 1 → V ≤ (centralizer ({v} : Set G)).pCoreIn 2)
    (g : G) (hfix : V ⊓ centralizer (V.conjBy g : Set G) ≠ ⊥) :
    IsPGroup 2 (V ⊔ V.conjBy g : Subgroup G) :=
  isPGroup_sup_of_fixed_point_core (hV.map (MulAut.conj g).toMonoidHom) hcore hfix

/-- The source two-orbit version of 12.7.22(5). Lemma 12.7.4(1) supplies
the orbits, 12.7.8 supplies the core containment at `t`, and 12.7.21
supplies the containment at `z`. Each conjugator normalizes the same `V`. -/
public theorem conjugate_join_isTwoGroup_of_two_orbits (V : Subgroup G)
    (hV : IsPGroup 2 V) (z t : G)
    (horbits : ∀ v ∈ V, v ≠ 1 → ∃ l ∈ normalizer (V : Set G),
      MulAut.conj l v = z ∨ MulAut.conj l v = t)
    (hz : V ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (ht : V ≤ (centralizer ({t} : Set G)).pCoreIn 2)
    (g : G) (hfix : V ⊓ centralizer (V.conjBy g : Set G) ≠ ⊥) :
    IsPGroup 2 (V ⊔ V.conjBy g : Subgroup G) := by
  obtain ⟨v, hv⟩ := ne_bot_iff_exists_ne_one.mp hfix
  obtain ⟨l, hl, hrep⟩ := horbits v v.property.1 (fun h => hv (Subtype.ext h))
  have hcore : V ≤ (centralizer ({MulAut.conj l (v : G)} : Set G)).pCoreIn 2 := by
    rcases hrep with h | h
    · rwa [h]
    · rwa [h]
  have hc : MulAut.conj l (v : G) ∈ centralizer ((V.conjBy g).conjBy l : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    change (MulAut.conj l) a * (MulAut.conj l) (v : G) =
      (MulAut.conj l) (v : G) * (MulAut.conj l) a
    simpa only [map_mul] using
      congrArg (MulAut.conj l) (mem_centralizer_iff.mp v.property.2 a ha)
  have hp := isPGroup_sup_of_elementCentralizer_core
    ((hV.map (MulAut.conj g).toMonoidHom).map (MulAut.conj l).toMonoidHom) hcore hc
  have hm : (V ⊔ V.conjBy g).map (MulAut.conj l).toMonoidHom =
      V ⊔ (V.conjBy g).conjBy l := by
    rw [Subgroup.map_sup]
    exact congrArg (fun W : Subgroup G => W ⊔ (V.conjBy g).conjBy l)
      (mem_normalizer_iff_map_conj_eq.mp hl)
  change IsPGroup 2 (V ⊔ (V.conjBy g).conjBy l : Subgroup G) at hp
  rw [← hm] at hp
  exact hp.of_equiv ((MulAut.conj l).subgroupMap (V ⊔ V.conjBy g)).symm

/-- The final fixed-point contradiction on p.849, with
`A = V.conjBy g`, `B = V₂.conjBy g`, and `I = A ⊔ A.conjBy k`.
Lemma 12.7.22(5) is the explicit earlier input `hpair`; the final local
construction must still supply `B`, `D`, `k`, their bounds, and `hnot`. -/
public theorem terminal_contradiction [Finite G] (V : Subgroup G)
    (hpair : ∀ a : G, V ⊓ centralizer (V.conjBy a : Set G) ≠ ⊥ →
      IsPGroup 2 (V ⊔ V.conjBy a : Subgroup G))
    (g k : G) (B D : Subgroup G) (hBA : B ≤ V.conjBy g) (hBD : B ≤ D)
    (hBcard : Nat.card B = 16)
    (hindex : (centralizer ((V.conjBy g).conjBy k : Set G)).relIndex D ≤ 4)
    (hnot : ¬ IsPGroup 2 (V.conjBy g ⊔ (V.conjBy g).conjBy k : Subgroup G)) : False := by
  apply hnot
  apply isPGroup_conjugate_pair_of_relIndex_lt_card V hpair g k B D hBA hBD
  omega

/-- The final contradiction with 12.7.22(5) discharged from the actual
two orbit representatives and their local cores. This remains a conditional
source reduction: it does not construct the terminal local configuration. -/
public theorem terminal_contradiction_of_two_orbit_cores [Finite G] (V : Subgroup G)
    (hV : IsPGroup 2 V) (z t : G)
    (horbits : ∀ v ∈ V, v ≠ 1 → ∃ l ∈ normalizer (V : Set G),
      MulAut.conj l v = z ∨ MulAut.conj l v = t)
    (hz : V ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (ht : V ≤ (centralizer ({t} : Set G)).pCoreIn 2)
    (g k : G) (B D : Subgroup G) (hBA : B ≤ V.conjBy g) (hBD : B ≤ D)
    (hBcard : Nat.card B = 16)
    (hindex : (centralizer ((V.conjBy g).conjBy k : Set G)).relIndex D ≤ 4)
    (hnot : ¬ IsPGroup 2 (V.conjBy g ⊔ (V.conjBy g).conjBy k : Subgroup G)) : False :=
  terminal_contradiction V (conjugate_join_isTwoGroup_of_two_orbits V hV z t horbits hz ht)
    g k B D hBA hBD hBcard hindex hnot
end CFSG.Quasithin.Chapter12.Section07
