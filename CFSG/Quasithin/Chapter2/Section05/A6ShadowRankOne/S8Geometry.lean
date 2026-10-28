module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.Selection

/-!
# Transporting the C₂ × S₈ geometry to the exceptional A₈ branch

An actual isomorphism from a subgroup I to C₂ × S₈ transports its arbitrary
Sylow subgroup and the two block overgroups. Their characteristic-two condition
is intrinsic, so the transported groups lie in Chapter 1's genuine family He.
The existing selection argument then constructs Γe0 membership from the β
and half-Sylow inputs.

The standard maximality and core-centralizer calculations are proved in the
imported geometry. The unconditional transport and selection theorems below
discharge these premises; the earlier conditional interfaces are retained.
Source: Aschbacher–Smith, Lemma 2.5.26, printed p.569.
-/

public section
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne

open Subgroup
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

variable {G : Type*} [Group G] [Finite G]

/-- The Sylow order in the actual subgroup supplied by the exceptional branch. -/
theorem s8_sylow_card (I : Subgroup G) (e : I ≃* X) (T : Sylow 2 I) :
    Nat.card T = 256 := by
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let ep : T ≃* P := e.subgroupMap (T : Subgroup I)
  rw [Nat.card_congr ep.toEquiv]
  exact card_sylow P

/-- The Sylow order is unchanged when viewed in the original ambient group. -/
theorem s8_sylow_map_card (I : Subgroup G) (e : I ≃* X) (T : Sylow 2 I) :
    Nat.card ((T : Subgroup I).map I.subtype) = 256 := by
  rw [← Nat.card_congr ((T : Subgroup I).equivMapOfInjective I.subtype I.subtype_injective).toEquiv]
  exact s8_sylow_card I e T

/-- Transport of the generating pair, including maximality relative to I,
from explicit standard permutation calculations. See `s8_overgroups` for
the assembled theorem with these calculations discharged. -/
theorem s8_overgroups_of_standard
    (hpairMax : IsCoatom pairOvergroup) (hfourMax : IsCoatom fourOvergroup)
    (hpair : pairOvergroup ⊓ centralizer (pairOvergroup.pCoreIn 2 : Set X) ≤
      pairOvergroup.pCoreIn 2)
    (hfour : fourOvergroup ⊓ centralizer (fourOvergroup.pCoreIn 2 : Set X) ≤
      fourOvergroup.pCoreIn 2)
    (I : Subgroup G) (e : I ≃* X) (T : Sylow 2 I) :
    ∃ L₁ L₂ : Subgroup G,
      L₁ ≤ I ∧ L₂ ≤ I ∧ IsCoatom (L₁.subgroupOf I) ∧ IsCoatom (L₂.subgroupOf I) ∧
      (T : Subgroup I).map I.subtype ≤ L₁ ∧ (T : Subgroup I).map I.subtype ≤ L₂ ∧
      L₁ ⊔ L₂ = I ∧ L₁ ∈ Chapter1.He G ∧ L₂ ∈ Chapter1.He G ∧
      twoCore L₁ ≠ ⊥ ∧ twoCore L₂ ≠ ⊥ := by
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨K₁, K₂, hmax₁, hmax₂, hP₁, hP₂, hgen, hC₁, hC₂, hcore₁, hcore₂⟩ :=
    exists_overgroups_of_standard hpairMax hfourMax hpair hfour P
  let f : X →* G := I.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := I.subtype_injective.comp e.symm.injective
  have hr : f.range = I := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [f]⟩
  have hle (K : Subgroup X) : K.map f ≤ I := by
    rintro x ⟨y, _, rfl⟩
    exact (e.symm y).property
  have hmax (K : Subgroup X) (hK : IsCoatom K) : IsCoatom ((K.map f).subgroupOf I) := by
    have heq : (K.map f).subgroupOf I = e.symm.mapSubgroup K := by
      change (K.map (I.subtype.comp e.symm.toMonoidHom)).comap I.subtype = _
      rw [← Subgroup.map_map, Subgroup.comap_map_eq_self_of_injective I.subtype_injective]
      rfl
    rw [heq]
    exact (e.symm.mapSubgroup.isCoatom_iff K).mpr hK
  have hT : (P : Subgroup X).map f = (T : Subgroup I).map I.subtype := by
    change ((T : Subgroup I).map e.toMonoidHom).map f = _
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [f]
  refine ⟨K₁.map f, K₂.map f, hle _, hle _, hmax _ hmax₁, hmax _ hmax₂,
    hT ▸ Subgroup.map_mono hP₁, hT ▸ Subgroup.map_mono hP₂, ?_,
    map_core_centralizer_le f hf K₁ 2 hC₁, map_core_centralizer_le f hf K₂ 2 hC₂,
    map_pCoreIn_ne_bot f hf K₁ 2 hcore₁, map_pCoreIn_ne_bot f hf K₂ 2 hcore₂⟩
  rw [← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, hr]

/-- An actual isomorphism with C₂ × S₈ supplies two maximal proper subgroups
of I containing the mapped Sylow subgroup. They generate I, belong to the
ambient characteristic-two family He, and have nontrivial two-cores. -/
theorem s8_overgroups (I : Subgroup G) (e : I ≃* X) (T : Sylow 2 I) :
    ∃ L₁ L₂ : Subgroup G,
      L₁ ≤ I ∧ L₂ ≤ I ∧ IsCoatom (L₁.subgroupOf I) ∧ IsCoatom (L₂.subgroupOf I) ∧
      (T : Subgroup I).map I.subtype ≤ L₁ ∧ (T : Subgroup I).map I.subtype ≤ L₂ ∧
      L₁ ⊔ L₂ = I ∧ L₁ ∈ Chapter1.He G ∧ L₂ ∈ Chapter1.He G ∧
      twoCore L₁ ≠ ⊥ ∧ twoCore L₂ ≠ ⊥ :=
  s8_overgroups_of_standard pairOvergroup_isCoatom fourOvergroup_isCoatom
    pairOvergroup_core_centralizer_le fourOvergroup_core_centralizer_le I e T

/-- The chapter selection now uses an actual mapped Sylow subgroup and
constructs a member of Γe0; it does not assume that family is nonempty. -/
theorem s8_exists_gammaEvenZero_of_standard
    (hpairMax : IsCoatom pairOvergroup) (hfourMax : IsCoatom fourOvergroup)
    (hpair : pairOvergroup ⊓ centralizer (pairOvergroup.pCoreIn 2 : Set X) ≤
      pairOvergroup.pCoreIn 2)
    (hfour : fourOvergroup ⊓ centralizer (fourOvergroup.pCoreIn 2 : Set X) ≤
      fourOvergroup.pCoreIn 2)
    (M I : Subgroup G) (e : I ≃* X) (T : Sylow 2 I)
    (hout : ¬ I ≤ M) (hβ : (T : Subgroup I).map I.subtype ∈ beta M)
    (hbound : ∀ J ∈ gamma (Chapter1.He G) M,
      twoPart J ≤ Nat.card ((T : Subgroup I).map I.subtype)) :
    ∃ L : Subgroup G, L ≤ I ∧ L ∈ gammaEvenZero (Chapter1.He G) M := by
  obtain ⟨L₁, L₂, hL₁I, hL₂I, _, _, hT₁, hT₂, hgen, hHe₁, hHe₂, hcore₁, hcore₂⟩ :=
    s8_overgroups_of_standard hpairMax hfourMax hpair hfour I e T
  obtain ⟨L, hL, hΓ⟩ := exists_gammaEvenZero_of_generating_overgroups
    M I ((T : Subgroup I).map I.subtype) L₁ L₂ hgen hout hβ
    hT₁ hT₂ hHe₁ hHe₂ hcore₁ hcore₂ hbound
  refine ⟨L, ?_, hΓ⟩
  rcases hL with rfl | hL
  · exact hL₁I
  · exact Set.mem_singleton_iff.mp hL ▸ hL₂I

/-- The C₂ × S₈ branch yields a member of Γe0 from the earlier β and
half-Sylow bound inputs. No further permutation geometry is assumed. -/
theorem s8_exists_gammaEvenZero
    (M I : Subgroup G) (e : I ≃* X) (T : Sylow 2 I)
    (hout : ¬ I ≤ M) (hβ : (T : Subgroup I).map I.subtype ∈ beta M)
    (hbound : ∀ J ∈ gamma (Chapter1.He G) M,
      twoPart J ≤ Nat.card ((T : Subgroup I).map I.subtype)) :
    ∃ L : Subgroup G, L ≤ I ∧ L ∈ gammaEvenZero (Chapter1.He G) M :=
  s8_exists_gammaEvenZero_of_standard pairOvergroup_isCoatom fourOvergroup_isCoatom
    pairOvergroup_core_centralizer_le fourOvergroup_core_centralizer_le
    M I e T hout hβ hbound

end CFSG.Quasithin.Chapter2.A6ShadowRankOne
