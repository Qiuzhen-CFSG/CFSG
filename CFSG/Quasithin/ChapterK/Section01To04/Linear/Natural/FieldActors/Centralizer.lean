module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Coefficients
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.FixedSpaces
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Centralizer.Descent
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Centralizer.Counting
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Centralizer.UpperBound
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Centralizer.FixedPlane

/-!
# Natural field-involution centralizer calculations

For a faithful semilinear extension of the marked natural SL₃(2^(2s)) action,
the literal centralizer of an outer involution has two-rank exactly `2*s+1`.
The upper bound descends commuting linear actors to the field of order `2^s`
and bounds the elementary coefficient image by two. A fixed root plane together
with the actual outer involution attains the bound. Both constructions are
proved in the imported modules, with no remaining centralizer-model premises.

The source applications discharge the centralizer-rank calculation in K.3.2.1.
The reexported `source_elementary_rank_le` gives the bound for every elementary
actor containing the involution; the displacement comparison remains with the
outer-actor assembly.

Source: Aschbacher–Smith, K.3.2.1, printed pp.454–455, manuscript of 1 March 2004.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors.Centralizer

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : BinaryField)
  (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))

/-- The constructed elementary subgroup contains the actual outer involution
and has binary rank `2*s+1`, as well as the corresponding exact order. -/
theorem exists_attaining_elementary_subgroup_rank
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hdegree : F.degree = 2 * s) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({a} : Set G) ∧
      a ∈ E ∧ IsElementaryAbelian 2 E ∧ rank E = 2 * s + 1 ∧
      Nat.card E = 2 ^ (2 * s + 1) := by
  obtain ⟨_, E, _, _, _, _, hEC, haE, hE, hcard⟩ :=
    exists_attaining_elementary_subgroup F ρ L e hf hs a ha haL s hdegree
  refine ⟨E, hEC, haE, hE, ?_, hcard⟩
  rw [rank, hcard, Nat.log_pow (by decide : 1 < 2)]

/-- Exact two-rank of the literal centralizer of a natural outer field involution. -/
theorem primeRank_centralizer_eq
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s) :
    primeRank 2 (Subgroup.centralizer ({a} : Set G)) = 2 * s + 1 := by
  refine le_antisymm
    (primeRank_centralizer_le ρ L F e hf hs a ha haL s hspos hdegree) ?_
  obtain ⟨E, _, haE, hE, hrank, _⟩ :=
    exists_attaining_elementary_subgroup_rank ρ L F e hf hs a ha haL s hdegree
  exact hrank ▸ elementary_rank_le_centralizer E hE a haE

/-- The attaining subgroup for the recognized natural source input, with its
binary rank and exact order and no remaining descent or placement hypothesis. -/
theorem source_outer_attaining_elementary_subgroup_rank {K : GroupClass}
    (h : SourceInput ρ L F 3 K) (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hdegree : F.degree = 2 * s) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({a} : Set G) ∧
      a ∈ E ∧ IsElementaryAbelian 2 E ∧ rank E = 2 * s + 1 ∧
      Nat.card E = 2 ^ (2 * s + 1) :=
  exists_attaining_elementary_subgroup_rank ρ L F h.natural h.faithful h.semilinear
    a ha haL s hdegree

/-- The centralizer-rank equality used in K.3.2.1, with both bounds discharged. -/
theorem source_primeRank_centralizer_eq {K : GroupClass}
    (h : SourceInput ρ L F 3 K) (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s) :
    primeRank 2 (Subgroup.centralizer ({a} : Set G)) = 2 * s + 1 :=
  primeRank_centralizer_eq ρ L F h.natural h.faithful h.semilinear
    a ha haL s hspos hdegree

end CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors.Centralizer
