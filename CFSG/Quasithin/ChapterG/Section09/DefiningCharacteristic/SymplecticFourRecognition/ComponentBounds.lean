module

public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# Component and actor bounds for G.9.3(9)

The actual binary derived group is identified with A₆ by the polar action,
so its full automorphism group has two-rank at most three. This covers
every two-element field witness. For a component identified with this
carrier, normality and irreducibility bound the original actor by three
and the original module degree by eight.

The nonbinary reduction below still takes the automorphism-rank calculation
as an explicit premise. A natural-module identification yields degree 4n
and m≥2n−1 without replacing the original actor. Arbitrary-module recognition
remains a separate obligation, also at the binary endpoint.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(9),
printed pp.354,356--357.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition

open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour

/-- The full automorphism bound for the smallest *derived* carrier.
The whole group Sp₄(2) is not substituted for its commutator subgroup. -/
theorem binary_automorphism_rank_le {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    primeRank 2 (MulAut (commutator (Matrix.symplecticGroup (Fin 2) F))) ≤ 3 := by
  rw [primeRank_equiv 2 (MulAut.congr (Binary.derivedEquivAlternatingSix hF))]
  exact AlternatingSixCover.alternating_six_automorphism_two_rank

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The automorphism-rank calculation controls the *original* actor and gives
the exhaustive recognition window 6n+2 on the original representation. -/
theorem component_degree_window_of_automorphism_rank
    (h : ComponentHypothesis K ρ A L L m)
    {F : Type*} [Field F] [Finite F] (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) F))
    {n : ℕ} (hr : primeRank 2
      (MulAut (commutator (Matrix.symplecticGroup (Fin 2) F))) ≤ 3 * n) :
    m ≤ 3 * n ∧ Module.finrank (ZMod 2) V ≤ 6 * n + 2 := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_H]
    exact le_top
  have hm := h.toSetup.rank_le_automorphisms hAL
  rw [primeRank_equiv 2 (MulAut.congr e)] at hm
  have hm' := hm.trans hr
  exact ⟨hm', by have := h.degree_le; omega⟩

/-- An unconditional binary-endpoint bound under the genuine G.9.3 hypotheses.
The ambient action is retained for the small-parameter recognition argument. -/
theorem binary_component_bounds
    (h : ComponentHypothesis K ρ A L L m)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) F)) :
    m ≤ 3 ∧ Module.finrank (ZMod 2) V ≤ 8 := by
  simpa using component_degree_window_of_automorphism_rank h e
    (n := 1) (by simpa using binary_automorphism_rank_le hF)

/-- Once the representation is recognized, both numerical clauses of (9)
follow for the given actor, not only for some actor of maximal rank. -/
theorem natural_component_parameters
    (h : ComponentHypothesis K ρ A L L m)
    {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hnatural : Quasiequivalent (ρ.comp L.subtype) (binaryNatural F)) :
    Module.finrank (ZMod 2) V = 4 * n ∧ 2 * n - 1 ≤ m := by
  have hd := finrank_of_quasiequivalent hF hnatural
  exact ⟨hd, by have := h.degree_le; omega⟩

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
