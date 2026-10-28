module

public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryRankOne
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.DegreeBounds
public import Theory.Representation.Quotient

/-!
# Defining-characteristic reductions for G.9.3

The genuine triple-cover alternative (5) follows from the Sylow and
representation calculations in `AlternatingSixCover`. For binary SL₂,
`BinaryRankOne` derives the possible degrees and the actual Schur-field
parameters of every irreducible representation, using highest weights
and Frobenius descent. Its application below retains the original actor
and uses a genuine component isomorphism.

The rank-one module identifications, the higher-rank small-module
classifications, and the remaining model degree/rank estimates are still
required for the full defining-characteristic classification. In particular,
the explicit SL₂ automorphism-rank premise below is not yet discharged here.
`DegreeBounds` supplies only the arithmetic step once such estimates are proved.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3,
printed pp.354,356--357. Group identifications and central-cover restrictions
from Theorem C/A.3.6 remain inputs to this part of the argument.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic

open scoped MatrixGroups

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- A concrete automorphism-rank estimate bounds the original G.9 actor. -/
theorem single_component_actor_rank_le
    (h : ComponentHypothesis K ρ A L L m) {r : ℕ}
    (hr : primeRank 2 (MulAut L) ≤ r) : m ≤ r := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  apply (h.toSetup.rank_le_automorphisms ?_).trans hr
  rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_H]
  exact le_top

/-- G.9.3(5), from the actual central quotient and center of the component. -/
theorem triple_cover_alternating_six_parameters
    (h : ComponentHypothesis K ρ A L L m)
    (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (Subgroup.center L) = 3) :
    Module.finrank (ZMod 2) V = 6 ∧ 2 ≤ m := by
  let : Theory.GroupTheory.IsQuasisimple L := h.component.2
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hd := AlternatingSixCover.small_degree_eq_six e hz (ρ.comp L.subtype)
    (h.faithful.comp L.subtype_injective) h.single_component_degree_bound
  exact ⟨hd, by have := h.degree_le; omega⟩

/-- The degree and original-actor bounds for the SL₂ alternatives, conditional
only on the indicated model automorphism-rank estimate. Module recognition
is not asserted by this degree theorem. -/
theorem rank_one_degree_parameters
    (h : ComponentHypothesis K ρ A L L m)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : L ≃* SL(2,F)) (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (hr : primeRank 2 (MulAut SL(2,F)) ≤ n) :
    (Module.finrank (ZMod 2) V = 2 * n ∧ n - 1 ≤ m) ∨
      (n = 3 ∧ Module.finrank (ZMod 2) V = 8 ∧ m = 3) := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  have hnontrivial : ∃ g, σ g ≠ 1 := by
    by_contra! hzero
    have hL : L = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      change x = 1
      apply h.faithful
      calc
        ρ x = 1 := by simpa [σ] using hzero (e ⟨x, hx⟩)
        _ = ρ 1 := (map_one ρ).symm
    apply h.noncentral
    rw [hL, Subgroup.commutator_bot_left]
  have hlocal : primeRank 2 (MulAut L) ≤ n := by
    rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)]
    exact hr
  have hm := single_component_actor_rank_le h hlocal
  have hd := h.degree_le
  have hsmall : Module.finrank (ZMod 2) V ≤ 2 * (n + 1) := by omega
  rcases binary_small_degree_alternatives σ hnontrivial n hn hcard hsmall with hnat | hex
  · exact Or.inl ⟨hnat, by omega⟩
  · exact Or.inr ⟨hex.1, hex.2, by omega⟩

/-- The exact half-field and actor parameters of case (17), once its genuine
tensor degree and model automorphism-rank estimate have been established. -/
theorem linear_three_twisted_actor_parameters
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 0 < n)
    (hr : primeRank 2 (MulAut L) ≤ 4 * n)
    (hd : Module.finrank (ZMod 2) V = 9 * n) : n ≤ 2 ∧ m = 4 * n := by
  apply DegreeBounds.linear_three_twisted_parameters hn (single_component_actor_rank_le h hr)
  have := h.degree_le
  omega

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
