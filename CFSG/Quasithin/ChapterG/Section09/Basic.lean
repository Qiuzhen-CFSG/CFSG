module

public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.BinaryIrreducibleCentralizer

/-!
# Basic consequences of the G.9 hypotheses

The actor's stated order witnesses its two-rank in the ambient group.
The noncentral component condition in G.9.3 makes this rank positive.
A faithful irreducible binary action has trivial two-core, by the modular
normal-subgroup kernel theorem. Finally, a supplied SQTK cover gives an
actual quotient isomorphism and passes the K-group condition to the image.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9,
printed pp.351--356. These are preliminary deductions, not the terminal
group-and-module classifications.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09

open scoped IsMulCommutative

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A L H : Subgroup G} {m : ℕ}

/-- The actor in G.9.1 witnesses its stated rank in the ambient group. -/
theorem Setup.rank_le (h : Setup ρ A m) : m ≤ primeRank 2 G := by
  let : IsElementaryAbelian 2 A := h.elementary
  let : CommGroup A := IsMulCommutative.instCommGroup
  exact primeRank_ge_of_elementary_embedding
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A)) h.card_actor A.subtype A.subtype_injective

/-- The small-degree bound also holds with the ambient two-rank. -/
theorem Setup.degree_le_ambient_rank (h : Setup ρ A m) :
    Module.finrank (ZMod 2) V ≤ 2 * (primeRank 2 G + 1) :=
  h.degree_le.trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right h.rank_le 1))

/-- Normalization and irreducibility give the automorphism-rank bound
used to apply small-degree representation results to a component. -/
theorem Setup.rank_le_automorphisms (h : Setup ρ A m)
    [Representation.IsIrreducible (ρ.comp L.subtype)]
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) : m ≤ primeRank 2 (MulAut L) := by
  let : IsElementaryAbelian 2 A := h.elementary
  let : CommGroup A := IsMulCommutative.instCommGroup
  exact primeRank_ge_of_elementary_embedding
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A)) h.card_actor
    (L.normalizerMonoidHom.comp (Subgroup.inclusion hAL))
    (Representation.BinaryIrreducibleCentralizer.elementary_conjugation_injective
      ρ L h.faithful A hAL)

/-- In the single-component case of G.9.3 the original actor's bound is
controlled by the component automorphism group, without replacing the actor. -/
theorem ComponentHypothesis.single_component_degree_bound {K : GroupClass.{u}}
    (h : ComponentHypothesis K ρ A L L m) :
    Module.finrank (ZMod 2) V ≤ 2 * (primeRank 2 (MulAut L) + 1) := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hn : A ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_H]
    exact le_top
  exact h.degree_le.trans (Nat.mul_le_mul_left 2
    (Nat.add_le_add_right (h.toSetup.rank_le_automorphisms hn) 1))

/-- Rank zero is precisely the trivial actor, and is not excluded by G.9.1. -/
theorem Setup.actor_eq_bot_iff (h : Setup ρ A m) : A = ⊥ ↔ m = 0 := by
  rw [← Subgroup.card_eq_one, h.card_actor]
  simp

/-- Unlike G.9.1 alone, the noncentrality premise of G.9.3 forces positive rank. -/
theorem ComponentHypothesis.actor_rank_pos {K : GroupClass.{u}}
    (h : ComponentHypothesis K ρ A L H m) : 0 < m := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hA := h.toSetup.actor_eq_bot_iff.mpr hm
  exact h.noncentral (by rw [hA, Subgroup.commutator_bot_right])

/-- The two-core observation preceding the proofs of G.9.3 and G.9.4. -/
theorem Setup.twoCore_eq_bot (h : Setup ρ A m) [Representation.IsIrreducible ρ] :
    pCore 2 G = ⊥ := by
  have hk := Representation.normal_p_subgroup_le_ker ρ (pCore 2 G) pCore_isPGroup
  rw [ρ.ker_eq_bot h.faithful] at hk
  exact le_bot_iff.mp hk

omit [Finite G] in
/-- The cover really presents the group as a quotient by its kernel. -/
noncomputable def SQTKCover.quotientEquiv {K : GroupClass.{u}} (c : SQTKCover K G) :
    (c.Cover ⧸ c.projection.ker) ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective c.projection c.surjective

omit [Finite G] in
/-- K-group membership descends from the finite SQTK cover. No rank bound
is claimed to descend to arbitrary quotients here. -/
theorem SQTKCover.isKGroup {K : GroupClass.{u}} (c : SQTKCover K G) : IsKGroup K G :=
  c.sqtk.isKGroup.of_surjective c.projection c.surjective

end CFSG.Quasithin.ChapterG.Section09
