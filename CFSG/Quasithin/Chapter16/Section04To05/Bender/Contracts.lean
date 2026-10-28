module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Action
public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.GroupTheory.DisjointCommutingProduct
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The local geometry to be constructed in Proposition 16.5.1

`Geometry` specifies the actual cyclic actor, its fixed and moved subgroups,
the model parameter, and the conjugator moving U_C inside V. Existence of
this data is a proof obligation, not an assumption of the source proposition.
There is no J₁ centralizer or global identification in the record.

The model parameter uses the fixed-field order for unitary groups. The
Suzuki model with parameter m has field order 2^(2m+1). The quotient is by
the actual component center; source 16.1.2 identifies it with O₂(L).

The product decomposition gives |V| = |U_C| 2^n. Thus the exceptional
O'Nan cardinalities force n = 2. The arithmetic deduction is independent
of constructing the geometry or proving GLS96 C.14.2.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1194–1195, Proposition 16.5.1.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.Bender
open Subgroup
open scoped IsMulCommutative

/-- The rank-one model with its specified binary field exponent. -/
def RankOneAt (Q : Type*) [Group Q] (n : ℕ) : Prop :=
  ClassicalGroup.IsPSL Q 2 (2 ^ n) ∨ ClassicalGroup.IsPSU Q 3 (2 ^ n) ∨
    ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧
      Nonempty (Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)

variable {G : Type*} [Group G]

/-- Output of the local construction before applying the O'Nan theorem.
Normality concerns the image of the actor in the stabilizer of U_C;
it is not ambient normality of X in G. -/
structure Geometry (T : Sylow 2 G) (L R : Subgroup G) (n : ℕ) where
  degree : 2 ≤ n
  model : RankOneAt (L ⧸ center L) n
  actor : Subgroup G
  actor_le : actor ≤ L ⊓ normalizer (componentSylow T L : Set G)
  actor_normalizes : actor ≤ normalizer (benderSpace T L : Set G)
  actor_cyclic : IsCyclic actor
  actor_card : Nat.card actor = 2 ^ n - 1
  elementary : IsElementaryAbelian 2 (benderSpace T L)
  fixed_eq : benderSpace T L ⊓ centralizer (actor : Set G) =
    omegaOneAmbient (commutingSylow T L)
  disjoint : Disjoint (omegaOneAmbient (commutingSylow T L)) ⁅benderSpace T L, actor⁆
  span : omegaOneAmbient (commutingSylow T L) ⊔ ⁅benderSpace T L, actor⁆ = benderSpace T L
  moved_card : Nat.card ↥(⁅benderSpace T L, actor⁆ : Subgroup G) = 2 ^ n
  regular : ∀ v ∈ ⁅benderSpace T L, actor⁆, v ≠ 1 →
    ∀ w ∈ ⁅benderSpace T L, actor⁆, w ≠ 1 → ∃! x : actor, MulAut.conj (x : G) v = w
  fixed_intersection : omegaOneAmbient (commutingSylow T L) =
    benderSpace T L ⊓ centralizer (L : Set G)
  actor_normal_in_stabilizer : ∀ a : normalizer (benderSpace T L : Set G),
    (a : G) ∈ normalizer (omegaOneAmbient (commutingSylow T L) : Set G) →
      (inducedActor (benderSpace T L) actor).conjBy
        ((benderSpace T L).normalizerMonoidHom.rangeRestrict a) =
          inducedActor (benderSpace T L) actor
  sylow_normalizes : (T : Subgroup G) ≤ normalizer (benderSpace T L : Set G)
  sylow_fixes : (T : Subgroup G) ≤ normalizer (omegaOneAmbient (commutingSylow T L) : Set G)
  mover : G
  mover_normalizes : mover ∈ normalizer (benderSpace T L : Set G)
  mover_eq : (omegaOneAmbient (commutingSylow T L)).conjBy mover = omegaOneAmbient R
  unitary_mover : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n) →
    mover ∈ normalizer (componentSylow T L : Set G)

/-- The constructed conjugator places U in the actual subgroup V. -/
theorem Geometry.omega_le {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n) : omegaOneAmbient R ≤ benderSpace T L := by
  rw [← d.mover_eq]
  calc
    (omegaOneAmbient (commutingSylow T L)).conjBy d.mover ≤
        (benderSpace T L).conjBy d.mover := map_mono le_sup_left
    _ = benderSpace T L := mem_normalizer_iff_map_conj_eq.mp d.mover_normalizes

/-- The exceptional cardinalities force the fixed-field size to be four. -/
theorem Geometry.degree_eq_two {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n)
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8) : n = 2 := by
  let := d.elementary
  have hc : omegaOneAmbient (commutingSylow T L) ≤
      centralizer ((⁅benderSpace T L, d.actor⁆ : Subgroup G) : Set G) := by
    intro x hx y hy
    have hxV : x ∈ benderSpace T L :=
      (show omegaOneAmbient (commutingSylow T L) ≤ benderSpace T L from le_sup_left) hx
    have hyV : y ∈ benderSpace T L := (le_sup_right.trans_eq d.span) hy
    exact congrArg Subtype.val (mul_comm (⟨y, hyV⟩ : benderSpace T L) ⟨x, hxV⟩)
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (omegaOneAmbient (commutingSylow T L)) ⁅benderSpace T L, d.actor⁆ d.disjoint hc
  have he := Nat.card_congr (e.trans (MulEquiv.subgroupCongr d.span)).toEquiv
  rw [Nat.card_prod, hUC, d.moved_card, hV] at he
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  change 2 ^ n = 4
  omega

end CFSG.Quasithin.Chapter16.Intersections.Bender
