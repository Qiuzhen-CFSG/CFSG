module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Commuting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences.Counting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences.CentralizedSingletons.Septuples
/-!
# Bender's centralized-singleton incidence equation

For each of the 28 three-subgroups X of H, the supplied local count gives
2d - 1 commuting involutions. Exactly one lies in H, exactly 2e lie in
septuple fibers, and every remaining one lies in a singleton fiber.
Conversely, each centralized singleton has a centralizer of order three
inside H and hence centralizes exactly one of these three-subgroups.

Counting the actual pairs in these two ways gives c + 56(1 + e) = 56d.
Only the source inputs and the explicit seven-inverter count are assumed;
all fiber, uniqueness and centralization counts are proved here.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed p.227, the commuting-three-subgroup paragraph.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Removing the inside and septuple involutions leaves precisely the commuting singletons. -/
public theorem bender_three_singleton_commuting_card
    (h : Janko1CentralizerData G) (d e : ℕ)
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h)
    (geometry : BenderNormalizerGeometry h) (he : e ≤ 1)
    (hseven : ∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = 7 →
      Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} = 7 * e)
    (X : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3) :
    Nat.card {u : BenderOutsideInvolutions (normalizer (h.sylow : Set G)) //
      X.1 ≤ centralizer ({u.1} : Set G) ∧
      Nat.card (BenderFiber (normalizer (h.sylow : Set G))
        (benderRightCoset (normalizer (h.sylow : Set G)) u.1)) = 1} +
      2 * (1 + e) = 2 * d := by
  classical
  let H := normalizer (h.sylow : Set G)
  let J := {u : BenderOutsideInvolutions H // X.1 ≤ centralizer ({u.1} : Set G)}
  let p : J → Prop := fun u => Nat.card (BenderFiber H (benderRightCoset H u.1.1)) = 1
  let ei : {u : J // p u} ≃ {u : BenderOutsideInvolutions H //
      X.1 ≤ centralizer ({u.1} : Set G) ∧ Nat.card (BenderFiber H (benderRightCoset H u.1)) = 1} :=
    { toFun := fun u => ⟨u.1.1, u.1.2, u.2⟩
      invFun := fun u => ⟨⟨u.1, u.2.1⟩, u.2.2⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  let eo : {u : J // ¬ p u} ≃ {u : BenderOutsideInvolutions H //
      X.1 ≤ centralizer ({u.1} : Set G) ∧ Nat.card (BenderFiber H (benderRightCoset H u.1)) = 7} :=
    { toFun := fun u => ⟨u.1.1, u.1.2,
        (bender_three_commuting_fiber_cases h d localData geometry X u.1.1 u.1.2).resolve_left u.2⟩
      invFun := fun u => ⟨⟨u.1, u.2.1⟩, by
        change Nat.card (BenderFiber H (benderRightCoset H u.1.1)) ≠ 1
        rw [u.2.2]
        decide⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  have hc := Nat.card_congr (Equiv.sumCompl p).symm
  have : Finite J := by unfold J BenderOutsideInvolutions; infer_instance
  rw [Nat.card_sum, Nat.card_congr ei, Nat.card_congr eo,
    bender_three_septuple_commuting_card h normalizerData geometry e he hseven X] at hc
  have hj : Nat.card J + 2 = 2 * d := bender_three_outside_commuting_card h d localData geometry X
  change Nat.card {u : BenderOutsideInvolutions H // X.1 ≤ centralizer ({u.1} : Set G) ∧
    Nat.card (BenderFiber H (benderRightCoset H u.1)) = 1} + 2 * (1 + e) = 2 * d
  omega

/-- Double-counting the actual singleton/three-subgroup incidences. -/
public theorem bender_centralized_singleton_pair_card
    (h : Janko1CentralizerData G) (normalizerData : BenderNormalizerData h) :
    Nat.card (Σ X : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3,
      {u : BenderOutsideInvolutions (normalizer (h.sylow : Set G)) //
        X.1 ≤ centralizer ({u.1} : Set G) ∧
        Nat.card (BenderFiber (normalizer (h.sylow : Set G))
          (benderRightCoset (normalizer (h.sylow : Set G)) u.1)) = 1}) =
      Nat.card (BenderCentralizedSingletons (normalizer (h.sylow : Set G))) := by
  classical
  let H := normalizer (h.sylow : Set G)
  let A := BenderSubgroupsOfOrder H 3
  let T := fun X : A => {u : BenderOutsideInvolutions H // X.1 ≤ centralizer ({u.1} : Set G) ∧
    Nat.card (BenderFiber H (benderRightCoset H u.1)) = 1}
  let f : (Σ X : A, T X) → BenderCentralizedSingletons H := fun a =>
    ⟨a.2.1.1, a.2.1.2.1,
      fun heq => a.2.1.2.2 ((benderRightCoset_eq_base_iff H _).mp heq), a.2.2.2, by
        obtain ⟨x, hx, hX⟩ := bender_three_generator a.1.1 a.1.2.2
        have hxX : x ∈ a.1.1 := hX ▸ mem_zpowers x
        refine ⟨x, a.1.2.1 hxX, ?_, mem_centralizer_singleton_iff.mp (a.2.2.1 hxX)⟩
        intro hx1
        simp [hx1] at hx⟩
  have hfi : Function.Injective f := by
    rintro ⟨X, u⟩ ⟨Y, v⟩ huv
    have huvG : u.1.1 = v.1.1 := congrArg (fun a : BenderCentralizedSingletons H => a.1) huv
    have hX : X.1 ≤ centralizer ({(f ⟨X, u⟩).1} : Set G) := u.2.1
    have hY : Y.1 ≤ centralizer ({(f ⟨X, u⟩).1} : Set G) := by
      change Y.1 ≤ centralizer ({u.1.1} : Set G)
      rw [huvG]
      exact v.2.1
    have hXY : X = Y := (bender_singleton_unique_three h normalizerData (f ⟨X, u⟩)).unique hX hY
    subst Y
    have huv' : u = v := Subtype.ext (Subtype.ext huvG)
    subst v
    rfl
  have hfs : Function.Surjective f := by
    intro u
    obtain ⟨X, hX, _⟩ := bender_singleton_unique_three h normalizerData u
    refine ⟨⟨X, ⟨⟨u.1, u.2.1, ?_⟩, hX, u.2.2.2.1⟩⟩, rfl⟩
    intro huH
    exact u.2.2.1 ((benderRightCoset_eq_base_iff H _).mpr huH)
  exact Nat.card_congr (Equiv.ofBijective f ⟨hfi, hfs⟩)

/-- Bender's centralized-singleton incidence equation, with only the local seven-inverter
count left as an explicit input to the independent final order assembly. -/
public theorem bender_centralized_singleton_incidence
    (h : Janko1CentralizerData G) (d e : ℕ)
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h)
    (geometry : BenderNormalizerGeometry h) (he : e ≤ 1)
    (hseven : ∀ x : normalizer (h.sylow : Set G), orderOf (x : G) = 7 →
      Nat.card {t : G // orderOf t = 2 ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹} = 7 * e) :
    Nat.card (BenderCentralizedSingletons (normalizer (h.sylow : Set G))) +
      56 * (1 + e) = 56 * d := by
  classical
  let H := normalizer (h.sylow : Set G)
  let A := BenderSubgroupsOfOrder H 3
  let T := fun X : A => {u : BenderOutsideInvolutions H // X.1 ≤ centralizer ({u.1} : Set G) ∧
    Nat.card (BenderFiber H (benderRightCoset H u.1)) = 1}
  have : Finite A := by unfold A BenderSubgroupsOfOrder; infer_instance
  let : Fintype A := Fintype.ofFinite A
  have : ∀ X : A, Finite (T X) := fun X => by unfold T BenderOutsideInvolutions; infer_instance
  have hc : Nat.card (BenderCentralizedSingletons H) = ∑ X : A, Nat.card (T X) := by
    rw [← bender_centralized_singleton_pair_card h normalizerData, Nat.card_sigma]
  have hlocal (X : A) : Nat.card (T X) + 2 * (1 + e) = 2 * d :=
    bender_three_singleton_commuting_card h d e localData normalizerData geometry he hseven X
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun X _ => hlocal X)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← hc] at hsum
  have hA : Fintype.card A = 28 := (Nat.card_eq_fintype_card.symm).trans geometry.three_subgroups
  rw [hA] at hsum
  change Nat.card (BenderCentralizedSingletons H) + 56 * (1 + e) = 56 * d
  omega

end CFSG.Quasithin.Janko1CentralizerData
