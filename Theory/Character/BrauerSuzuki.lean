module

public import Mathlib.Data.Complex.Basic
public import Mathlib.GroupTheory.Index
public import Theory.FiniteSums
public import Theory.Star
public import Theory.Character.ClassFunction
public import Theory.Character.Induction

/-!
# Brauer--Suzuki machinery (Gorenstein 4.4.6)

Reindexing and support lemmas, and the Brauer--Suzuki expansion of the scalar
product of two induced class functions as a double sum over the base group and
the subgroup.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u

-- This file's sums over subgroups need `Fintype ↥H`.  `Fintype.ofFinite` as a
-- local instance covers statement contexts, but inside `classical` proofs
-- mathlib's `instFintypeSubtypeMemOfDecidablePred` wins (it needs a
-- `DecidablePred`); making `Classical.propDecidable` a local instance too
-- keeps statement and proof contexts synthesizing the *same* instance, so
-- calc chains across the two elaborate consistently.  All local: deliberately
-- not exported, so importing this module does not change instance resolution
-- elsewhere.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable


/-- The summand of the pairing of two induced class functions:
`δ₁ h · conj(δ₂(z⁻¹·h·z))` when `z⁻¹·h·z ∈ H`, else `0`. -/
noncomputable def pairingSummand {G : Type u} [Group G] (H : Subgroup G)
    (δ₁ δ₂ : ClassFunction (↥H)) (z : G) (h : ↥H)
    : ℂ := by
  classical
  exact if hz : z⁻¹ * (h : G) * z ∈ H then δ₁ h * star (δ₂ ⟨z⁻¹ * (h : G) * z, hz⟩) else 0

/-- The Brauer--Suzuki expansion: the scalar product of two induced class
functions is a double sum over the base group and the subgroup. -/
lemma pairing_induced_expand {L : Type u} [Group L] [Fintype L] (K : Subgroup L)
    (δ₁ δ₂ : ClassFunction (↥K))
    : scalarProduct L (inducedClassFunction K δ₁) (inducedClassFunction K δ₂)
      = ((Nat.card (↥K) : ℂ)⁻¹ * (Nat.card (↥K) : ℂ)⁻¹)
        * ∑ z : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h := by
  classical
  let c : ℂ := (Nat.card (↥K) : ℂ)⁻¹
  have hcstar : star c = c := by
    unfold c
    exact (map_inv₀ (starRingEnd ℂ) (Nat.card (↥K) : ℂ)).trans (by simp)
  let A : L → L → ℂ :=
    fun g x => if hx : x⁻¹ * g * x ∈ K then δ₁ ⟨x⁻¹ * g * x, hx⟩ else 0
  let B : L → L → ℂ :=
    fun g y => if hy : y⁻¹ * g * y ∈ K then δ₂ ⟨y⁻¹ * g * y, hy⟩ else 0
  have hsubst : ∀ x y : L,
      (∑ g : L, A g x * star (B g y)) =
        ∑ h : ↥K, pairingSummand K δ₁ δ₂ (x⁻¹ * y) h := by
    intro x y
    let z : L := x⁻¹ * y
    calc
      (∑ g : L, A g x * star (B g y))
          = ∑ h : L, A (x * h * x⁻¹) x * star (B (x * h * x⁻¹) y) := by
        refine (Finset.sum_bij (fun h hh => x * h * x⁻¹) ?_ ?_ ?_ ?_).symm
        · intro h hh
          simp
        · intro h₁ hh₁ h₂ hh₂ hEq
          exact mul_left_cancel (mul_right_cancel hEq)
        · intro g hg
          refine ⟨x⁻¹ * g * x, by simp, ?_⟩
          group
        · intro h hh
          rfl
      _ = ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h := by
        have hsummand : ∀ h : L,
            A (x * h * x⁻¹) x * star (B (x * h * x⁻¹) y) =
              (if hK : h ∈ K then
                (if hz0 : z⁻¹ * h * z ∈ K then
                  δ₁ ⟨h, hK⟩ * star (δ₂ ⟨z⁻¹ * h * z, hz0⟩) else 0)
               else 0) := by
          intro h
          have hA : A (x * h * x⁻¹) x = (if hK : h ∈ K then δ₁ ⟨h, hK⟩ else 0) := by
            have hEq : x⁻¹ * (x * h * x⁻¹) * x = h := by group
            change
              (if hx : x⁻¹ * (x * h * x⁻¹) * x ∈ K then
                δ₁ ⟨x⁻¹ * (x * h * x⁻¹) * x, hx⟩ else 0) =
              (if hK : h ∈ K then δ₁ ⟨h, hK⟩ else 0)
            rw [hEq]
          have hB : star (B (x * h * x⁻¹) y) =
              (if hz0 : z⁻¹ * h * z ∈ K then star (δ₂ ⟨z⁻¹ * h * z, hz0⟩) else 0) := by
            have hEq : y⁻¹ * (x * h * x⁻¹) * y = z⁻¹ * h * z := by
              change y⁻¹ * (x * h * x⁻¹) * y = (x⁻¹ * y)⁻¹ * h * (x⁻¹ * y)
              group
            change
              star (if hy : y⁻¹ * (x * h * x⁻¹) * y ∈ K then
                δ₂ ⟨y⁻¹ * (x * h * x⁻¹) * y, hy⟩ else 0) =
              (if hz0 : z⁻¹ * h * z ∈ K then star (δ₂ ⟨z⁻¹ * h * z, hz0⟩) else 0)
            rw [hEq]
            by_cases hz0 : z⁻¹ * h * z ∈ K <;> simp [hz0]
          rw [hA, hB]
          by_cases hK : h ∈ K
          · by_cases hz0 : z⁻¹ * h * z ∈ K <;> simp [hK, hz0]
          · simp [hK]
        calc
          (∑ h : L, A (x * h * x⁻¹) x * star (B (x * h * x⁻¹) y))
              = ∑ h : L,
                  (if hK : h ∈ K then
                      (if hz0 : z⁻¹ * h * z ∈ K then
                          δ₁ ⟨h, hK⟩ * star (δ₂ ⟨z⁻¹ * h * z, hz0⟩)
                        else
                          0)
                    else
                      0) := by
            refine Finset.sum_congr rfl ?_
            intro h hh
            exact hsummand h
          _ = ∑ h : ↥K,
                (if hz0 : z⁻¹ * (h : L) * z ∈ K then
                    δ₁ h * star (δ₂ ⟨z⁻¹ * (h : L) * z, hz0⟩)
                  else
                    0) := by
            calc
              (∑ h : L,
                  (if hK : h ∈ K then
                      (if hz0 : z⁻¹ * h * z ∈ K then
                          δ₁ ⟨h, hK⟩ * star (δ₂ ⟨z⁻¹ * h * z, hz0⟩)
                        else
                          0)
                    else
                      0))
                  = Finset.sum (Finset.univ.filter (fun h : L => h ∈ K))
                      (fun h =>
                        (if hK : h ∈ K then
                            (if hz0 : z⁻¹ * h * z ∈ K then
                                δ₁ ⟨h, hK⟩ * star (δ₂ ⟨z⁻¹ * h * z, hz0⟩)
                              else
                                0)
                          else
                            0)) := by
                refine (Finset.sum_subset (by intro h hh; exact Finset.mem_univ h)
                          ?_).symm
                intro h hh hnot
                have hhK : h ∉ K := by
                  intro hK
                  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ h, hK⟩)
                simp [hhK]
              _ = ∑ h : ↥K,
                    (if hz0 : z⁻¹ * (h : L) * z ∈ K then
                        δ₁ h * star (δ₂ ⟨z⁻¹ * (h : L) * z, hz0⟩)
                      else
                        0) := by
                refine Finset.sum_bij (fun h hh =>
                  (⟨(h : L), (Finset.mem_filter.mp hh).2⟩ : ↥K)) ?_ ?_ ?_ ?_
                · intro h hh
                  simp
                · intro h₁ hh₁ h₂ hh₂ hEq
                  exact congrArg Subtype.val hEq
                · intro h hh
                  refine ⟨(h : L), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩, ?_⟩
                  exact Subtype.ext rfl
                · intro a ha
                  by_cases hK : a ∈ K
                  · by_cases hz0 : z⁻¹ * a * z ∈ K
                    · simp [hK, hz0]
                    · simp [hK, hz0]
                  · exfalso
                    exact hK (Finset.mem_filter.mp ha).2
          _ = ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h := by
            refine Finset.sum_congr rfl ?_
            intro h hh
            by_cases hz0 : z⁻¹ * (h : L) * z ∈ K
            · rw [pairingSummand]
            · rw [pairingSummand]
  calc
    scalarProduct L (inducedClassFunction K δ₁) (inducedClassFunction K δ₂)
        = (Nat.card L : ℂ)⁻¹
          * ∑ g : L, (c * ∑ x : L, A g x) * star (c * ∑ y : L, B g y) := by
      rw [scalarProduct]
      congr 1
    _ = (Nat.card L : ℂ)⁻¹
        * (c * c)
        * ∑ g : L, ∑ x : L, ∑ y : L, A g x * star (B g y) := by
      calc
        (Nat.card L : ℂ)⁻¹ * (∑ g : L, (c * ∑ x : L, A g x) * star (c * ∑ y : L, B g y))
            = (Nat.card L : ℂ)⁻¹
              * ((c * c) * ∑ g : L, (∑ x : L, A g x) * (∑ y : L, star (B g y))) := by
          congr 1
          calc
            ∑ g : L, (c * ∑ x : L, A g x) * star (c * ∑ y : L, B g y)
                = ∑ g : L, (c * ∑ x : L, A g x) * (c * (∑ y : L, star (B g y))) := by
              refine Finset.sum_congr rfl ?_
              intro g hg
              simp [hcstar]
            _ = ∑ g : L, c * c * ((∑ x : L, A g x) * (∑ y : L, star (B g y))) := by
              refine Finset.sum_congr rfl ?_
              intro g hg
              ring
            _ = (c * c) * ∑ g : L, (∑ x : L, A g x) * (∑ y : L, star (B g y)) := by
              rw [← Finset.mul_sum]
        _ = (Nat.card L : ℂ)⁻¹
            * (c * c)
            * ∑ g : L, (∑ x : L, A g x) * (∑ y : L, star (B g y)) := by
          rw [← mul_assoc]
        _ = (Nat.card L : ℂ)⁻¹
            * (c * c)
            * ∑ g : L, ∑ x : L, ∑ y : L, A g x * star (B g y) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro g hg
          rw [Fintype.sum_mul_sum]
    _ = (Nat.card L : ℂ)⁻¹
        * (c * c)
        * ∑ x : L, ∑ y : L, ∑ g : L, A g x * star (B g y) := by
      congr 1
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun g x : L => ∑ y : L, A g x * star (B g y))]
      refine Finset.sum_congr rfl ?_
      intro x hx
      exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun g y : L => A g x * star (B g y))
    _ = (Nat.card L : ℂ)⁻¹
        * (c * c)
        * ∑ x : L, ∑ y : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ (x⁻¹ * y) h := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x hx
      refine Finset.sum_congr rfl ?_
      intro y hy
      exact hsubst x y
    _ = (Nat.card L : ℂ)⁻¹
        * (c * c)
        * ((Nat.card L : ℂ) * ∑ z : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h) := by
      congr 1
      rw [conj_reindex_mul (fun z : L => ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h)]
    _ = (c * c) * ∑ z : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h := by
      let S : ℂ := ∑ z : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h
      calc
        (Nat.card L : ℂ)⁻¹ * (c * c) * ((Nat.card L : ℂ) * S)
            = (Nat.card L : ℂ)⁻¹ * (Nat.card L : ℂ) * ((c * c) * S) := by
          ring
        _ = (c * c) * S := by
          rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt (Nat.card_pos (α := L)))),
            one_mul]
    _ = ((Nat.card (↥K) : ℂ)⁻¹ * (Nat.card (↥K) : ℂ)⁻¹)
        * ∑ z : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h := by
      rfl
