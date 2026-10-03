module
public import Theory.GroupAction.QuotientFixedIndex
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# Fixed-point bounds for an actual quotient-conjugation actor

Suppose `P` normalizes `U` and a specified homomorphism `ρ` describes its
conjugation action on the literal quotient `U/(Z.subgroupOf U)`, using a
specified normality instance. If `x ∈ P` also lies in `A`, a bound on
`|U : U ∩ C_G(A)|` bounds the fixed-point index of `ρ(x)` on this quotient.
No coprimality or commutativity hypothesis is needed.

Restrict `U ∩ C_G(A)` to `U`. Its quotient image is fixed by `ρ(x)` by
the supplied conjugation identity, hence by all powers of `ρ(x)`. The
index of this image divides the original index, and enlargement to the
full fixed subgroup decreases the index. The subgroup cardinal-index
identities give the stated cardinal bound. The construction uses the
caller's exact quotient and action homomorphism throughout.

This is the fixed-index input for the single-involution application of
Stellmacher (1.3) in the proof of (9.1), Journal of Algebra 190 (1997), p.47.
-/

namespace Subgroup
public theorem quotient_conjugation_fixed_card_bound
    {G : Type*} [Group G] [Finite G] (P U Z A : Subgroup G)
    (hPU : P ≤ normalizer (U : Set G)) (hN : (Z.subgroupOf U).Normal) :
    let _ := hN
    ∀ ρ : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ p : P, ∀ u : U,
        ρ p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(p : G) * (u : G) * (p : G)⁻¹,
              (mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) →
      ∀ (x : P), (x : G) ∈ A → ∀ k : ℕ,
      Nat.card U ≤ k * Nat.card (U ⊓ centralizer (A : Set G) : Subgroup G) →
      Nat.card (U ⧸ Z.subgroupOf U) ≤ k *
        Nat.card (FixedPoints.subgroup (zpowers (ρ x)) (U ⧸ Z.subgroupOf U)) := by
  let _ := hN
  dsimp only
  intro ρ hρ x hx k hbound
  let W := U ⧸ Z.subgroupOf U
  let f := QuotientGroup.mk' (Z.subgroupOf U)
  let C := U ⊓ centralizer (A : Set G)
  let D := C.subgroupOf U
  let F := FixedPoints.subgroup (zpowers (ρ x)) W
  have hDcard : Nat.card D = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe (show C ≤ U from inf_le_left)).toEquiv
  have hmap : D.map f ≤ F := by
    rintro w ⟨u, hu, rfl⟩ a
    have hxu : (x : G) * (u : G) = (u : G) * (x : G) :=
      mem_centralizer_iff.mp hu.2 x hx
    have hfixed : (ρ x) • f u = f u := by
      change ρ x (f u) = f u
      rw [hρ]
      apply congrArg f
      apply Subtype.ext
      change (x : G) * (u : G) * (x : G)⁻¹ = (u : G)
      rw [hxu, mul_assoc, mul_inv_cancel, mul_one]
    exact smul_eq_self_of_mem_zpowers a.property hfixed
  have hDidx : D.index ≤ k := by
    rw [← hDcard, ← D.card_mul_index, mul_comm k] at hbound
    exact Nat.le_of_mul_le_mul_left hbound Nat.card_pos
  have hidx : F.index ≤ D.index :=
    (index_antitone hmap).trans (Nat.le_of_dvd
      (Nat.pos_of_ne_zero (FiniteIndex.index_ne_zero (H := D)))
      (D.index_map_dvd (QuotientGroup.mk'_surjective (Z.subgroupOf U))))
  rw [← F.card_mul_index, mul_comm k]
  exact Nat.mul_le_mul_left _ (hidx.trans hDidx)
end Subgroup
