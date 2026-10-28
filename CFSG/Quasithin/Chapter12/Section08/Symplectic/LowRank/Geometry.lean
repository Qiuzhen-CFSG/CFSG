module
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank.Action
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness

/-!
# The marked line and hyperplane in U/Z(U)

The zero criterion of the commutator form identifies What with the orthogonal
complement of V₂hat. The center-intersection equation V∩Z(U)=V₁ identifies
the kernel of V₂→U/Z(U) with V₁. The actual orders four and two then prove
that V₂hat is a line. No dimension or hyperplane conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
12.8.8(2–3), printed pp.851–852, used in 12.8.11(6), printed p.855.
-/

public section

open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The hyperplane is the orthogonal complement of the marked line, by the
zero criterion of the source commutator form (12.8.8(2)). -/
theorem hatSpace_W_eq_orthogonal (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U,
      B (Additive.ofMul (QuotientGroup.mk' (center F.U) u))
        (Additive.ofMul (QuotientGroup.mk' (center F.U) v)) = 0 ↔ Commute u v) :
    hatSpace F F.W = B.orthogonal (hatSpace F (F.Vi 2)) := by
  apply le_antisymm
  · intro w hw l hl
    obtain ⟨u, hu, heu⟩ := (show w.toMul ∈ hatImage F F.W from hw)
    obtain ⟨v, hv, hev⟩ := (show l.toMul ∈ hatImage F (F.Vi 2) from hl)
    have hc : Commute v u := by
      apply Subtype.ext
      exact hu.2 v hv
    have he := (hB v u).mpr hc
    simpa only [hev, heu, ofMul_toMul] using he
  · intro w hw
    obtain ⟨u, heu⟩ := QuotientGroup.mk'_surjective (center F.U) w.toMul
    have hu : (u : G) ∈ F.W := by
      refine ⟨u.property, fun v hv => ?_⟩
      let v' : F.U := ⟨v, (F.le_seed 2).trans (le_conjugateSpanBy V F.H) hv⟩
      have hvhat : Additive.ofMul (QuotientGroup.mk' (center F.U) v') ∈
          hatSpace F (F.Vi 2) := ⟨v', hv, rfl⟩
      have he := hw _ hvhat
      rw [← ofMul_toMul w, ← heu] at he
      exact congrArg Subtype.val ((hB v' u).mp he).eq
    exact ⟨u, hu, heu⟩

/-- The plane has one-dimensional image, using the actual center intersection
of 12.8.8(3) and the orders in the marked flag. -/
theorem finrank_hatSpace_plane (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 F.Uhat] (hn : 2 ≤ n)
    (hc : V ⊓ F.ZU = F.Vi 1) :
    finrank (ZMod 2) (hatSpace F (F.Vi 2)) = 1 := by
  have hU : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  let π : F.Vi 2 →* F.Uhat := (QuotientGroup.mk' (center F.U)).comp
    (inclusion hU)
  have hk : π.ker = (F.Vi 1).subgroupOf (F.Vi 2) := by
    ext v
    change π v = 1 ↔ (v : G) ∈ F.Vi 1
    rw [show π v = QuotientGroup.mk' (center F.U)
      ⟨v, hU v.property⟩ from rfl]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hz
      rw [← hc]
      exact ⟨F.le_seed 2 v.property, ⟨_, hz, rfl⟩⟩
    · intro hv
      have hz : (v : G) ∈ F.ZU := (show F.Vi 1 ≤ F.ZU from hc ▸ inf_le_right) hv
      obtain ⟨u, hu, he⟩ := hz
      have he' : u = ⟨v, hU v.property⟩ :=
        Subtype.ext he
      exact he' ▸ hu
  have hr : π.range = hatImage F (F.Vi 2) := by
    ext q
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨⟨v, hU v.property⟩,
        v.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  have hkcard : Nat.card π.ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (F.monotone (by omega : 1 ≤ 2))).toEquiv]
    simpa using F.card 1 (by omega)
  have hc2 : Nat.card (F.Vi 2) = 4 := by simpa using F.card 2 hn
  have hcard := π.ker.card_mul_index
  rw [index_ker, hkcard, hc2, hr] at hcard
  have hhat : Nat.card (hatSpace F (F.Vi 2)) = 2 := by
    change Nat.card (hatImage F (F.Vi 2)) = 2
    omega
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := hatSpace F (F.Vi 2))
  rw [Nat.card_zmod, hhat] at hd
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hd.symm

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
