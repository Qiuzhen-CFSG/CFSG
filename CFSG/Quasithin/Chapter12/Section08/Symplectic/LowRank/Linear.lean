module
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank.Geometry
public import Theory.LinearAlgebra.DisplacementFiltration
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The two linear cases of the low-rank witness

For a nonidentity symplectic isometry whose displacement on a marked
hyperplane lies in its orthogonal line, the displacement is either exactly
that line, or has dimension two. In the second case the hyperplane's image
is the line. The proof combines orthogonality with the codimension-one
image bound. The final theorems apply this to the literal faithful quotient
action and the actual section centralizer from LowRank.Action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.11(6), final two cases, printed p.855 / PDF p.872.
-/

open Module
namespace LowRankLinear
variable {k A : Type*} [Field k] [AddCommGroup A] [Module k A]


private theorem range_ne_bot (t : A ≃ₗ[k] A) (ht : t ≠ 1) :
    LinearMap.range (t.toLinearMap - LinearMap.id) ≠ ⊥ := by
  intro h
  apply ht
  ext v
  have hz := LinearMap.congr_fun (LinearMap.range_eq_bot.mp h) v
  exact sub_eq_zero.mp hz

private theorem range_le_orthogonal_of_fixed (B : LinearMap.BilinForm k A)
    (t : A ≃ₗ[k] A) (hi : ∀ u v, B (t u) (t v) = B u v)
    (W : Submodule k A) (hW : ∀ w ∈ W, t w = w) :
    LinearMap.range (t.toLinearMap - LinearMap.id) ≤ B.orthogonal W := by
  rintro _ ⟨v, rfl⟩ w hw
  change B w (t v - v) = 0
  rw [map_sub, ← hW w hw, hi, hW w hw, sub_self]

private theorem fixed_of_range_le (B : LinearMap.BilinForm k A)
    (hB : B.Nondegenerate) (t : A ≃ₗ[k] A)
    (hi : ∀ u v, B (t u) (t v) = B u v)
    (L : Submodule k A) (hL : LinearMap.range (t.toLinearMap - LinearMap.id) ≤ L) :
    ∀ w ∈ B.orthogonal L, t w = w := by
  intro w hw
  apply sub_eq_zero.mp
  apply hB.2
  intro u
  obtain ⟨v, rfl⟩ := t.surjective u
  have horth := hw _ (hL (LinearMap.mem_range_self (t.toLinearMap - LinearMap.id) v))
  change B (t v - v) w = 0 at horth
  have he : B (t v) w = B v w := by simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using horth
  simp only [map_sub, hi, he, sub_self]

variable [FiniteDimensional k A]

/-- The two source cases at the end of 12.8.11(6). -/
theorem moved_cases (B : LinearMap.BilinForm k A) (hB : B.Nondegenerate)
    (hBr : B.IsRefl) (L W : Submodule k A) (hL : finrank k L = 1)
    (hW : W = B.orthogonal L) (t : A ≃ₗ[k] A) (ht : t ≠ 1)
    (hi : ∀ u v, B (t u) (t v) = B u v)
    (hm : W.map (t.toLinearMap - LinearMap.id) ≤ L) :
    ((∀ w ∈ W, t w = w) ∧ LinearMap.range (t.toLinearMap - LinearMap.id) = L) ∨
    (W.map (t.toLinearMap - LinearMap.id) = L ∧
      finrank k (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2) := by
  have hcodim : finrank k (A ⧸ W) = 1 := by
    have hdim := W.finrank_quotient_add_finrank
    have hdW : finrank k W = finrank k A - 1 := by
      rw [hW, B.finrank_orthogonal hB, hL]
    have hle := Submodule.finrank_le L
    rw [hL] at hle
    omega
  have hsmall := LinearMap.finrank_range_le_quotient_add_map (t.toLinearMap - LinearMap.id) W
  have hmrank := Submodule.finrank_mono hm
  rw [hL] at hmrank
  rw [hcodim] at hsmall
  have hatom := (Submodule.isAtom_iff_finrank_eq_one).mpr hL
  by_cases hfix : ∀ w ∈ W, t w = w
  · left
    refine ⟨hfix, ?_⟩
    have hle := range_le_orthogonal_of_fixed B t hi W hfix
    rw [hW, B.orthogonal_orthogonal hB hBr] at hle
    exact (hatom.le_iff_eq (range_ne_bot t ht)).mp hle
  · right
    have hne : W.map (t.toLinearMap - LinearMap.id) ≠ ⊥ := by
      intro he
      apply hfix
      intro w hw
      have hz : (t.toLinearMap - (LinearMap.id : A →ₗ[k] A)) w ∈ (⊥ : Submodule k A) :=
        he ▸ Submodule.mem_map_of_mem hw
      exact sub_eq_zero.mp hz
    have heq := (hatom.le_iff_eq hne).mp hm
    refine ⟨heq, ?_⟩
    have hle : L ≤ LinearMap.range (t.toLinearMap - LinearMap.id) :=
      heq ▸ (show W.map (t.toLinearMap - LinearMap.id) ≤ _ from
        fun _ ⟨w, _, he⟩ => ⟨w, he⟩)
    have hlower : 2 ≤ finrank k (LinearMap.range (t.toLinearMap - LinearMap.id)) := by
      by_contra hn
      have he := Submodule.eq_of_le_of_finrank_le hle (by omega)
      apply hfix
      rw [hW]
      exact fixed_of_range_le B hB t hi L he.ge
    omega
end LowRankLinear

public section
open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The faithful linear quotient action preserves the form when the original
H-action does, as in 12.8.8(2). -/
theorem dotLinearAction_preserves (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hi : ∀ (h : F.H) (u v : F.Uhat),
      B (Additive.ofMul (ρ h u)) (Additive.ofMul (ρ h v)) =
        B (Additive.ofMul u) (Additive.ofMul v))
    (x : Hdot F ρ) (u v : Additive F.Uhat) :
    B (dotLinearAction F ρ x u) (dotLinearAction F ρ x v) = B u v := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker x
  exact hi h u.toMul v.toMul

/-- Both final linear cases of 12.8.11(6), on the actual faithful actor.
The line and hyperplane dimensions are deduced from 12.8.8, not assumed.
The existence of a nonidentity element of Xdot₀ remains a separate source step. -/
theorem lowRank_moved_cases (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 F.Uhat] (hn : 2 ≤ n)
    (hc : V ⊓ F.ZU = F.Vi 1) (ρ : F.H →* MulAut F.Uhat) (g : G)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : B.Nondegenerate) (hBa : B.IsAlt)
    (hzero : ∀ u v : F.U,
      B (Additive.ofMul (QuotientGroup.mk' (center F.U) u))
        (Additive.ofMul (QuotientGroup.mk' (center F.U) v)) = 0 ↔ Commute u v)
    (hi : ∀ (h : F.H) (u v : F.Uhat),
      B (Additive.ofMul (ρ h u)) (Additive.ofMul (ρ h v)) =
        B (Additive.ofMul u) (Additive.ofMul v))
    {x : Hdot F ρ} (hx : x ∈ Xdot₀ F ρ g) (hne : x ≠ 1) :
    ((∀ w ∈ hatSpace F F.W, dotLinearAction F ρ x w = w) ∧
      movedSpace F ρ x = hatSpace F (F.Vi 2)) ∨
    ((hatSpace F F.W).map ((dotLinearAction F ρ x).toLinearMap - LinearMap.id) =
        hatSpace F (F.Vi 2) ∧
      finrank (ZMod 2) (movedSpace F ρ x) = 2) := by
  have ht : dotLinearAction F ρ x ≠ 1 := by
    intro he
    apply hne
    exact dotLinearAction_injective F ρ (he.trans (map_one (dotLinearAction F ρ)).symm)
  exact LowRankLinear.moved_cases B hB hBa.isRefl _ _
    (finrank_hatSpace_plane F hn hc) (hatSpace_W_eq_orthogonal F B hzero)
    (dotLinearAction F ρ x) ht (dotLinearAction_preserves F ρ B hi x)
    (moved_W_le_line_of_mem_Xdot₀ F ρ g hx)

/-- Every nonidentity element of the actual section centralizer has moved
rank at most two, and its moved space contains the marked line. -/
theorem lowRank_bound_of_mem_Xdot₀ (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 F.Uhat] (hn : 2 ≤ n)
    (hc : V ⊓ F.ZU = F.Vi 1) (ρ : F.H →* MulAut F.Uhat) (g : G)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : B.Nondegenerate) (hBa : B.IsAlt)
    (hzero : ∀ u v : F.U,
      B (Additive.ofMul (QuotientGroup.mk' (center F.U) u))
        (Additive.ofMul (QuotientGroup.mk' (center F.U) v)) = 0 ↔ Commute u v)
    (hi : ∀ (h : F.H) (u v : F.Uhat),
      B (Additive.ofMul (ρ h u)) (Additive.ofMul (ρ h v)) =
        B (Additive.ofMul u) (Additive.ofMul v))
    {x : Hdot F ρ} (hx : x ∈ Xdot₀ F ρ g) (hne : x ≠ 1) :
    finrank (ZMod 2) (movedSpace F ρ x) ≤ 2 ∧
      hatSpace F (F.Vi 2) ≤ movedSpace F ρ x := by
  rcases lowRank_moved_cases F hn hc ρ g B hB hBa hzero hi hx hne with h | h
  · rw [h.2, finrank_hatSpace_plane F hn hc]
    exact ⟨by decide, le_rfl⟩
  · refine ⟨h.2.le, ?_⟩
    rw [← h.1]
    rintro _ ⟨w, _, he⟩
    exact ⟨w, he⟩

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
