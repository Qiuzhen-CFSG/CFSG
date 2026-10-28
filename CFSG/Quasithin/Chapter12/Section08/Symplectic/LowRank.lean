module

public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank.Linear
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank.Nontrivial

/-!
# The low-rank witness in Lemma 12.8.11(6)

On the literal U/Z(U), every nonidentity element of the section centralizer
Xdot₀ has moved dimension at most two and its moved space contains V₂hat.
We prove both cases of the source argument: a fixed hyperplane gives exactly
the moved line; otherwise the hyperplane has that line as its image and the
whole moved space has dimension exactly two. The line dimension and the
hyperplane identification follow from the earlier center intersection and
commutator form.

The strict fixed-space inequality gives Xdot₀≠1 by the group-theoretic
argument in LowRank.Nontrivial. Combining it with the linear cases constructs
the requested nonidentity element of the actual X-image. The fixed-lift
placement, internal interchange in I₂ and nontrivial section centralizer are
proved, rather than assumed by the assembled witness theorem.

The explicit inputs are the earlier 12.8.4–10 conclusions on the original
marked groups, action and form, together with 12.8.11(4). The latter is
constructed independently in Symplectic.Transvections; all premise discharge
and the G.11 classification application remain with the Symplectic assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.11(6), printed pp.854–855 / PDF pp.871–872.
-/

public section
open Subgroup Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Witness extraction from a nontrivial literal section centralizer.
The source implication discharging this premise is assembled below. -/
theorem exists_lowRank_of_Xdot₀_ne_bot (F : InvariantFlag T V n) [Finite G]
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
    (hkernel : Xdot₀ F ρ g ≠ ⊥) :
    ∃ x ∈ dotImage F ρ (F.X g), x ≠ 1 ∧
      finrank (ZMod 2) (movedSpace F ρ x) ≤ 2 ∧
      hatSpace F (F.Vi 2) ≤ movedSpace F ρ x := by
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hkernel
  have hne : (x : Hdot F ρ) ≠ 1 := fun h => hx (Subtype.ext h)
  exact ⟨x, Xdot₀_le F ρ g x.property, hne,
    lowRank_bound_of_mem_Xdot₀ F hn hc ρ g B hB hBa hzero hi x.property hne⟩

/-- The conditional witness assertion of 12.8.11(6), with nontriviality of
the section centralizer discharged.

The earlier inputs are the nonabelian two-group and Frattini line (12.8.4),
the invariant commutator form and center intersection (12.8.8), the full
plane action, index, literal commutator surjectivity and exact action kernel
(12.8.9), and the center intersection (12.8.10(1)). The sibling fixed-space
equality is 12.8.11(4). In particular `hmove` is the representative form of
the source equality `[X/E,u] = W/E`, for each `u ∈ U − W`.

Every group, quotient map and action is the marked one. The line and
hyperplane geometry and both moved-space cases are proved in LowRank.Linear;
LowRank.Nontrivial proves the internal conjugation and fixed-lift argument.
No nontriviality or low-rank witness is included among the premises. -/
theorem exists_lowRank_of_fixedSpace_lt (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 (F.Vi 2)]
    [IsElementaryAbelian 2 F.Uhat] (hn : 2 ≤ n)
    (hUnon : ¬ IsMulCommutative F.U) (hUtwo : IsPGroup 2 F.U)
    (hPhi : (frattini F.U).map F.U.subtype = F.Vi 1)
    (hc : V ⊓ F.ZU = F.Vi 1)
    (L : Subgroup G) (g : G) (hg : g ∈ F.Gi 2)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (hI : F.I₂ L ≤ F.Gi 2)
    (hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hI)))
    (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (hkernel : F.X g ⊓ ρ.ker.map F.H.subtype = F.E g)
    (hindex : F.W.relIndex F.U = 2)
    (hmove : ∀ u ∈ F.U, u ∉ F.W → ∀ w ∈ F.W,
      ∃ x ∈ F.X g, ∃ e ∈ F.E g, ⁅x, u⁆ * e = w)
    (hcenter : F.ZU ⊓ conjugate F.U g =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : B.Nondegenerate) (hBa : B.IsAlt)
    (hzero : ∀ u v : F.U,
      B (Additive.ofMul (QuotientGroup.mk' (center F.U) u))
        (Additive.ofMul (QuotientGroup.mk' (center F.U) v)) = 0 ↔ Commute u v)
    (hi : ∀ (h : F.H) (u v : F.Uhat),
      B (Additive.ofMul (ρ h u)) (Additive.ofMul (ρ h v)) =
        B (Additive.ofMul u) (Additive.ofMul v))
    (hfour : hatSpace F (F.E g) ⊓ XfixedSpace F ρ g = hatSpace F (F.Vi 2))
    (hstrict : hatSpace F (F.Vi 2) < XfixedSpace F ρ g) :
    ∃ x ∈ dotImage F ρ (F.X g), x ≠ 1 ∧
      finrank (ZMod 2) (movedSpace F ρ x) ≤ 2 ∧
      hatSpace F (F.Vi 2) ≤ movedSpace F ρ x := by
  have hnontrivial := Xdot₀_ne_bot_of_fixedSpace_lt F hn hUnon hUtwo hPhi
    L g hg hdis z hz hne hI hfull ρ hρ hkernel hindex hmove hcenter hfour hstrict
  exact exists_lowRank_of_Xdot₀_ne_bot F hn hc ρ g B hB hBa hzero hi hnontrivial

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
