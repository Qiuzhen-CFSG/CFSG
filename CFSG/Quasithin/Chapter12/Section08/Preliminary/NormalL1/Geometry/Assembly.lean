module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Geometry.LinearGeneration

/-!
# The geometric implication in the normal-L₁ branch

The actual binary point-residual calculation supplies generation by the
N_L(Vᵢ)-conjugates of L₁. The natural action lifts this through O₂(L),
using O²(L)=L, and gives the full action on Vᵢ and the literal ambient
factorization Gᵢ=C_G(Vᵢ)N_L(Vᵢ). Relative normality of L₁ in G₁ then
forces Gᵢ≤M. The earlier TI and transitivity results give seed-normalizer
control, uniqueness of the conjugate containing Vᵢ, and the rank bound.

`normal_geometry` discharges the concrete generation premise of
`normal_geometry_of_linear_generation`. Its explicit earlier inputs are
the genuine natural action from 12.8.1/12.8.3(1), O²(L)=L from the source
setup, Notation 12.2.5(2), Lemma 12.2.6, and Lemma 12.8.3(2,3).
Their construction remains with the earlier-source assembly.
No generation or geometric conclusion is a premise. The full subspace
action is exported as `normalizer_full_action`. The exceptional solvable
residual convention for L₂,L₃ in dimension five is unchanged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.5(2), printed p.850 (PDF p.867).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section08.NormalGeometry
open Subgroup
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {V L M : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 V]

/-- The full geometric implication of 12.8.5(2), with the natural-action
generation proved. The earlier source inputs are explicit: `hTI` is
12.2.6, `hNV` is Notation 12.2.5(2), and `hplanes`, `htrans` are
12.8.3(2,3). Normality is inside G₁, and all conjugates are right conjugates. -/
theorem normal_geometry (F : InvariantFlag T V n)
    (d : NaturalAction L V) (hn : 2 < n)
    (hL : pResidual 2 L = ⊤) (hM : M = normalizer (L : Set G))
    (hL1 : ((F.Li L 1).subgroupOf F.H).Normal)
    (hTI : ∀ g ∈ M, V ⊓ conjugate V g = ⊥ ∨ conjugate V g = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (hplanes : ∀ A : Subgroup G, A ≤ V → Nat.card A = 4 →
      ∃ l ∈ L, conjugate A l = F.Vi 2)
    (htrans : ∀ i, 1 < i → i < n → ∀ g : G, F.Vi i ≤ conjugate V g →
      ∃ k ∈ F.Gi i, conjugate V g = conjugate V k) :
    (∀ i, 1 < i → i < n →
      conjugateSpanBy (F.Li L 1) (L ⊓ F.Gi i) = L ∧
      (F.Gi i : Set G) = (centralizer (F.Vi i : Set G) : Set G) *
        (L ⊓ F.Gi i : Subgroup G) ∧
      F.Gi i ≤ M ∧ F.Gi i ≤ seedNormalizer M V ∧
      ∀ g : G, F.Vi i ≤ conjugate V g → conjugate V g = V) ∧
    ∀ g : G, g ∉ seedNormalizer M V →
      primeRank 2 (V ⊓ conjugate V g : Subgroup G) ≤ 1 :=
  normal_geometry_of_linear_generation F d hn hL hM hL1 hTI hNV hplanes htrans
    (flag_linear_generation F hn)

end CFSG.Quasithin.Chapter12.Section08.NormalGeometry
