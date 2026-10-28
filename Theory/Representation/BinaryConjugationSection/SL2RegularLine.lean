module
public import Theory.GroupAction.RegularNonidentity
public import Theory.Representation.BinaryConjugationSection.SL2OddCentralizers

/-!
# Fixed subgroups on natural Cartan lines

An odd subgroup of order q−1 acts freely on every nonzero vector of a
natural SL₂ section. On an invariant subgroup of order q with trivial
intersection with the coordinate kernel, the action is regular. Any
commuting actor therefore fixes either the whole line or only its identity.
This is the line-action step in DGS (1985), 5.1 and 9.10(4).
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G]

theorem natural_line_fixed_dichotomy
    (H A Z₀ : Subgroup G) {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (q : H →* SL(2,F)) (hp : IsPGroup 2 q.ker)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection H A Z₀ (σ.comp q))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z))
    (K R T : Subgroup G) [Finite K] [Finite R]
    (hKH : K ≤ H) (hodd : Odd (Nat.card K))
    (hRA : R ≤ A) (hRZ : Disjoint R Z₀)
    (hcard : Nat.card K + 1 = Nat.card R)
    (hn : K ≤ normalizer (R : Set G)) (hKT : K ≤ centralizer (T : Set G)) :
    R ⊓ centralizer (T : Set G) = ⊥ ∨ R ≤ centralizer (T : Set G) := by
  apply inf_centralizer_eq_bot_or_le_of_regular_card K R T hcard hn hKT
  intro k hk r hr hr1 hkr
  by_contra hk1
  have hDK : zpowers k ≤ K := zpowers_le.mpr hk
  have hDne : zpowers k ≠ ⊥ := by
    intro he
    exact hk1 (show k ∈ (⊥ : Subgroup G) from he ▸ mem_zpowers k)
  have hDodd : Odd (Nat.card (zpowers k)) := hodd.of_dvd_nat (card_dvd_of_le hDK)
  have hrc : r ∈ centralizer (zpowers k : Set G) := by
    have hkc : k ∈ centralizer ({r} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hkr)
    have hz : zpowers k ≤ centralizer ({r} : Set G) := zpowers_le.mpr hkc
    intro y hy
    exact (mem_centralizer_singleton_iff.mp (hz hy))
  have hrZ := natural_odd_centralizer_le_kernel H A Z₀ q hp σ c E hE
    (zpowers k) (hDK.trans hKH) hDodd hDne ⟨hRA hr,hrc⟩
  exact hr1 (disjoint_def.mp hRZ hr hrZ)
end Representation.BinaryConjugationSection
