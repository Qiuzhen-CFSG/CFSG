module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import Theory.GroupTheory.SylowKernelCore

/-!
# Marked Suzuki Borels and their order-three action kernel

The relevant detecting quotient is B/O₂(B). The predicate below says
that its pointwise action detects automorphisms whose cube is one; it
does not assume pointwise fixation of B. The marked model is one or two
actual Suzuki matrix factors, with the whole Borel carried to the product
of the concrete root--torus Borels. It retains the two-component case.

Transport and restriction connect this intrinsic action calculation to
literal ambient conjugation. No model detection theorem or existence of
a marked Borel is asserted here; both must be constructed for 15.3.34.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.34, printed p.1134. Concrete Borels are from F.1.3(1), pp.259--260.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion

/-- The action on B/O₂(B) detects automorphisms whose cube is one. -/
def DetectsThreeAutomorphisms {K : Type*} [Group K] (B : Subgroup K) : Prop :=
  ∀ α : MulAut K, α ^ 3 = 1 →
    (∀ b ∈ B, α b * b⁻¹ ∈ B.pCoreIn 2) → α = 1

/-- A Borel in one or two actual Suzuki factors, with its marked equivalence. -/
def IsSuzukiOrbitBorel {K : Type*} [Group K] (B : Subgroup K) : Prop :=
  ∃ m n : ℕ, 0 < m ∧ (n = 1 ∨ n = 2) ∧
    ∃ e : K ≃* (Fin n → BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m),
      B.map e.toMonoidHom = Subgroup.pi Set.univ
        (fun _ => BenderSuzuki.MatrixGroups.SuzukiBorelSubgroup m)

variable {G K : Type*} [Group G] [Group K]

theorem DetectsThreeAutomorphisms.of_mulEquiv {B : Subgroup G} {D : Subgroup K}
    (hD : DetectsThreeAutomorphisms D) (e : G ≃* K)
    (hB : B.map e.toMonoidHom = D) : DetectsThreeAutomorphisms B := by
  intro α hα hcomm
  have hβ : MulAut.congr e α = 1 := by
    apply hD
    · rw [← map_pow, hα, map_one]
    · intro d hd
      obtain ⟨b, hb, rfl⟩ := (show d ∈ B.map e.toMonoidHom from hB.symm ▸ hd)
      have hh := Subgroup.mem_map_of_mem e.toMonoidHom (hcomm b hb)
      rw [map_pCoreIn_of_injective 2 B e.toMonoidHom e.injective, hB] at hh
      simpa [MulAut.congr, MulEquiv.trans_apply] using hh
  exact (MulAut.congr e).injective (hβ.trans (map_one (MulAut.congr e)).symm)

/-- Literal ambient conjugation inherits the marked Borel detector. -/
theorem centralizes_of_borel_detector {H B : Subgroup G} (hBH : B ≤ H)
    (hD : DetectsThreeAutomorphisms (B.subgroupOf H))
    {y : G} (hy : y ∈ normalizer (H : Set G)) (hy3 : orderOf y = 3)
    (hcomm : ∀ b ∈ B, ⁅y, b⁆ ∈ B.pCoreIn 2) :
    y ∈ centralizer (H : Set G) := by
  let t : normalizer (H : Set G) := ⟨y, hy⟩
  let α := H.normalizerMonoidHom t
  have ht : t ^ 3 = 1 := Subtype.ext (by
    change y ^ 3 = 1
    rw [← hy3]
    exact pow_orderOf_eq_one y)
  have hα : α ^ 3 = 1 := by
    dsimp [α]
    rw [← map_pow, ht, map_one]
  have hαone := hD α hα (by
    intro b hb
    have he : ((B.subgroupOf H).pCoreIn 2).map H.subtype = B.pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
        map_subgroupOf_eq_of_le hBH]
    have hh : (α b * b⁻¹ : H).val ∈ B.pCoreIn 2 := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, α,
        Subgroup.normalizerMonoidHom_apply_apply_coe, t, commutatorElement_def] using
          hcomm b hb
    rw [← he] at hh
    obtain ⟨a, ha, hae⟩ := hh
    exact (Subtype.ext hae : a = α b * b⁻¹) ▸ ha)
  rw [mem_centralizer_iff]
  intro x hx
  have hh := congrArg (fun β : MulAut H => (β ⟨x, hx⟩ : G)) hαone
  change y * x * y⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion
