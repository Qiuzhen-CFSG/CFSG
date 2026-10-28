module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry

/-!
# The marked square-field reduction for Proposition 16.5

An involutory automorphism fixing the marked pair but acting nontrivially on
its generated root excludes the Suzuki and unitary cases. In the linear case
an inner automorphism fixing both marks is trivial, so the automorphism is
outer. Its fixed group and marked torus action therefore have the same
square-root field parameter. The source consumer derives nontriviality from
Lemma 16.4(a), rather than assuming the resulting linear recognition.

Source: GLS IV, Chapter 2, Proposition 16.5, its first model reduction.
-/

noncomputable section
namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup PFAppendixIII
open _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

/-- Nontrivial action on the literal marked root forces the square-field
linear model and the actual field action on its two-point torus. -/
public theorem source16_square_field_of_nontrivial_root_action
    (hn : 2 ≤ n) (hperfect : commutator G = ⊤)
    (hodd : Odd (Nat.card (center G)))
    (hmodel : IsSimpleBenderGroupAtExponent n (G ⧸ center G))
    (P : Sylow 2 G) {z t : G} (hzP : z ∈ (P : Subgroup G))
    (hz : IsInvolution z) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set G))
    (a : MulAut G) (ha : a ^ 2 = 1) (haz : a z = z) (hat : a t = t)
    (haB : (normalizer (P : Set G)).map a.toMonoidHom = normalizer (P : Set G))
    (hne : ¬ rootGenerated (P : Subgroup G) t ≤ a.fixedSubgroup) :
    ∃ _e : G ≃* PSL2BinaryMatrixGroup n,
      (¬ ∃ g : G, a = MulAut.conj g) ∧
      ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
        Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m) ∧
        (∀ x ∈ twoPoint (normalizer (P : Set G)) t, a x = x ^ (2 ^ m)) ∧
        ∀ p : ℕ, p.Prime → p ∣ 2 ^ m + 1 →
          ∀ x ∈ (twoPoint (normalizer (P : Set G)) t).pCoreIn p, a x = x⁻¹ := by
  have ha1 : a ≠ 1 := by
    intro he
    apply hne
    intro x _
    rw [MulAut.mem_fixedSubgroup, he, MulAut.one_apply]
  rcases oddCentralCover_root_cases hn hperfect hodd hmodel P z t hzP hz ht htB with
    ⟨_, ⟨e⟩⟩ | ⟨_, m, hm, _, ⟨e⟩⟩ |
      ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, hquotient, hroot, hfix⟩
  · have houter : ¬ ∃ g : G, a = MulAut.conj g := fun hinner =>
      ha1 (LinearGeometry.inner_fixing_eq_one e P hz hzP htB a hinner haz hat)
    exact ⟨e, houter, linear_outer_marked_fixed_and_pCore hn e P t ht htB a ha houter haB hat⟩
  · exact False.elim (ha1 (suzuki_automorphism_eq_one_of_fixed_pair hm e P a ha hzP hz htB haz hat))
  · exact False.elim (hne (hfix a ha haz hat))

end BenderSuzuki.ZD.RankOneModelGeometry
