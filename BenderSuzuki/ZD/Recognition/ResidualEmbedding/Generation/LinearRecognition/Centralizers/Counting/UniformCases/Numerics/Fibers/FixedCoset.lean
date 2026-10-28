module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Inputs
public import Theory.GroupAction.FixedPointCentralizerCount

/-!
# The fixed-coset ratio for the actor class inside M

The general transporter count is applied to the literal action on G/M.
Its point stabilizer is M and its ambient orbit is all of G/M. The resulting
multiplied identity supplies the centralizer factor in Lemma 12.8(b), while
retaining the actual ambient conjugacy-class intersection with M.
Source: GLS4, Chapter 2, proof of Lemma 12.8, `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
/-- The fixed-coset ratio with the literal ambient conjugacy class inside M. -/
public theorem residual_conjugates_card_mul_centralizer (v : G) :
    Nat.card {a : M // IsConj v (a : G)} * Nat.card (centralizer ({v} : Set G)) =
      Nat.card M * Nat.card {beta : G ⧸ M // v • beta = beta} := by
  let alpha : G ⧸ M := QuotientGroup.mk 1
  have hc := MulAction.centralizer_card_mul_conj_stabilizer alpha v
  have hs : MulAction.stabilizer G alpha = M := baseCoset_stabilizer M
  rw [hs] at hc
  have hi : Nat.card {a : M // IsConj (a : G) v} =
      Nat.card {a : M // IsConj v (a : G)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => isConj_comm)
  have ho : Nat.card {b : MulAction.orbit G alpha // v • b.val = b.val} =
      Nat.card {beta : G ⧸ M // v • beta = beta} := by
    apply Nat.card_congr
    exact {
      toFun := fun b => ⟨b.val.val, b.property⟩
      invFun := fun b => ⟨⟨b.val, by
        obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective b.val
        exact MulAction.mem_orbit_iff.mpr ⟨g, by
          change (QuotientGroup.mk (g * 1) : G ⧸ M) = b.val
          simpa only [mul_one] using hg⟩⟩, b.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hi, ho, mul_comm (Nat.card (centralizer ({v} : Set G)))] at hc
  exact hc
end BenderSuzuki.ZD
