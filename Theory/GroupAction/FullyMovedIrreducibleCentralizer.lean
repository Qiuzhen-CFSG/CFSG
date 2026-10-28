module

public import Theory.GroupAction.PPerfectFixedCentralizer
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Two-groups fixing a fully moved irreducible section

Let B be two-perfect and E an elementary binary group with E = [E,B].
Suppose E/C_E(B) is irreducible. A two-group Q normalized by B and
normalizing E centralizes E whenever the two actions commute on E.
Indeed C_E(Q) C_E(B) is either C_E(B) or E. In the first case Thompson's
commuting fixed-point lemma makes B centralize E; in the second case full
movement gives E = [C_E(Q),B], which Q fixes.

This is the fixed-point argument of Aschbacher–Smith A.1.41 and C.1.11,
printed pp.31,124, applied directly to a chosen section rather than an
intrinsic block layer. Its native J₄ first-centralizer consumer is in the
original point-component inspection of 10.2.9, printed pp.750–751.
-/

public section
open Subgroup
namespace Theory.GroupAction
variable {G : Type*} [Group G] [Finite G]

/-- Commuting two-group action fixes the entire fully moved section. -/
theorem centralizes_fully_moved_irreducible_section
    (B Q E : Subgroup G) (hB : IsPPerfect 2 B) (hQ : IsPGroup 2 Q)
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B)
    (hBQ : B ≤ normalizer (Q : Set G))
    (hQE : Q ≤ normalizer (E : Set G))
    (hcomm : ⁅Q,B⁆ ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E)
    (hirr : ∀ N : Subgroup G, E ⊓ centralizer (B : Set G) ≤ N → N ≤ E →
      B ≤ normalizer (N : Set G) → N = E ⊓ centralizer (B : Set G) ∨ N = E) :
    Q ≤ centralizer (E : Set G) := by
  let := hE
  let W := E ⊓ centralizer (Q : Set G)
  let Z := E ⊓ centralizer (B : Set G)
  have hBE : B ≤ normalizer (E : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hmove.le
  have hBW : B ≤ normalizer (W : Set G) :=
    (le_inf hBE (hBQ.trans (normalizer_le_normalizer_centralizer Q))).trans
      inf_normalizer_le_normalizer_inf
  have hBZ : B ≤ normalizer (Z : Set G) :=
    (le_inf hBE (B.le_normalizer.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf
  have hBWZ : B ≤ normalizer (↑(W ⊔ Z : Subgroup G) : Set G) :=
    (le_inf hBW hBZ).trans (W.normalizer_inf_normalizer_le_normalizer_sup Z)
  rcases hirr (W ⊔ Z) le_sup_right (sup_le inf_le_left inf_le_left) hBWZ with hz | he
  · have hWC : W ≤ centralizer (B : Set G) :=
      (le_sup_left.trans hz.le).trans inf_le_right
    have hzero : ⁅E,B⁆ = ⊥ := hB.centralizes_of_commuting_fixed B Q E hQ
      hBE hQE hcomm (commutator_eq_bot_iff_le_centralizer.mpr hWC)
    have hEzero : E = ⊥ := hmove.symm.trans hzero
    intro q _ e he
    have he1 : e = 1 := mem_bot.mp (hEzero ▸ he)
    simp only [he1,mul_one,one_mul]
  · have hZW : ⁅Z,B⁆ ≤ W :=
      (commutator_eq_bot_iff_le_centralizer.mpr (show Z ≤ centralizer (B : Set G) from
        inf_le_right)).le.trans bot_le
    have hjoin : ⁅W ⊔ Z,B⁆ ≤ W := by
      apply (le_commutatorPreimage_iff (normalizer (W : Set G)) B W (W ⊔ Z) le_rfl).mp
        (sup_le
          (le_commutatorPreimage W.le_normalizer
            (le_normalizer_iff_commutator_le_left.mp hBW))
          (le_commutatorPreimage
            (((show Z ≤ centralizer (B : Set G) from inf_le_right).trans
              (centralizer_le (show W ≤ B from inf_le_left.trans hEB))).trans
                (Subgroup.centralizer_le_normalizer _)) hZW)) |>.2
    have hEW : E ≤ W := hmove.symm.le.trans (he ▸ hjoin)
    exact le_centralizer_iff.mp (hEW.trans inf_le_right)

end Theory.GroupAction
