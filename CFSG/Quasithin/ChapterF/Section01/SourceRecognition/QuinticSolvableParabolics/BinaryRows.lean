module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.ReducedSylow

/-!
# Binary reduced rows in the quintic branch

The reduced catalogue has three binary constructors.  The two constructors
whose quotient is attached to a local factor or to its join are already
enough to finish the row: on the right they give a solvable right parabolic,
while on the left they would force the original quintic quotient to have
order six.  The full-parabolic constructor gives the same conclusion on the
right.  These are literal quotient transports; no type-only recognition or
ambient Sylow assumption is used.

The remaining left full-parabolic binary clause belongs to the exhaustive DGS
source selection.  It is deliberately not identified with a marked model in
this module.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source
open SuzukiContainment

variable {G : Type*} [Group G] {K R S : Subgroup G}

private theorem no_quintic_psl2_quotient
    (hc : Nat.card (K ⧸ pCore 2 K) = 10 ∨ Nat.card (K ⧸ pCore 2 K) = 20)
    (he : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 2) : False := by
  rcases he with ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hF)
  have ho := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1), mul_one, hF, ← Nat.card_congr e.toEquiv] at ho
  rcases hc with hc | hc <;> norm_num [hc] at ho

private theorem solvable_of_psl2_two {X : Type*} [Group X]
    (he : ClassicalGroup.IsPSL X 2 2) : Group.IsSolvable X := by
  rcases he with ⟨F,_,_,hF,⟨e⟩⟩
  let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
  exact Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective

/-- A binary local row on the right makes the right parabolic solvable. -/
theorem HypothesisF11.quintic_solvable_of_binary_local_right
    (h : HypothesisF11 ![K,R] S)
    (he : ClassicalGroup.IsPSL ((![K,R] (1 : Fin 2)) ⧸
      pCore 2 (![K,R] (1 : Fin 2))) 2 2) :
    Group.IsSolvable (parabolic ![K,R] S 1) := by
  apply (h.parabolic_solvable_iff_local_quotient 1).mpr
  simpa only [Matrix.cons_val_one] using solvable_of_psl2_two he

/-- A binary local row on the quintic endpoint is impossible. -/
theorem HypothesisF11.quintic_no_binary_local_left
    (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K)
    (hi : S.relIndex K = 5)
    (he : ClassicalGroup.IsPSL ((![K,R] (0 : Fin 2)) ⧸
      pCore 2 (![K,R] (0 : Fin 2))) 2 2) : False := by
  have he' : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 2 := by
    change ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 2 at he
    exact he
  exact no_quintic_psl2_quotient (h.quintic_quotient_card hSK hi) he'

/-- A binary join row on the right is a binary full-parabolic row after the
quintic reduced-Sylow identity. -/
theorem HypothesisF11.quintic_solvable_of_binary_join_right
    (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K) (hi : S.relIndex K = 5)
    (he : ClassicalGroup.IsPSL
      ((![K,R] (1 : Fin 2) ⊔ reducedSylow ![K,R] S : Subgroup G) ⧸
        pCore 2 (![K,R] (1 : Fin 2) ⊔ reducedSylow ![K,R] S : Subgroup G)) 2 2) :
    Group.IsSolvable (parabolic ![K,R] S 1) := by
  change ClassicalGroup.IsPSL
    ((R ⊔ reducedSylow (![K,R]) S : Subgroup G) ⧸
      pCore 2 (R ⊔ reducedSylow (![K,R]) S : Subgroup G)) 2 2 at he
  rw [h.quintic_reducedSylow_eq hSK,
    ← h.quintic_right_parabolic hSK hi] at he
  exact h.parabolic_solvable_of_small_ree_quotient 1 (Or.inl he)

/-- A binary join row on the quintic endpoint is impossible: its join is `K`,
so its quotient has order six, contradicting the D₁₀/Sz(2) alternatives. -/
theorem HypothesisF11.quintic_no_binary_join_left
    (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K)
    (hi : S.relIndex K = 5)
    (he : ClassicalGroup.IsPSL
      ((![K,R] (0 : Fin 2) ⊔ reducedSylow ![K,R] S : Subgroup G) ⧸
        pCore 2 (![K,R] (0 : Fin 2) ⊔ reducedSylow ![K,R] S : Subgroup G)) 2 2) : False := by
  change ClassicalGroup.IsPSL
    ((K ⊔ reducedSylow (![K,R]) S : Subgroup G) ⧸
      pCore 2 (K ⊔ reducedSylow (![K,R]) S : Subgroup G)) 2 2 at he
  rw [h.quintic_reducedSylow_eq hSK, sup_eq_left.mpr hSK] at he
  exact no_quintic_psl2_quotient (h.quintic_quotient_card hSK hi) he

/-- A binary full-parabolic row on the right directly gives solvability. -/
theorem HypothesisF11.quintic_solvable_of_binary_parabolic_right
    (h : HypothesisF11 ![K,R] S)
    (he : ClassicalGroup.IsPSL
      (parabolic ![K,R] S 1 ⧸ pCore 2 (parabolic ![K,R] S 1)) 2 2) :
    Group.IsSolvable (parabolic ![K,R] S 1) :=
  h.parabolic_solvable_of_small_ree_quotient 1 (Or.inl he)

end CFSG.Quasithin.ChapterF.Source
