module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.Assembly
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

/-!
# The order-four Sylow refinement

Both remaining exceptional carriers in the complete Theorem C sieve have
order divisible by eight. A Sylow subgroup of order at most four therefore
leaves only the odd prime-field PSL2 model. This is the source sieve used
by the quasisimple branch of F.6.18(4).

Source: Aschbacher--Smith F.6.17--18, printed pp.309--310.
-/

public section
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

/-- The literal Theorem C list with a small elementary Sylow of order at
most four has no J1 or binary PSL2 exception. -/
theorem prime_psl2_of_theoremC_small_elementary_sylow
    (P : Sylow 2 G) [IsElementaryAbelian 2 P] (hP : Nat.card P ≤ 4)
    (hns : ¬ Group.IsSolvable G) (hm : ChapterA.Section02.IsTheoremCModel G) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      ClassicalGroup.IsPSL G 2 p := by
  have hn8 : ¬ 8 ∣ Nat.card G := by
    intro hd
    have h := P.pow_dvd_card_of_pow_dvd_card (n := 3) hd
    have hp := Nat.le_of_dvd (Nat.card_pos (α := P)) h
    omega
  rcases theoremC_model_of_small_elementary_sylow P (by omega) hns hm with hm | hm | hm
  · exact hm
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) (by
      simpa [Nat.card_eq_fintype_card] using hF)
    have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
    rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1), mul_one, hF] at hc
    apply (hn8 _).elim
    rw [Nat.card_congr e.toEquiv, hc]
    norm_num
  · obtain ⟨e⟩ := hm
    apply (hn8 _).elim
    rw [Nat.card_congr e.toEquiv, Janko1.card_model]
    norm_num

end CFSG.Quasithin.ChapterF.SourceAssembly
