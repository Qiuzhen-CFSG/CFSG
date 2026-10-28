module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinear

/-!
# Cartan data for the field-four conclusion

The source chooses compatible odd Hall subgroups A = D_L and B and, after
5.1.17, the order-three subgroup C = D₃ of A. `LinearFieldCartan` records
these actual subgroups and their orders. It asserts no field-four or
centralization conclusion and no existence theorem for these data.

Once the two cubic branches prove A = B, the Cartan orders give n = 2.
The Hall supplement then identifies N_L(T∩L) with (T∩L)B, which centralizes
Ω₁(Z(T)) because B lies in H. The separate geometry lemma retains the
individual centralizer C_G(z) bound from 5.1.14(2), needed in 5.1.17--23.

Source: Aschbacher--Smith, 5.1.14(2), 5.1.17--20, pp.639--644.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B C : Subgroup G} {n : ℕ}

/-- The genuine compatible Cartans and their cubic subgroup. This is a
construction target for the parity branch, not an assumed book theorem. -/
structure LinearFieldCartan (T : Sylow 2 G) (L H A B C : Subgroup G) (n : ℕ) : Prop
    extends CartanPair T L H A B where
  left_cyclic : IsCyclic A
  left_card : Nat.card A = 2 ^ n - 1
  right_card : Nat.card B = 3
  cubic_le : C ≤ A
  cubic_card : Nat.card C = 3

omit [Finite G] in
/-- Equality of the two source Cartans forces the binary field to have order four. -/
theorem LinearFieldCartan.exponent_eq_two
    (c : LinearFieldCartan T L H A B C n) (hAB : A = B) : n = 2 := by
  have hcard : Nat.card A = 3 := by simpa only [hAB] using c.right_card
  have he : 2 ^ n - 1 = 3 := c.left_card.symm.trans hcard
  have hp : 0 < 2 ^ n := by positivity
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  norm_num
  omega

/-- The entire Borel centralizes the Sylow omega-center when its odd
Cartan lies in H. This uses the full Hall condition, not just odd order. -/
theorem CartanPair.borel_le_omegaCentralizer_of_left_le
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hHC : H ≤ omegaCentralizer T) (hAH : A ≤ H) :
    localBorel T L ≤ omegaCentralizer T := by
  rw [← c.left_sup_intersection hTL]
  exact sup_le (inf_le_left.trans sylow_le_omegaCentralizer) (hAH.trans hHC)

/-- The surviving Cartan equality supplies both inputs of the selected-module
fixed-point consumer. Neither input is assumed separately. -/
theorem LinearFieldCartan.field_four_and_borel
    (c : LinearFieldCartan T L H A B C n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hHC : H ≤ omegaCentralizer T) (hAB : A = B) :
    n = 2 ∧ localBorel T L ≤ omegaCentralizer T := by
  refine ⟨c.exponent_eq_two hAB, c.toCartanPair.borel_le_omegaCentralizer_of_left_le
    hTL hHC ?_⟩
  rw [hAB]
  exact c.right_le.trans inf_le_right

/-- Every nonidentity point of the actual Sylow omega-center has centralizer
inside N_G(O²(H)). This strengthens the whole-omega centralizer containment
to the literal pointwise assertion used later in the source argument. -/
theorem point_centralizer_le_residual_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    {z : G} (hz : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hne : z ≠ 1) : centralizer ({z} : Set G) ≤ normalizer (residual H : Set G) := by
  obtain ⟨hc, hu⟩ := residual_geometry_of_maximal_nonfaithful hG hH hK hnf
  have hHC := (residual_le_omegaCentralizer_iff hH.2).mp hc
  have htwo := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1
  obtain ⟨N, hCN, hN⟩ := Finite.exists_le_maximal
    (isTwoLocal_involution_centralizer (orderOf_eq_prime htwo hne))
  have hHN : H ≤ N := hHC.trans
    ((centralizer_le (Set.singleton_subset_iff.mpr hz)).trans hCN)
  exact (hu N hN hHN) ▸ hCN

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
