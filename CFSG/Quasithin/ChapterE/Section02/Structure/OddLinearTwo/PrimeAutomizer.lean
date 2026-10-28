module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeGeometry
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.AutomizerGeometry
public import GorensteinWalter.PSL2Center

/-!
# The actual prime-field automizer bound in E.2.2

The marked maximal overgroup is an involution centralizer. All involutions
of the actual PSL₂ component fuse, and a Klein four in its Sylow intersection
provides a different involution there. The small-Sylow fusion obstruction
forces |T|>8. Since O₂(H)=1, the centerless normal Sylow supplement has trivial
centralizer, so its actual T-automizer has that same order.

Source: Aschbacher–Smith E.2.2(2c), printed pp.215–216, for p > 9.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure

/-- The source Sylow and its literal conjugation image both have order greater than eight. -/
theorem prime_linear_source_automizer_bound {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    8 < Nat.card T ∧
      8 < Nat.card ((T : Subgroup H).map (MulAut.conjNormal : H →* MulAut K)) := by
  obtain ⟨t, ht, htT, hfix, hM, _⟩ := prime_linear_source_centralizer T hP K hgen ho hF hp eK
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, ho, by decide, by simpa using hF⟩
  let S' := S.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨m, hm, ⟨d⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd S'
  let dS : S ≃* DihedralGroup (2 ^ m) :=
    ((S : Subgroup K).equivMapOfInjective eK.toMonoidHom eK.injective).trans d
  obtain ⟨V, hVS, hV⟩ := GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (S : Subgroup K) hm dS
  let := hV
  have hex : ∃ y : K, y ∈ V ∧ orderOf y = 2 ∧ y ≠ t := by
    by_contra! hno
    have hVt : V ≤ zpowers t := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]; exact one_mem _
      have hy2 : y ^ 2 = 1 := by
        rw [pow_two]
        exact congrArg (fun v : V => (v : K)) (IsKleinFour.mul_self (⟨y, hy⟩ : V))
      rw [hno y hy (orderOf_eq_prime hy2 hy1)]
      exact mem_zpowers t
    have hc := card_le_of_le hVt
    rw [hV.card_four, Nat.card_zpowers, orderOf_eq_prime ht.2 ht.1] at hc
    omega
  obtain ⟨y, hy, hyo, hyt⟩ := hex
  have ht' : GorensteinWalter.IsInvolution (eK t) :=
    (orderOf_eq_prime_iff.mp ((eK.orderOf_eq t).trans (orderOf_eq_prime ht.2 ht.1))).symm
  have hy' : GorensteinWalter.IsInvolution (eK y) :=
    (orderOf_eq_prime_iff.mp ((eK.orderOf_eq y).trans hyo)).symm
  obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power
    F hodd (eK t) (eK y) ht' hy'
  have hconj : eK.symm g * t * (eK.symm g)⁻¹ = y := by
    apply eK.injective
    simpa only [map_mul, map_inv, eK.apply_symm_apply] using hg
  have hlarge : 8 < Nat.card T := by
    apply eight_lt_sylow_card_of_max_centralizer T hP hO (t : H)
      ((orderOf_injective K.subtype K.subtype_injective t).trans (orderOf_eq_prime ht.2 ht.1)) htT
    · intro a ha
      exact mem_centralizer_singleton_iff.mp (hfix ha)
    · exact hM
    · refine ⟨(eK.symm g : H), ?_, ?_⟩
      all_goals
        have hc : (eK.symm g : H) * (t : H) * (eK.symm g : H)⁻¹ = (y : H) :=
          congrArg (fun x : K => (x : H)) hconj
        rw [hc]
      · exact show y ∈ (T : Subgroup H).subgroupOf K from hS ▸ hVS hy
      · exact fun he => hyt (Subtype.ext he)
  have hZ : center K = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    have hcent : eK k ∈ center (PSL2MatrixGroup F) := (centerCongr eK ⟨k, hk⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at hcent
    exact mem_bot.mpr (eK.injective (by simpa only [map_one] using hcent))
  have hC := centralizer_eq_bot_of_centerless_sylow_supplement T K hgen hZ hO
  have hfaith := MulAut.conjNormal_injective_of_centralizer_eq_bot K hC
  refine ⟨hlarge, ?_⟩
  rw [card_map_of_injective hfaith]
  exact hlarge


/-- All local conclusions of the prime-field odd row, for p > 9. -/
theorem prime_linear_source_row {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    (p % 8 = 1 ∨ p % 8 = 7) ∧
      (ChapterB.minimalParabolicMax T hP).subgroupOf K =
        centralizer (((center ((T : Subgroup H).subgroupOf K)).map
          ((T : Subgroup H).subgroupOf K).subtype) : Set K) ∧
      8 < Nat.card ((T : Subgroup H).map (MulAut.conjNormal : H →* MulAut K)) := by
  obtain ⟨hc, hM⟩ := prime_linear_source_geometry T hP K hgen ho hF hp eK
  exact ⟨hc, hM, (prime_linear_source_automizer_bound T hP K hgen hO ho hF hp eK).2⟩

end CFSG.Quasithin.ChapterE.Structure
