module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeAutomizer
public import Theory.SpecificGroups.PSL2.PrimeNormalExtension
public import GorensteinWalter.LinearRingEquiv
public import GorensteinWalter.PGL2DihedralSylow

/-!
# The actual large dihedral Sylow in the prime odd source row

Faithfulness on the original normal PSL₂(p) subgroup identifies H with
PSL₂(p) or its full PGL₂(p) extension. The concrete Sylow theorems then
supply a dihedral model for the original T. Its already proved order bound
excludes the four-group and dihedral-eight cases.

Source: Aschbacher–Smith E.2.2 and E.2.7, printed pp.215–216 and220–221.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure

/-- The original Sylow has an actual dihedral model of order at least sixteen. -/
theorem prime_linear_source_sylow_dihedral {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    ∃ m : ℕ, 3 ≤ m ∧ Nonempty (T ≃* DihedralGroup (2 ^ m)) := by
  have hlarge := (prime_linear_source_automizer_bound T hP K hgen hO ho hF hp eK).1
  have hmodel : ∃ m : ℕ, 1 ≤ m ∧ Nonempty (T ≃* DihedralGroup (2 ^ m)) := by
    by_cases hKtop : K = ⊤
    · let eH : H ≃* PSL2MatrixGroup F :=
        (topEquiv.symm.trans (MulEquiv.subgroupCongr hKtop.symm)).trans eK
      let S := T.mapSurjective (f := eH.toMonoidHom) eH.surjective
      have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
        ⟨p, 1, Fact.out, ho, by decide, by simpa using hF⟩
      obtain ⟨m, hm, ⟨d⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd S
      exact ⟨m, hm, ⟨((T : Subgroup H).equivMapOfInjective eH.toMonoidHom eH.injective).trans d⟩⟩
    · have hZ : center K = ⊥ := by
        apply le_bot_iff.mp
        intro k hk
        have hcent : eK k ∈ center (PSL2MatrixGroup F) := (centerCongr eK ⟨k, hk⟩).property
        rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at hcent
        exact mem_bot.mpr (eK.injective (by simpa only [map_one] using hcent))
      have hC := centralizer_eq_bot_of_centerless_sylow_supplement T K hgen hZ hO
      let := Fintype.ofFinite F
      let eF : ZMod p ≃+* F := ZMod.ringEquivOfPrime F Fact.out
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      let eK₀ := eK.trans (GorensteinWalter.psl2RingEquiv eF).symm
      obtain ⟨eH, _⟩ := Theory.PSL2.exists_pgl_equiv_of_proper_normal_prime_psl K hC hKtop
        (ZMod p) (by omega : 3 < p) (by simp) eK₀
      let S := T.mapSurjective (f := eH.toMonoidHom) eH.surjective
      have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
        ⟨p, 1, Fact.out, ho, by decide, by simp⟩
      obtain ⟨m, hm, ⟨d⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model (ZMod p) hodd S
      exact ⟨m, hm, ⟨((T : Subgroup H).equivMapOfInjective eH.toMonoidHom eH.injective).trans d⟩⟩
  obtain ⟨m, hm, ⟨d⟩⟩ := hmodel
  have hcard : 8 < 2 * 2 ^ m := by
    simpa only [Nat.card_congr d.toEquiv, DihedralGroup.nat_card] using hlarge
  have hm3 : 3 ≤ m := by
    by_contra! hh
    interval_cases m <;> norm_num at hcard
  exact ⟨m, hm3, ⟨d⟩⟩

end CFSG.Quasithin.ChapterE.Structure
