module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.CentralizerSource
public import Theory.SpecificGroups.PSL2.PrimeInvolutionCentralizerMaximal

/-!
# The original maximal overgroup in prime-field odd PSL₂

For a normal marked PSL₂(p) subgroup, p > 9, the prescribed Sylow subgroup
supplies a central involution in K. Its intrinsic centralizer is maximal by
the proved Dickson calculation. Hence the actual unique maximal overgroup
is its full ambient centralizer, and its intersection with K is the literal
intrinsic centralizer. No centralizer recognition conclusion is an input.

Source: Aschbacher–Smith E.2.2(2c), printed pp.215–216.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure

/-- The original normal prime-field branch supplies its actual centralizer
and a marked involution of the original Sylow subgroup. -/
theorem prime_linear_source_centralizer {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    ∃ t : K, GorensteinWalter.IsInvolution t ∧ (t : H) ∈ (T : Subgroup H) ∧
      (T : Subgroup H) ≤ centralizer ({(t : H)} : Set H) ∧
      ChapterB.minimalParabolicMax T hP = centralizer ({(t : H)} : Set H) ∧
      (ChapterB.minimalParabolicMax T hP).subgroupOf K = centralizer ({t} : Set K) := by
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, ho, by decide, by simpa using hF⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := PSL2MatrixGroup F)
  obtain ⟨m, _, ⟨d⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd S
  have heven : 2 ∣ Nat.card K := by
    rw [Nat.card_congr eK.toEquiv]
    have hS : 2 ∣ Nat.card S := by
      rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
      exact dvd_mul_right 2 _
    exact hS.trans (S : Subgroup (PSL2MatrixGroup F)).card_subgroup_dvd_card
  obtain ⟨t, ht, htT, hfix⟩ := normal_even_subgroup_central_sylow_involution T K heven
  have hmap : (centralizer ({t} : Set K)).map eK.toMonoidHom =
      centralizer ({eK t} : Set (PSL2MatrixGroup F)) := by
    ext y
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    rw [← eK.injective.eq_iff]
    simp only [map_mul, eK.apply_symm_apply]
  have hti : GorensteinWalter.IsInvolution (eK t) :=
    ⟨fun he => ht.1 (eK.injective (by simpa using he)), by rw [← map_pow, ht.2, map_one]⟩
  have hmax : IsCoatom (centralizer ({t} : Set K)) := by
    apply (OrderIso.isCoatom_iff eK.mapSubgroup _).mp
    change IsCoatom ((centralizer ({t} : Set K)).map eK.toMonoidHom)
    rw [hmap]
    exact Theory.PSL2.prime_involution_centralizer_isCoatom_of_nine_lt ho hF hp (eK t) hti
  exact ⟨t, ht, htT, hfix, minimalParabolic_max_eq_involution_centralizer T hP K hgen t hmax hfix⟩

end CFSG.Quasithin.ChapterE.Structure
