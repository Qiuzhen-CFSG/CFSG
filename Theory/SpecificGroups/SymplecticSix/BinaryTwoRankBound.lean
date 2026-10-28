module
public import Theory.SpecificGroups.SymplecticSix.BinarySylowAutomorphisms
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PGroup.MaximalIndex
import all Theory.SpecificGroups.SymplecticSix.BinarySylowAutomorphisms

/-!
# A strict rank-eight obstruction in binary symplectic six-space

The literal Sylow group has order 512 and a nonabelian Frattini subgroup,
as witnessed by two of its existing matrix coordinates. An abelian subgroup
of order at least 256 would contain the Frattini subgroup: a proper such
subgroup is already maximal. Consequently every elementary subgroup has
order at most 128. This sufficient bound retains the actual symplectic
carrier and uses no subgroup classification.

Source application: Aschbacher--Smith 4.4.12 and 12.1.9, printed
pp.622 and 793, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.SpecificGroups.SymplecticSix
open BinarySylowAutomorphisms

private theorem frattini_not_commutative : ¬ IsMulCommutative (frattini Parameters) := by
  intro hc
  let := hc
  let a : Parameters := ⟨![0,1,0,0,0,0,0,0,0]⟩
  let b : Parameters := ⟨![0,0,0,0,0,0,1,1,0]⟩
  have ha : a ∈ frattini Parameters := by rw [frattini_eq_kernel,kernel_mem]; decide
  have hb : b ∈ frattini Parameters := by rw [frattini_eq_kernel,kernel_mem]; decide
  have he := congrArg (fun x : frattini Parameters => x.val 4)
    (mul_comm (⟨a,ha⟩ : frattini Parameters) ⟨b,hb⟩)
  change (product a b) 4 = (product b a) 4 at he
  exact (by decide : (product a b) 4 ≠ (product b a) 4) he

private theorem abelian_card_lt (A : Subgroup Parameters) [IsMulCommutative A] :
    Nat.card A < 256 := by
  by_contra! hlarge
  have hphi : frattini Parameters ≤ A := by
    rcases eq_top_or_exists_le_coatom A with htop | ⟨M,hM,hAM⟩
    · rw [htop]; exact le_top
    · have hi := parameters_two.index_of_isCoatom M hM
      have hc := M.index_mul_card
      rw [hi,card_parameters] at hc
      have he : A = M := eq_of_le_of_card_ge hAM (by omega)
      rw [he]
      exact frattini_le_coatom hM
  exact frattini_not_commutative
    (.of_setLike_mul_comm (fun a ha b hb => setLike_mul_comm (hphi ha) (hphi hb)))

/-- The native binary symplectic group cannot contain an elementary group
of rank eight. The proved bound is sufficient, without asserting optimality. -/
theorem binary_twoRank_le_seven : primeRank 2 (Sp (ZMod 2)) ≤ 7 := by
  rw [sylow.primeRank_eq,←primeRank_congr 2 sylowEquiv]
  apply (primeRank_le_iff_elementary_card_le Parameters).mpr
  intro A hA
  let := hA
  have hsmall := abelian_card_lt A
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hnlt : n < 8 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    simpa only [hn] using hsmall
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) (by omega)

end Theory.SpecificGroups.SymplecticSix
