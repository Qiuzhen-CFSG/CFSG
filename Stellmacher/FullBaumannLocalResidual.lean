module
public import Stellmacher.FullBaumannLocalNormalizer
public import Stellmacher.SectionFiveToSeven.ResidualTwoExtension

/-!
# Full Baumann commutators at a cubic vertex

Suppose the original ambient Sylow S has local two-core Q of index two,
and B(S) is not contained in Q. A full Baumann commutator F supplementing
S in the local vertex is normal there: its two-core normalizes F by
Baumann weak closure, and S=Q B(S). The two-group quotient then puts the
entire local two-residual in F.

This is the cubic local specialization of Stellmacher (5.2) used in the
two-extraction argument of (9.3), Journal of Algebra 190 (1997), p.49.
It uses the actual global Sylow, with no assumption about solvability of
ambient two-local subgroups. It asserts local normality, not subnormality
in an arbitrary centralizer.
-/
open Subgroup Stellmacher
namespace Stellmacher.SectionsFiveToSeven
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem sup_eq_of_index_two (Q B S : Subgroup G)
    (hQ : Q ≤ S) (hB : B ≤ S) (hi : Q.relIndex S = 2) (hnot : ¬ B ≤ Q) :
    Q ⊔ B = S := by
  have hle : Q ⊔ B ≤ S := sup_le hQ hB
  have hm := Q.relIndex_mul_relIndex (Q ⊔ B) S le_sup_left hle
  rw [hi] at hm
  have hd : Q.relIndex (Q ⊔ B) ∣ 2 := ⟨_, hm.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact (hnot (le_sup_right.trans (relIndex_eq_one.mp h))).elim
  · have hh : (Q ⊔ B).relIndex S = 1 := by rw [h] at hm; omega
    exact le_antisymm hle (relIndex_eq_one.mp hh)

/-- A full Baumann commutator supplementing the ambient Sylow is the whole
local residual once the Baumann group escapes the local core. -/
public theorem residual_le_full_baumann_of_index_two
    (S : Sylow 2 G) (F P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hFP : F ≤ P)
    (hfull : F = ⁅F, baumannIn (S : Subgroup G)⁆)
    (hgen : F ⊔ (S : Subgroup G) = P)
    (hi : (twoCoreIn P).relIndex (S : Subgroup G) = 2)
    (hnot : ¬ baumannIn (S : Subgroup G) ≤ twoCoreIn P) :
    NormalIn F P ∧ twoResidualIn P ≤ F := by
  have hcore : twoCoreIn P ≤ (S : Subgroup G) := by
    let T := S.subtype hSP
    have hh := (pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal T
    rintro x ⟨y,hy,rfl⟩
    exact hh hy
  have hQS := sup_eq_of_index_two (twoCoreIn P) (baumannIn (S : Subgroup G))
    (S : Subgroup G) hcore inf_le_left hi hnot
  have hQF := twoCore_normalizes_full_baumann S F P hFP
    (inf_le_left.trans hSP) hfull
  have hBF : baumannIn (S : Subgroup G) ≤ normalizer (F : Set G) := by
    rw [hfull]
    exact normalizer_commutator_ge_right _ _
  have hSF : (S : Subgroup G) ≤ normalizer (F : Set G) :=
    hQS ▸ sup_le hQF hBF
  have hnorm : (F.subgroupOf (F ⊔ (S : Subgroup G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le F.le_normalizer hSF)
  refine ⟨⟨hFP, hgen ▸ hnorm⟩, ?_⟩
  exact Stellmacher.SectionThree.twoResidualAmbient_le_left_of_le_sup F (S : Subgroup G) P
    hnorm S.isPGroup' hgen.ge
end Stellmacher.SectionsFiveToSeven
