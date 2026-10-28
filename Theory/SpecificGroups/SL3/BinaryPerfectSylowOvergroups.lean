module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# Perfect subgroups of binary SL₃ and the actual central projection

The kernel of SL₃(F) → PSL₃(F) has order dividing three. For p > 3 the
restricted projection preserves p-rank, and perfection passes to its image.
The projective full-Sylow overgroup theorem therefore fills PSL₃. The center
of the perfect covering group lies in its Frattini subgroup, so this fills
SL₃ itself. In particular, no identification of the cover with its quotient
is made, including over the field of order four.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, central-cover lifting.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SL3.BinaryPerfectSylowOvergroups
variable (F : Type*) [Field F] [Finite F] [CharP F 2] [Group.IsPerfect SL(3,F)]

/-- A perfect subgroup of p-rank two, p > 3, forces every full-Sylow
overgroup in the genuine special linear cover to be the whole group. -/
theorem eq_top_of_perfect_large_odd_rank_two
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (ho : Odd p)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 SL(3,F)) (D K : Subgroup SL(3,F)) [Group.IsPerfect K]
    (hSD : (S : Subgroup SL(3,F)) ≤ D) (hKD : K ≤ D)
    (hr : 2 ≤ primeRank p K) : D = ⊤ := by
  let q := PSL3.projection F
  let k := q.subgroupMap K
  have hk : IsPGroup 3 k.ker := by
    rw [show k.ker = (q.subgroupMap K).ker from rfl, ker_subgroupMap,
      PSL3.projection_ker]
    exact (IsPGroup.of_card_dvd_pow (n := 1)
      (by simpa using card_center_dvd_three F)).comap_subtype
  have hcop : Nat.Coprime p (Nat.card k.ker) := by
    obtain ⟨a,ha⟩ := hk.exists_card_eq
    rw [ha]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd (by decide : 0 < 3) hd
      omega)).pow_right a
  have hrq : 2 ≤ primeRank p (K.map q) :=
    hr.trans (primeRank_le_of_coprime_ker p k hcop)
  let : Group.IsPerfect (K.map q) :=
    Group.IsPerfect.ofSurjective (f := k) (q.subgroupMap_surjective K)
  have him : (K.map q).subtype.range ≤ D.map q := by
    rw [range_subtype]
    exact map_mono hKD
  have hd := PSL3.LinearThree.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
    F ho hrq hn hF (S.mapSurjective (PSL3.projection_surjective F))
    (D.map q) (map_mono hSD) (K.map q).subtype (K.map q).subtype_injective him
  apply eq_top_of_sup_center_eq_top
  have hh := congrArg (Subgroup.comap q) hd
  simpa only [comap_map_eq, q, PSL3.projection_ker, comap_top] using hh

end Matrix.SL3.BinaryPerfectSylowOvergroups
