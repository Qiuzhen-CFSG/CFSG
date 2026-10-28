module
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterCentralizerGeneration
public import Theory.SpecificGroups.PSL3Two.NonSolvable
public import Theory.GroupTheory.SolvableSylowControl.AbelianProduct
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter

/-!
# The binary graph-extension Cartan parameter and odd kernel

Every solvable subgroup of Aut(SL₃(2)) containing a full Sylow two-subgroup
is a two-group. Otherwise its outer actor and Sylow intersection force
it to contain the nonsolvable inner SL₃(2). An odd abelian Sylow permuter
has solvable join with the Sylow and is therefore trivial. Consequently
the literal E.3.37 Cartan parameter is one.

Surjective transport retains the prescribed Sylow and the entire odd
subgroup: its image is trivial, so it lies in the full actor kernel.
`NonFFSourceDoubledBinaryGeneration` applies this to the actual chosen orbit
and its original H-star Cartan witness. The odd-kernel normalizer theorem
is a separate ambient obligation; the parameter calculation alone does
not bound n(H) or w.

Source: Aschbacher–Smith 7.3.4 and 7.6.1, printed pp.699,702,
refs/quasithin.pdf; E.3.37, printed p.239.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryGeneration
open Matrix.PSL3Two ChapterE.Section06.FixedPointBounds

/-- Every solvable overgroup of a full Sylow in the graph extension is a two-group. -/
theorem solvable_sylow_overgroup_two
    (P : Sylow 2 (MulAut SL)) (H : Subgroup (MulAut SL))
    (hPH : (P : Subgroup (MulAut SL)) ≤ H) (hs : Group.IsSolvable H) :
    IsPGroup 2 H := by
  by_contra hn
  have hnot : ¬ (P : Subgroup (MulAut SL)) ≤ MulAut.innerSubgroup SL := by
    intro hh
    apply P.not_dvd_index
    have hi := index_dvd_of_le hh
    change Nat.card (MulAut.Outer SL) ∣ (P : Subgroup (MulAut SL)).index at hi
    rwa [Automorphisms.card_outer_sl] at hi
  obtain ⟨a,ha,hao⟩ := SetLike.not_le_iff_exists.mp hnot
  have hi := Automorphisms.OuterCentralizerGeneration.inner_le_of_sylow_le_of_not_isTwoGroup
    P H hPH hn a (hPH ha) hao
  let f : SL →* H := MulAut.conj.codRestrict H (fun g => hi ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y he
    exact (MulAut.conj_injective_of_center_eq_bot center_eq_bot) (congrArg Subtype.val he)
  let := hs
  exact not_isSolvable_sl3_two (Group.isSolvable_of_isSolvable_injective hf)

/-- The full graph extension has no nontrivial odd abelian Sylow permuter. -/
theorem odd_permuter_eq_bot (P : Sylow 2 (MulAut SL))
    (B : Subgroup (MulAut SL)) [IsMulCommutative B]
    (ho : Odd (Nat.card B))
    (hp : (B : Set (MulAut SL)) * P = (P : Set (MulAut SL)) * B) : B = ⊥ := by
  have hs := solvable_of_odd_abelian_permuting_two_subgroup B P ho P.isPGroup' hp
  have htwo := (solvable_sylow_overgroup_two P (B ⊔ (P : Subgroup (MulAut SL)))
    le_sup_right hs).to_le (show B ≤ B ⊔ (P : Subgroup (MulAut SL)) from le_sup_left)
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  apply card_eq_one.mp
  rw [hn]
  have hzero : n = 0 := by
    by_contra hh
    exact ho.not_two_dvd_nat (hn ▸ dvd_pow_self 2 hh)
  simp [hzero]

/-- A surjective original actor map retains the prescribed Sylow and permuting
odd subgroup. The latter lies in its full kernel. -/
theorem odd_permuter_le_kernel {X : Type*} [Group X] [Finite X]
    (q : X →* MulAut SL) (hq : Function.Surjective q) (P : Sylow 2 X)
    (B : Subgroup X) [IsMulCommutative B] (ho : Odd (Nat.card B))
    (hp : (B : Set X) * P = (P : Set X) * B) : B ≤ q.ker := by
  have hperm : (B.map q : Set (MulAut SL)) * (P.mapSurjective hq : Set (MulAut SL)) =
      (P.mapSurjective hq : Set (MulAut SL)) * (B.map q : Set (MulAut SL)) := by
    change (q '' (B : Set X)) * (q '' (P : Set X)) =
      (q '' (P : Set X)) * (q '' (B : Set X))
    rw [← Set.image_mul, ← Set.image_mul, hp]
  have hb := odd_permuter_eq_bot (P.mapSurjective hq) (B.map q)
    (ho.of_dvd_nat (card_map_dvd B q)) hperm
  intro b hbB
  exact mem_bot.mp (hb ▸ mem_map_of_mem q hbB)

/-- The literal Cartan parameter, including its Sylow permutation clause, is one. -/
theorem automorphism_nPrime_eq_one : nPrime (MulAut SL) = 1 := by
  apply le_antisymm (nPrime_le_iff.mpr ?_) one_le_nPrime
  intro c w
  let := w.abelian
  have hb := odd_permuter_eq_bot w.sylow w.abelianGroup w.odd w.permutes
  have hc : w.cyclicGroup = ⊥ := bot_unique (hb ▸ w.cyclic_le)
  have hcard := w.card
  rw [hc,card_bot] at hcard
  have hpow := c.lt_two_pow_self
  omega
end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryGeneration
