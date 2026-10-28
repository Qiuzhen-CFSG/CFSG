module
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Local markings through an ambient central quotient

For a subgroup P whose prime-core quotient is centerless, the kernel of
P -> K/Z(K) lies in that prime core: its elements are central in P, and
their images are central in the centerless quotient. With a two-core this
preserves every odd prime rank by the coprime-kernel rank theorem.

A nontrivial elementary binary subgroup W=[W,P] cannot disappear in K/Z(K),
since containment in Z(K) would make its commutator with P trivial. Its
image remains elementary and moved, and is normalized by the perfect image.
The ambient center is retained throughout; K need not be centerless.

Source application: Aschbacher--Smith 4.4.10--12, printed pp.621--622,
transporting the actual residual and moved module to a component quotient.
-/

public section
open Subgroup
namespace Theory.GroupTheory.CentralQuotientLocalMarking
variable {K : Type*} [Group K]

/-- The kernel on the subgroup lies in its prime core when its core quotient is centerless. -/
theorem subgroupMap_ker_le_pCore (p : ℕ) (P : Subgroup K)
    (hc : center (P ⧸ pCore p P) = ⊥) :
    ((QuotientGroup.mk' (center K)).subgroupMap P).ker ≤ pCore p P := by
  intro x hx
  have hxK : (x : K) ∈ center K := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg Subtype.val hx
  have hxP : x ∈ center P := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hxK y)
  have hq : QuotientGroup.mk' (pCore p P) x ∈ center (P ⧸ pCore p P) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore p P) y
    exact congrArg (QuotientGroup.mk' (pCore p P)) (mem_center_iff.mp hxP z)
  rw [hc,mem_bot] at hq
  exact (QuotientGroup.eq_one_iff _).mp hq

/-- Odd prime ranks survive the ambient central quotient on a subgroup with centerless two-core quotient. -/
theorem primeRank_map [Finite K] (P : Subgroup K)
    (hc : center (P ⧸ pCore 2 P) = ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (P.map (QuotientGroup.mk' (center K))) = primeRank p P := by
  let f := (QuotientGroup.mk' (center K)).subgroupMap P
  have hk : IsPGroup 2 f.ker :=
    pCore_isPGroup.to_le (subgroupMap_ker_le_pCore 2 P hc)
  apply (primeRank_eq_of_surjective_of_coprime p f
    ((QuotientGroup.mk' (center K)).subgroupMap_surjective P) ?_).symm
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  rw [hn]
  exact (Nat.coprime_two_right.mpr ho).pow_right n

/-- A nontrivial moved binary subgroup stays nontrivial, elementary and moved in the central quotient. -/
theorem moved_image (P W : Subgroup K) [Group.IsPerfect P]
    (hne : W ≠ ⊥) (he : IsElementaryAbelian 2 W) (hm : W = ⁅W,P⁆) :
    let q := QuotientGroup.mk' (center K)
    Group.IsPerfect (P.map q) ∧ W.map q ≠ ⊥ ∧
      IsElementaryAbelian 2 (W.map q) ∧
      W.map q = ⁅W.map q,P.map q⁆ ∧
      P.map q ≤ normalizer (W.map q : Set (K ⧸ center K)) := by
  let q := QuotientGroup.mk' (center K)
  have hmove : W.map q = ⁅W.map q,P.map q⁆ := by
    rw [←map_commutator,←hm]
  have hne' : W.map q ≠ ⊥ := by
    intro hb
    have hc : W ≤ center K := by
      simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb
    apply hne
    rw [hm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hc.trans (center_le_centralizer _))
  let := he
  exact ⟨Group.IsPerfect.ofSurjective (f := q.subgroupMap P) (q.subgroupMap_surjective P),
    hne',IsElementaryAbelian.map q,hmove,
    le_normalizer_iff_commutator_le_left.mpr hmove.symm.le⟩
end Theory.GroupTheory.CentralQuotientLocalMarking
