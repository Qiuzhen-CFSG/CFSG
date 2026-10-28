module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.ProperSections
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.SpecificGroups.SL2.DefiningRank

/-!
# Proper SL₂ sections in the nonsemisimple A.2.12 branch

A proper subgroup of an actual quotient lifts to a proper subgroup of the
original ambient group. The genuine proper-section induction hypothesis
therefore applies there. Grün's lemma makes the exceptional A(1.b) quotient
center-free, so a semisimple section with nontrivial center has local rank at
most two. A proper SL₂(pᵉ) section contradicts this bound for odd p and e > 2:
its central involution centralizes the defining root group of rank e.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.2.12,
printed p.36. No quasithinness of an arbitrary quotient is assumed.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G Q R : Type u}
  [Group G] [Group Q] [Group R] [Finite G] [Finite Q] [Finite R]

omit [Finite G] [Finite R] in
/-- A's exceptional quotient has trivial center by Grün's lemma. -/
theorem TheoremAException.center_eq_bot {p : ℕ} (h : TheoremAException G R p) :
    center R = ⊥ := by
  obtain ⟨_,H,_,⟨e⟩,⟨d⟩⟩ := h
  let : Group.IsPerfect H := d.semisimple.isPerfect
  have hz := Group.IsPerfect.center_quotient_center_eq_bot H
  apply bot_unique
  intro z hzR
  change z = 1
  have hzQ : e z ∈ center (H ⧸ center H) := (centerCongr e ⟨z,hzR⟩).property
  rw [hz] at hzQ
  exact e.injective (show e z = e 1 by simpa using hzQ)

/-- A proper semisimple subgroup of an actual quotient is controlled by
induction in its literal preimage when its center is nontrivial. -/
theorem proper_quotient_subgroup_local_rank_le_two
    (ih : TheoremsOnProperSections K G) (hqt : IsQuasithin G) (hk : IsKGroup K G)
    (f : G →* Q) (hf : Function.Surjective f) (L : Subgroup Q) (hL : L ≠ ⊤)
    (hsemi : IsSemisimple L) (hz : center L ≠ ⊥)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) : twoLocalPrimeRank p L ≤ 2 := by
  let M := L.comap f
  have hM : M ≠ ⊤ := by
    intro ht
    apply hL
    change L.comap f = ⊤ at ht
    rw [← L.map_comap_eq_self_of_surjective hf, ht, Subgroup.map_top_of_surjective f hf]
  have hsection : IsSectionOf L M :=
    IsSectionOf.of_surjective (f.subgroupComap L) (f.subgroupComap_surjective_of_surjective L hf)
  have hc := ((ih.subgroup M hM).1 (hqt.subgroup M) (hk.subgroup M)
    L hsection hsemi p hp ho).1
  exact (hc.resolve_right (fun he => hz he.center_eq_bot)).1.trans
    (isQuasithin_iff_twoLocalPrimeRank.mp (hqt.subgroup M) p hp ho)

namespace Nonsemisimple.RankTwoSieve
open Matrix
variable {F : Type*} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]
local instance : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩

/-- A proper SL₂ over a large odd field in any quotient contradicts the
original induction hypothesis, using the literal subgroup preimage. -/
theorem no_large_proper_sl2_quotient
    (ih : TheoremsOnProperSections K G) (hqt : IsQuasithin G) (hk : IsKGroup K G)
    (f : G →* Q) (hf : Function.Surjective f)
    (ho : Odd p) (hcard : Nat.card F = p^e) (he : 2 < e)
    (j : SpecialLinearGroup (Fin 2) F →* Q) (hj : Function.Injective j)
    (hproper : j.range ≠ ⊤) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by intro heq; subst p; exact (by decide : ¬ Odd 2) ho
  have hpow : p < p^e := by
    simpa only [pow_one] using (Nat.pow_lt_pow_right hp.one_lt (show 1 < e by omega))
  have hlarge : 3 < Nat.card F := by rw [hcard]; have := hp.two_le; omega
  let L := j.range
  let a : SpecialLinearGroup (Fin 2) F ≃* L := MonoidHom.ofInjective hj
  let : IsQuasisimple L :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hlarge a.symm
  have hsemi : IsSemisimple L := by
    apply top_unique
    exact le_sSup (show IsComponent L ⊤ from
      ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩)
  let z : L := a (-1)
  have hz := SpecialLinearGroup.map_neg_one_isInvolution hp2 a.toMonoidHom a.injective
  have hzcenter : z ∈ center L := by
    apply mem_center_iff.mpr
    intro b
    obtain ⟨b,rfl⟩ := a.surjective b
    change a b * a (-1) = a (-1) * a b
    rw [← map_mul, ← map_mul]
    congr 1
    simp
  have hzbot : center L ≠ ⊥ := by
    intro hbot
    have hzone : z = 1 := by simpa only [hbot, mem_bot] using hzcenter
    exact hz.1 hzone
  have hrank := proper_quotient_subgroup_local_rank_le_two ih hqt hk f hf L hproper
    hsemi hzbot p hp ho
  have hlocal : IsTwoLocal (centralizer ({z} : Set L)) :=
    isTwoLocal_involution_centralizer (orderOf_eq_prime hz.2 hz.1)
  have hr := SpecialLinearGroup.fieldExponent_le_primeRank_centralizer hcard
    a.toMonoidHom a.injective
  exact (Nat.not_le_of_gt he) (hr.trans (hlocal.primeRank_le p |>.trans hrank))


end Nonsemisimple.RankTwoSieve
end CFSG.Quasithin.ChapterA.Section02

end
