module
public import BenderSuzuki.SE.Final
public import BenderSuzuki.SE.ModelSylowInvolutions
/-!
# A strong-embedding obstruction from two-subgroup involutions

In ambient two-rank at least two, the full Bender–Suzuki theorem identifies
the involution core modulo its odd core with one of the three Bender models.
Square-one elements lie in the involution core. The odd-core quotient is
injective on every two-subgroup, so commuting model involutions lift to
commuting original elements. This is weaker than a general solvability
claim about strongly embedded subgroups and retains the rank hypothesis.

Source: the full Bender–Suzuki Theorem SE; its application in Aschbacher,
Sporadic Groups (1994), 45.11, printed pp.248–249.
-/
public section
open Subgroup
namespace BenderSuzuki
open PFchapter1section1 PFAppendixIII
private theorem mem_involutionCore_of_sq {G:Type*} [Group G] {a:G} (ha:a^2=1) :
    a∈involutionCore G := by
  by_cases h:a=1
  · exact h ▸ one_mem _
  rw [involutionCore_eq_closure]
  exact Subgroup.subset_closure ⟨h,ha⟩

private theorem rank_involutionCore {G:Type*} [Group G] (hr:TwoRankAtLeastTwo G) :
    TwoRankAtLeastTwo (involutionCore G) := by
  obtain ⟨E,hE,hsq⟩:=hr
  have hEL : E ≤ involutionCore G:=fun x hx=>mem_involutionCore_of_sq (congrArg Subtype.val (hsq ⟨x,hx⟩))
  refine ⟨E.subgroupOf (involutionCore G),?_,?_⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe hEL).toEquiv,hE]
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val (hsq ⟨(x:G),x.property⟩)

theorem IsStronglyEmbedded.squares_commute_in_twoSubgroup
    {G:Type*} [Group G] [Finite G] {M:Subgroup G} (hM:IsStronglyEmbedded M)
    (hr:TwoRankAtLeastTwo G) (P:Subgroup G) (hP:IsPGroup 2 P) (a b:G)
    (ha:a∈P) (hb:b∈P) (ha2:a^2=1) (hb2:b^2=1) : Commute a b := by
  have hSE:=(theorem_SE M hM).resolve_left (fun h => h (rank_involutionCore hr))
  let L:=involutionCore G
  let R:=P.subgroupOf L
  have hR:IsPGroup 2 R:=hP.comap_subtype
  let q:L→*L⧸twoPrimeCore L:=QuotientGroup.mk' (twoPrimeCore L)
  let f:R→*L⧸twoPrimeCore L:=q.comp R.subtype
  have hd:Disjoint R (twoPrimeCore L) := by
    obtain ⟨n,hn⟩:=hR.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact (pPrimeCore_coprime_card (p:=2) (G:=L)).pow_left n
  have hf:Function.Injective f:=by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp hd x.property ((QuotientGroup.eq_one_iff _).mp hx)
  let A:R:=⟨⟨a,mem_involutionCore_of_sq ha2⟩,ha⟩
  let B:R:=⟨⟨b,mem_involutionCore_of_sq hb2⟩,hb⟩
  have hA:A^2=1:=Subtype.ext (Subtype.ext ha2)
  have hB:B^2=1:=Subtype.ext (Subtype.ext hb2)
  have hc:=hSE.1.squares_commute_in_twoSubgroup ((⊤:Subgroup R).map f)
    ((hR.to_subgroup ⊤).map f) (f A) (f B)
    (mem_map_of_mem _ (mem_top _)) (mem_map_of_mem _ (mem_top _))
    (by rw [←map_pow,hA,map_one]) (by rw [←map_pow,hB,map_one])
  have hab:A*B=B*A:=hf (by simpa only [map_mul] using hc.eq)
  exact congrArg (fun x:R=>(x:G)) hab
end BenderSuzuki
