module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The stronger Sylow congruence for trivial intersection

A TI Sylow subgroup acts freely by conjugation on all the other Sylow
subgroups: a stabilizer lies in their intersection. Orbit decomposition
therefore makes the Sylow subgroup order divide the number of other Sylows.
This strengthens the usual congruence modulo the prime and is used in
Aschbacher, Sporadic Groups (1994),45.9,printed p247.
-/

public section
open Subgroup MulAction
namespace Sylow
variable {G:Type*} [Group G] [Finite G] {p:ℕ} [Fact p.Prime]
theorem card_dvd_card_sub_one_of_ti (P:Sylow p G)
    (hTI:∀g:G,g∉normalizer (P:Set G)→Disjoint (P:Subgroup G)
      ((P:Subgroup G).map (MulAut.conj g).toMonoidHom)) :
    Nat.card P∣Nat.card (Sylow p G)-1 := by
  classical
  have hpair (Q:Sylow p G) (hQ:Q≠P):Disjoint (P:Subgroup G) (Q:Subgroup G):=by
    obtain ⟨g,hg⟩:=exists_smul_eq G P Q
    have hgN:g∉normalizer (P:Set G):=fun hh=>hQ (hg.symm.trans (smul_eq_iff_mem_normalizer.mpr hh))
    rw [←hg]
    change Disjoint (P:Subgroup G) ((P:Subgroup G).map (MulAut.conj g).toMonoidHom)
    exact hTI g hgN
  let X:={Q:Sylow p G//Q≠P}
  have hPfix (a:P):(a:G)•P=P:=smul_eq_iff_mem_normalizer.mpr (P.le_normalizer a.property)
  let :MulAction P X:={
    smul a Q:=⟨(a:G)•Q.val,by
      intro he
      apply Q.property
      have hh:=congrArg (fun R:Sylow p G=>(a:G)⁻¹•R) he
      simpa only [inv_smul_smul,show (a:G)⁻¹•P=P from hPfix a⁻¹] using hh⟩
    one_smul Q:=by apply Subtype.ext;exact one_smul G Q.val
    mul_smul a b Q:=by apply Subtype.ext;exact mul_smul (a:G) (b:G) Q.val }
  have hstab (Q:X):stabilizer P Q=⊥:=by
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    have he:(a:G)•Q.val=Q.val:=congrArg Subtype.val ha
    have haN:(a:G)∈normalizer (Q.val:Set G):=smul_eq_iff_mem_normalizer.mp he
    have hPQ:(a:G)∈(P:Subgroup G)⊓Q.val:=
      (P.isPGroup'.inf_normalizer_sylow Q.val).le ⟨a.property,haN⟩
    exact Subtype.ext (Subgroup.disjoint_def.mp (hpair Q.val Q.property) hPQ.1 hPQ.2)
  have hc:=Nat.card_congr (selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod] at hc
  have hX:Nat.card X=Nat.card (Sylow p G)-1:=by
    let :Fintype (Sylow p G):=Fintype.ofFinite _
    change Nat.card {Q:Sylow p G//¬Q=P}=Nat.card (Sylow p G)-1
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp [Nat.card_eq_fintype_card]
  rw [hX] at hc
  exact ⟨Nat.card (Quotient (orbitRel P X)),by simpa only [Nat.mul_comm] using hc⟩
end Sylow
