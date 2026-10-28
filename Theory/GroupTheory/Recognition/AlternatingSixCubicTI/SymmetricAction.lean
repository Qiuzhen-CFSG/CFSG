module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.WeakClosure
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.CubicFixedPoints
public import Theory.SpecificGroups.SymmetricFourSmallQuotient

/-!
# Faithfulness of the original fifteen-coset action

The weakly closed four-core fixes exactly the original coset. Every nontrivial normal subgroup of S4 contains this core, so the action kernel is trivial.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
variable {G:Type*} [Group G] [Finite G]

theorem symmetricCore_fixedPoints (H:Subgroup G) (e:H≃*Four) (hi:H.index=15)
    (hc:∀x:G,orderOf x=3→Nat.card (centralizer ({x}:Set G))=9):
    MulAction.fixedPoints (symmetricCore H) (G⧸H)={((1:G):G⧸H)} := by
  have hN:=symmetricCore_normalizer H e hi hc
  have hEH:symmetricCore H≤H := by
    rintro _ ⟨a,_,rfl⟩
    exact a.property
  ext q
  induction q using Quotient.inductionOn' with | h g =>
    constructor
    · intro hq
      have hg: (symmetricCore H).map (MulAut.conj g⁻¹).toMonoidHom≤H :=
        (fixed_coset_iff H (symmetricCore H) g).mp hq
      have he:=symmetricCore_weakly_closed H e hi hc g⁻¹ hg
      have hn:g⁻¹∈normalizer (symmetricCore H:Set G) := mem_normalizer_iff_map_conj_eq.mpr he
      rw [hN] at hn
      apply Set.mem_singleton_iff.mpr
      apply QuotientGroup.eq.mpr
      simpa only [mul_one] using hn
    · intro hq
      rw [Set.mem_singleton_iff.mp hq]
      rw [fixed_coset_iff]
      have he:(MulAut.conj (1:G)⁻¹).toMonoidHom=MonoidHom.id G := by ext x; simp
      rw [he,map_id]
      exact hEH

theorem symmetric_coset_action_injective (H:Subgroup G) (e:H≃*Four) (hi:H.index=15)
    (hc:∀x:G,orderOf x=3→Nat.card (centralizer ({x}:Set G))=9):
    Function.Injective (MulAction.toPermHom G (G⧸H)) := by
  let a:=MulAction.toPermHom G (G⧸H)
  let f:=H.subtype.comp e.symm.toMonoidHom
  let ψ:=a.comp f
  have hfixed:=symmetricCore_fixedPoints H e hi hc
  have hiψ:Function.Injective ψ := by
    apply ψ.ker_eq_bot_iff.mp
    by_contra hk
    have hcore:core≤ψ.ker := by
      rw [core_eq]
      exact Theory.SpecificGroups.SymmetricFour.twoCore_le_normal_of_ne_bot ψ.ker hk
    let : Nontrivial (G⧸H):=Finite.one_lt_card_iff_nontrivial.mp (by
      change 1<H.index
      rw [hi]
      decide)
    obtain ⟨q,hq⟩:=exists_ne (((1:G):G⧸H))
    have hqfix:q∈MulAction.fixedPoints (symmetricCore H) (G⧸H) := by
      intro x
      have hx:(x:G)∈core.map f :=
        Eq.mp (congrArg (fun K:Subgroup G=>(x:G)∈K) (symmetricCore_eq H e)) x.property
      obtain ⟨b,hb,he⟩:=hx
      have hp:ψ b=1:=hcore hb
      have heq:=congrArg (fun v:Equiv.Perm (G⧸H)=>v q) hp
      change f b • q=q at heq
      change (x:G) • q=q
      rwa [he] at heq
    rw [hfixed,Set.mem_singleton_iff] at hqfix
    exact hq hqfix
  apply a.ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro g hg
  have hbase:=congrArg (fun v:Equiv.Perm (G⧸H)=>v (((1:G):G⧸H))) hg
  have hgH:g∈H := by
    change ((g*1:G):G⧸H)=((1:G):G⧸H) at hbase
    have hh:=QuotientGroup.eq.mp hbase.symm
    simpa using hh
  have he:ψ (e ⟨g,hgH⟩)=1 := by simpa [ψ,f] using hg
  have he1:e ⟨g,hgH⟩=1:=hiψ (he.trans ψ.map_one.symm)
  have hgs: (⟨g,hgH⟩:H)=1 := e.injective (he1.trans e.map_one.symm)
  exact congrArg Subtype.val hgs
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
