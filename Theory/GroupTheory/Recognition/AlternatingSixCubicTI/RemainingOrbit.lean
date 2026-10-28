module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.EightOrbit
public import Mathlib.Data.Set.Card

/-!
# The remaining six-point suborbit

Every nonbase symmetric suborbit has at least four points: an action on
at most three points would kill the normal four-core and contradict its
unique fixed coset. Removing the base and the eight-point orbit leaves
six points, which cannot split into two such orbits. The final theorem
constructs the complete (1,8,6) source decomposition from the original
TI Sylow and faithful cyclic-four normalizer quotient.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
variable {G:Type*} [Group G] [Finite G]

theorem nonbase_orbit_card_ge_four (f:Four→*G) (hf:Function.Injective f) (hi:f.range.index=15)
    (hc:∀x:G,orderOf x=3→Nat.card (centralizer ({x}:Set G))=9)
    (q:G⧸f.range) (hq:q≠((1:G):G⧸f.range)):
    4≤Nat.card (MulAction.orbit f.range q) := by
  classical
  by_contra hn
  have hsmall:Nat.card (MulAction.orbit f.range q)≤3:=by omega
  let O:=MulAction.orbit f.range q
  let : Fintype O:=Fintype.ofFinite O
  let ψ:Four→*Equiv.Perm O:=(MulAction.toPermHom f.range O).comp f.rangeRestrict
  have hp:Nat.card (Equiv.Perm O)<24 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    have hO:Fintype.card O≤3:=by simpa only [Nat.card_eq_fintype_card] using hsmall
    exact (Nat.factorial_le hO).trans_lt (by decide : Nat.factorial 3<24)
  have hcore:core≤ψ.ker := by
    rw [core_eq]
    exact Theory.SpecificGroups.SymmetricFour.twoCore_le_ker_of_card_lt ψ hp
  have hfix:q∈MulAction.fixedPoints (core.map f) (G⧸f.range) := by
    intro x
    obtain ⟨b,hb,he⟩:=x.property
    have hh:ψ b=1:=hcore hb
    have hhq:=congrArg (fun e:Equiv.Perm O=>e ⟨q,MulAction.mem_orbit_self q⟩) hh
    have hv:=congrArg Subtype.val hhq
    change f b • q=q at hv
    change (x:G) • q=q
    rwa [he] at hv
  rw [mapped_core_fixedPoints f hf hi hc,Set.mem_singleton_iff] at hfix
  exact hq hfix

section Counting
variable {A X:Type*} [Group A] [MulAction A X] [Finite X]

theorem remaining_six_orbit (a b:X) (ha:∀g:A,g • a=a)
    (hX:Nat.card X=15) (hb:b≠a) (h8:Nat.card (MulAction.orbit A b)=8)
    (hmin:∀x:X,x≠a→4≤Nat.card (MulAction.orbit A x)):
    ∃c:X,MulAction.orbit A c=(({a}:Set X)∪MulAction.orbit A b)ᶜ ∧
      Nat.card (MulAction.orbit A c)=6 := by
  classical
  have hao:a∉MulAction.orbit A b := by
    rintro ⟨g,hg⟩
    exact hb ((MulAction.injective g) (hg.trans (ha g).symm))
  let R:Set X:=(({a}:Set X)∪MulAction.orbit A b)ᶜ
  have hR:R.ncard=6 := by
    rw [Set.ncard_compl,Set.singleton_union,Set.ncard_insert_of_notMem hao]
    change Nat.card X-(Nat.card (MulAction.orbit A b)+1)=6
    rw [hX,h8]
  have hsub (x:X) (hx:x∈R):MulAction.orbit A x⊆R := by
    have hxa:x≠a:=fun hh=>hx (Or.inl hh)
    have hxb:x∉MulAction.orbit A b:=fun hh=>hx (Or.inr hh)
    rintro y ⟨g,rfl⟩ hbad
    rcases hbad with hbad|hbad
    · exact hxa ((MulAction.injective g) (hbad.trans (ha g).symm))
    · obtain ⟨k,hk⟩:=hbad
      apply hxb
      refine ⟨g⁻¹*k,?_⟩
      change (g⁻¹*k) • b=x
      change k • b=g • x at hk
      rw [mul_smul,hk,inv_smul_smul]
  obtain ⟨c,hc⟩:=(Set.ncard_pos (s:=R)).mp (show 0<R.ncard by rw [hR]; decide)
  have hca:c≠a:=fun hh=>hc (Or.inl hh)
  have he:MulAction.orbit A c=R := by
    apply Set.Subset.antisymm (hsub c hc)
    intro d hd
    by_contra hdn
    have hda:d≠a:=fun hh=>hd (Or.inl hh)
    have hdis:Disjoint (MulAction.orbit A c) (MulAction.orbit A d) := by
      apply Set.disjoint_left.mpr
      rintro x ⟨g,rfl⟩ ⟨k,hk⟩
      apply hdn
      refine ⟨k⁻¹*g,?_⟩
      change (k⁻¹*g) • c=d
      change k • d=g • c at hk
      rw [mul_smul,←hk,inv_smul_smul]
    have hle: (MulAction.orbit A c∪MulAction.orbit A d).ncard≤R.ncard :=
      Set.ncard_le_ncard (Set.union_subset (hsub c hc) (hsub d hd))
    rw [Set.ncard_union_eq hdis,hR] at hle
    have hc4:=hmin c hca
    have hd4:=hmin d hda
    change Nat.card (MulAction.orbit A c)+Nat.card (MulAction.orbit A d)≤6 at hle
    omega
  exact ⟨c,he,he ▸ hR⟩
end Counting

theorem exists_suborbits_of_ti (f:Four→*G) (hf:Function.Injective f) (hi:f.range.index=15)
    (P:Sylow 3 G) [IsElementaryAbelian 3 P] (hP:Nat.card (P:Subgroup G)=9)
    (hTI:∀g:G,(P:Subgroup G)⊓(P:Subgroup G).map (MulAut.conj g).toMonoidHom=⊥ ∨
      (P:Subgroup G).map (MulAut.conj g).toMonoidHom=P)
    (hC:centralizer (P:Set G)≤P)
    (eN:(normalizer ((P:Subgroup G):Set G)⧸(P:Subgroup G).subgroupOf
      (normalizer ((P:Subgroup G):Set G)))≃*Multiplicative (ZMod 4)):
    ∃b c:G⧸f.range,b≠((1:G):G⧸f.range) ∧ Nat.card (MulAction.orbit f.range b)=8 ∧
      MulAction.orbit f.range c=(({((1:G):G⧸f.range)}:Set (G⧸f.range))∪MulAction.orbit f.range b)ᶜ ∧
      Nat.card (MulAction.orbit f.range c)=6 := by
  obtain ⟨b,hb,_,h8⟩:=exists_eight_orbit_of_ti f hf hi P hP hTI hC eN
  have hfix:∀g:f.range,g • (((1:G):G⧸f.range))=((1:G):G⧸f.range) := by
    intro g
    change ((g.val*1:G):G⧸f.range)=((1:G):G⧸f.range)
    apply QuotientGroup.eq.mpr
    simp
  obtain ⟨c,hcover,h6⟩:=remaining_six_orbit (((1:G):G⧸f.range)) b hfix hi hb h8
    (nonbase_orbit_card_ge_four f hf hi (cubic_centralizer_card P hP hTI hC eN))
  exact ⟨b,c,hb,h8,hcover,h6⟩
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
