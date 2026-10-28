module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.QuotientAction
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.LocalStructure
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Terminal factor placement for a binary PSL₂ quotient

Let L be the normal span of the distinguished involutions in the terminal
step of Aschbacher's Lemma 3.4. If L/O₂′(L) is the actual binary PSL₂ model,
the Sylow intersection S ∩ L has exponent two: its image is a PSL₂ Sylow
subgroup, and the odd kernel makes the quotient map injective on it.
Every nonidentity element of S ∩ L is distinguished, so strong closure
places this entire subgroup in one of the two factors.

The other factor centralizes S ∩ L. Its quotient action therefore fixes a
PSL₂ Sylow subgroup pointwise and is inner by an element of that subgroup.
This action squares to one. Faithfulness on the factor forces each of its
elements to square to one upstairs, and its involutions already belong to L.
Thus the other factor lies in S ∩ L and hence in the first factor, contrary
to incomparability. This proves the requested placement in this model case.

Source: M. Aschbacher, *On finite groups of component type* (1975),
Lemma 3.4, pp.94–96, terminal appeal to Theorem 3.3;
GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
-/

public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII
open BenderSuzuki.MatrixGroups

private theorem linear_sylow_square {K : Type*} [Field K] [Finite K] [CharP K 2]
    (P : Sylow 2 (PSL2MatrixGroup K)) (x : P) : x ^ 2 = 1 := by
  let e := BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive P
  apply e.symm.injective
  rw [map_pow, map_one]
  change 2 • (e.symm x).toAdd = 0
  exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

private theorem linear_span_sylow_square
    (T : Sylow 2 (closure (terminalInvolutions A₁ A₂)))
    {n : ℕ}
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* PSL2BinaryMatrixGroup n)
    (x : T) : x ^ 2 = 1 := by
  let L := closure (terminalInvolutions A₁ A₂)
  let q := QuotientGroup.mk' (pPrimeCore 2 L)
  let φ := e.toMonoidHom.comp q
  have hq : Nat.Coprime 2 (Nat.card q.ker) := by
    simpa only [q, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (p := 2) (G := L))
  have hinj := injective_comp_subtype_of_coprime_ker q hq (T : Subgroup L) T.isPGroup'
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := T.mapSurjective hφ
  have hxP : φ (x : L) ∈ P := mem_map_of_mem φ x.property
  have hs : φ (x : L) ^ 2 = 1 :=
    congrArg Subtype.val (linear_sylow_square P ⟨φ (x : L), hxP⟩)
  apply hinj
  change q ((x : L) ^ 2) = q 1
  apply e.injective
  simpa only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_pow, map_one] using hs

private theorem linear_centralizing_factor_le
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (T : Sylow 2 (closure (terminalInvolutions A₁ A₂)))
    (hT : (T : Subgroup (closure (terminalInvolutions A₁ A₂))) =
      (S : Subgroup G).subgroupOf (closure (terminalInvolutions A₁ A₂)))
    {n : ℕ}
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* PSL2BinaryMatrixGroup n)
    (A B : Subgroup G) (hBS : B ≤ S)
    (hTA : (T : Subgroup (closure (terminalInvolutions A₁ A₂))).map
      (closure (terminalInvolutions A₁ A₂)).subtype ≤ A)
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hi : Function.Injective ((terminalQuotientAction hL).comp B.subtype))
    (hBI : ∀ b ∈ B, IsInvolution b → b ∈ closure (terminalInvolutions A₁ A₂)) : B ≤ A := by
  let := hL
  let L := closure (terminalInvolutions A₁ A₂)
  let q := QuotientGroup.mk' (pPrimeCore 2 L)
  let φ := e.toMonoidHom.comp q
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := T.mapSurjective hφ
  let ρ := terminalQuotientAction hL
  intro b hb
  have hfix : ∀ x ∈ P, MulAut.congr e (ρ b) x = x := by
    rintro x ⟨t, ht, rfl⟩
    change e (ρ b (e.symm (e (q t)))) = e (q t)
    rw [e.symm_apply_apply]
    congr 1
    change normalQuotientAction L (pPrimeCore 2 L) b (q t) = q t
    rw [normalQuotientAction_apply_mk]
    congr 1
    apply Subtype.ext
    change b * (t : G) * b⁻¹ = t
    have hcomm := (hc t (hTA (mem_map_of_mem L.subtype ht)) b hb).symm
    rw [hcomm.eq, mul_inv_cancel_right]
  obtain ⟨x, hx, he⟩ := Theory.PSL2.aut_fixing_sylow_inner P (MulAut.congr e (ρ b)) hfix
  have hx2 : x ^ 2 = 1 := congrArg Subtype.val (linear_sylow_square P ⟨x, hx⟩)
  have hbρ : ρ b ^ 2 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, he, ← map_pow, hx2, map_one]
  have hb2 : b ^ 2 = 1 := by
    have hh : (⟨b, hb⟩ : B) ^ 2 = 1 := by
      apply hi
      rw [map_pow, map_one]
      exact hbρ
    exact congrArg Subtype.val hh
  by_cases hb1 : b = 1
  · exact hb1 ▸ A.one_mem
  have hbL : b ∈ L := hBI b hb ⟨hb1, hb2⟩
  apply hTA
  refine ⟨⟨b, hbL⟩, ?_, rfl⟩
  rw [hT]
  exact hBS hb

/-- The binary PSL₂ quotient case of terminal factor placement. In fact the
terminal fusion conditions force nesting, contradicting incomparability. -/
theorem terminal_factors_le_span_linear
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (n : ℕ) (_hn : 2 ≤ n)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* PSL2BinaryMatrixGroup n) :
    A₁ ≤ closure (terminalInvolutions A₁ A₂) ∧
      A₂ ≤ closure (terminalInvolutions A₁ A₂) := by
  let L := closure (terminalInvolutions A₁ A₂)
  have hL : L.Normal := (terminalInvolutions_productDisconnected h f hp).closure_normal
  let := hL
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal L
  let U := (T : Subgroup L).map L.subtype
  have hU : (U : Set G) ⊆ (A₁ : Set G) ∪ A₂ := by
    rintro x ⟨t, ht, rfl⟩
    by_cases ht1 : (t : G) = 1
    · left
      change (t : G) ∈ A₁
      rw [ht1]
      exact A₁.one_mem
    have ht2 : (t : G) ^ 2 = 1 :=
      congrArg (fun z : T => ((z : L) : G)) (linear_span_sylow_square T e ⟨t, ht⟩)
    have htS : (t : G) ∈ (S : Subgroup G) := by
      rw [hT] at ht
      exact ht
    exact terminalInvolutions_mem_union f
      (terminal_involution_mem_distinguished h f hp hs t.property ⟨ht1, ht2⟩) htS
  have hc : ∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b := by
    intro a ha b hb
    exact ((mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp h.commute) ha)) b hb).symm
  have hi := terminalQuotientAction_factors_injective hL h hs
  exfalso
  rcases SubgroupClass.subset_union.mp hU with hU1 | hU2
  · exact h21 (linear_centralizing_factor_le hL T hT e A₁ A₂ h.right_le hU1 hc hi.2
      (fun b hb hbi => subset_closure (mem_terminalInvolutions (Or.inr hb) hbi)))
  · exact h12 (linear_centralizing_factor_le hL T hT e A₂ A₁ h.left_le hU2
      (fun b hb a ha => (hc a ha b hb).symm) hi.1
      (fun a ha hai => subset_closure (mem_terminalInvolutions (Or.inl ha) hai)))

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
