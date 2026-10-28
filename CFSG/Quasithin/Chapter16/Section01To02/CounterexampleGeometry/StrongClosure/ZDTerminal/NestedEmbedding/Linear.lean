module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Transfer
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.QuotientAction
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.LocalStructure
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.InvolutionSaturation
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CoprimeQuotientSubgroups


/-!
# Nested-factor absorption for a binary PSL₂ quotient

The Sylow intersection with the normal involution span has exponent two,
because its image is a PSL₂ Sylow subgroup and the quotient kernel has odd
order. Involution fusion and strong closure put this intersection in the
larger factor. The smaller factor centralizes it, so pointwise Sylow rigidity
and faithfulness of the factor action put the smaller factor in the span.
This completes the prescribed normal-closure absorption when A₁ ≤ A₂.

For A₂ ≤ A₁, the faithful quotient image of A₁ contains the whole inner Sylow
subgroup, and every involution of that image belongs to the inner Sylow.
The concrete automorphism saturation theorem puts this image in the inner
Sylow subgroup. Faithfulness then gives exponent two in A₁, placing A₁ in
the span. Normality gives absorption throughout the normal closure of A₁.
Both orientations retain that same normal closure; no assertion about the
ambient action kernel is used.

The Sylow lifting and pointwise-rigidity arguments adapt the private helpers
in `FactorAlternatives.SpanPlacement.Linear`, preserving that shared module.

Source: M. Aschbacher, *On finite groups of component type* (1975),
Lemma 3.4, printed pp.94–96; GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
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

private theorem linear_centralizing_factor_le_span
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (T : Sylow 2 (closure (terminalInvolutions A₁ A₂)))
    {n : ℕ}
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* PSL2BinaryMatrixGroup n)
    (A B : Subgroup G)
    (hTA : (T : Subgroup (closure (terminalInvolutions A₁ A₂))).map
      (closure (terminalInvolutions A₁ A₂)).subtype ≤ A)
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hi : Function.Injective ((terminalQuotientAction hL).comp B.subtype))
    (hBI : ∀ b ∈ B, IsInvolution b → b ∈ closure (terminalInvolutions A₁ A₂)) :
    B ≤ closure (terminalInvolutions A₁ A₂) := by
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
  · exact hb1 ▸ L.one_mem
  exact hBI b hb ⟨hb1, hb2⟩

private theorem linear_span_sylow_le_union
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (T : Sylow 2 (closure (terminalInvolutions A₁ A₂)))
    (hT : (T : Subgroup (closure (terminalInvolutions A₁ A₂))) =
      (S : Subgroup G).subgroupOf (closure (terminalInvolutions A₁ A₂)))
    {n : ℕ}
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* PSL2BinaryMatrixGroup n) :
    (((T : Subgroup (closure (terminalInvolutions A₁ A₂))).map
      (closure (terminalInvolutions A₁ A₂)).subtype : Subgroup G) : Set G) ⊆
        (A₁ : Set G) ∪ A₂ := by
  rintro x ⟨t, ht, rfl⟩
  by_cases ht1 : (t : G) = 1
  · left
    change (t : G) ∈ A₁
    rw [ht1]
    exact A₁.one_mem
  have ht2 : (t : G) ^ 2 = 1 :=
    congrArg (fun z : T => ((z : closure (terminalInvolutions A₁ A₂)) : G))
      (linear_span_sylow_square T e ⟨t, ht⟩)
  have htS : (t : G) ∈ (S : Subgroup G) := by rwa [hT] at ht
  exact terminalInvolutions_mem_union f
    (terminal_involution_mem_distinguished h f hp hs t.property ⟨ht1, ht2⟩) htS

/-- In the orientation where A₁ is the smaller factor, pointwise Sylow
rigidity puts every element of A₁ in the involution span. -/
theorem terminal_left_le_span_linear_of_le_right
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) (h12 : A₁ ≤ A₂)
    {n : ℕ}
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* PSL2BinaryMatrixGroup n) :
    A₁ ≤ closure (terminalInvolutions A₁ A₂) := by
  let L := closure (terminalInvolutions A₁ A₂)
  have hL : L.Normal := (terminalInvolutions_productDisconnected h f hp).closure_normal
  let := hL
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal L
  have hU := linear_span_sylow_le_union h f hp hs T hT e
  have hTA : (T : Subgroup L).map L.subtype ≤ A₂ := by
    intro x hx
    exact (hU hx).elim (fun ha => h12 ha) id
  apply linear_centralizing_factor_le_span hL T e A₂ A₁ hTA
  · intro b hb a ha
    exact (mem_centralizer_iff.mp
      ((commutator_eq_bot_iff_le_centralizer.mp h.commute) ha)) b hb
  · exact (terminalQuotientAction_factors_injective hL h hs).1
  · exact fun a ha hai => subset_closure (mem_terminalInvolutions (Or.inl ha) hai)

/-- The smaller-A₁ orientation already gives absorption in the prescribed
normal closure of A₁, without any further automorphism-model premise. -/
theorem terminal_involution_absorption_linear_of_le_right
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) (h12 : A₁ ≤ A₂)
    {n : ℕ}
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* PSL2BinaryMatrixGroup n) :
    ∀ z ∈ normalClosure (A₁ : Set G), z ∈ intersectionGenerated A₁ A₂ →
      IsInvolution z → z ∈ closure (terminalInvolutions A₁ A₂) := by
  let := (terminalInvolutions_productDisconnected h f hp).closure_normal
  have hN := normalClosure_le_normal
    (terminal_left_le_span_linear_of_le_right h f hp hs h12 e)
  exact fun _ hz _ _ => hN hz

private theorem linear_large_factor_le_span_of_automorphism_saturation
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) (h21 : A₂ ≤ A₁)
    {n : ℕ}
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* PSL2BinaryMatrixGroup n)
    (hmodel : ∀ (P : Sylow 2 (PSL2BinaryMatrixGroup n))
      (B : Subgroup (MulAut (PSL2BinaryMatrixGroup n))), IsPGroup 2 B →
      (P : Subgroup (PSL2BinaryMatrixGroup n)).map MulAut.conj ≤ B →
      (∀ b ∈ B, IsInvolution b →
        b ∈ (P : Subgroup (PSL2BinaryMatrixGroup n)).map MulAut.conj) →
      B ≤ (P : Subgroup (PSL2BinaryMatrixGroup n)).map MulAut.conj) :
    A₁ ≤ closure (terminalInvolutions A₁ A₂) := by
  let L := closure (terminalInvolutions A₁ A₂)
  have hL : L.Normal := (terminalInvolutions_productDisconnected h f hp).closure_normal
  let := hL
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal L
  have hU := linear_span_sylow_le_union h f hp hs T hT e
  have hTA : (T : Subgroup L).map L.subtype ≤ A₁ := by
    intro x hx
    exact (hU hx).elim id (fun ha => h21 ha)
  let q := QuotientGroup.mk' (pPrimeCore 2 L)
  let φ := e.toMonoidHom.comp q
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := T.mapSurjective hφ
  let ρ := (MulAut.congr e).toMonoidHom.comp (terminalQuotientAction hL)
  let B := A₁.map ρ
  have hi : Function.Injective (ρ.comp A₁.subtype) :=
    (MulAut.congr e).injective.comp (terminalQuotientAction_factors_injective hL h hs).1
  have hρ (l : L) : ρ (l : G) = MulAut.conj (φ l) := by
    change MulAut.congr e (terminalQuotientAction hL (l : G)) = _
    rw [terminalQuotientAction_inner, MulAut.congr_conj]
    rfl
  have hPB : (P : Subgroup (PSL2BinaryMatrixGroup n)).map MulAut.conj ≤ B := by
    rintro b ⟨p, hpP, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hpP
    exact ⟨t, hTA (mem_map_of_mem L.subtype ht), hρ t⟩
  have hBI : ∀ b ∈ B, IsInvolution b →
      b ∈ (P : Subgroup (PSL2BinaryMatrixGroup n)).map MulAut.conj := by
    rintro b ⟨a, ha, rfl⟩ hai
    have ha2 : (⟨a, ha⟩ : A₁) ^ 2 = 1 := by
      apply hi
      rw [map_pow, map_one]
      exact hai.sq_eq_one
    have haiG : IsInvolution a :=
      ⟨fun he => hai.ne_one (he ▸ ρ.map_one), congrArg Subtype.val ha2⟩
    have haL : a ∈ L := subset_closure (mem_terminalInvolutions (Or.inl ha) haiG)
    let aL : L := ⟨a, haL⟩
    have haT : aL ∈ (T : Subgroup L) := by rw [hT]; exact h.left_le ha
    exact ⟨φ aL, mem_map_of_mem φ haT, (hρ aL).symm⟩
  have hBP := hmodel P B ((S.isPGroup'.to_le h.left_le).map ρ) hPB hBI
  intro a ha
  obtain ⟨p, hpP, he⟩ := hBP (mem_map_of_mem ρ ha)
  have hp2 : p ^ 2 = 1 := congrArg Subtype.val (linear_sylow_square P ⟨p, hpP⟩)
  have haρ2 : ρ a ^ 2 = 1 := by rw [← he, ← map_pow, hp2, map_one]
  have ha2 : a ^ 2 = 1 := by
    have hh : (⟨a, ha⟩ : A₁) ^ 2 = 1 := by
      apply hi
      rw [map_pow, map_one]
      exact haρ2
    exact congrArg Subtype.val hh
  by_cases ha1 : a = 1
  · exact ha1 ▸ L.one_mem
  exact subset_closure (mem_terminalInvolutions (Or.inl ha) ⟨ha1, ha2⟩)

/-- Reduction of both nesting orientations to one concrete PSL₂ automorphism
lemma. The model premise has no reference to the ambient group, its odd core,
or its normal closure. The unconditional theorem below discharges it using
the intrinsic automorphism saturation theorem. -/
theorem terminal_nested_involution_absorption_linear_of_automorphism_saturation
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    (n : ℕ) (_hn : 2 ≤ n)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* PSL2BinaryMatrixGroup n)
    (hmodel : ∀ (P : Sylow 2 (PSL2BinaryMatrixGroup n))
      (B : Subgroup (MulAut (PSL2BinaryMatrixGroup n))), IsPGroup 2 B →
      (P : Subgroup (PSL2BinaryMatrixGroup n)).map MulAut.conj ≤ B →
      (∀ b ∈ B, IsInvolution b →
        b ∈ (P : Subgroup (PSL2BinaryMatrixGroup n)).map MulAut.conj) →
      B ≤ (P : Subgroup (PSL2BinaryMatrixGroup n)).map MulAut.conj) :
    ∀ z ∈ normalClosure (A₁ : Set G), z ∈ intersectionGenerated A₁ A₂ →
      IsInvolution z → z ∈ closure (terminalInvolutions A₁ A₂) := by
  rcases hn with h12 | h21
  · exact terminal_involution_absorption_linear_of_le_right h f hp hs h12 e
  · let := (terminalInvolutions_productDisconnected h f hp).closure_normal
    have hN := normalClosure_le_normal
      (linear_large_factor_le_span_of_automorphism_saturation h f hp hs h21 e hmodel)
    exact fun _ hz _ _ => hN hz

/-- For a binary PSL₂ quotient, every involution of the prescribed normal
closure lying in the intersection-generated subgroup lies in the involution
span. Both nesting orientations use the normal closure of A₁. -/
theorem terminal_nested_involution_absorption_linear
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    (n : ℕ) (hn₂ : 2 ≤ n)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* PSL2BinaryMatrixGroup n) :
    ∀ z ∈ normalClosure (A₁ : Set G), z ∈ intersectionGenerated A₁ A₂ →
      IsInvolution z → z ∈ closure (terminalInvolutions A₁ A₂) := by
  exact terminal_nested_involution_absorption_linear_of_automorphism_saturation
    h f hp hs hn n hn₂ e
    (BenderSuzuki.ZD.Linear.twoSubgroup_le_inner_sylow_of_involutions hn₂)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
