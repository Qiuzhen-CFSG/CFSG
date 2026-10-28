module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.QuotientAction
public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Contract
public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Overgroup
public import Theory.GroupTheory.SetStrongClosureImage

/-!
# Unitary terminal placement

Transport the genuine quotient action through the supplied PSU₃ isomorphism
and restrict its codomain to its actual image. Surjective-image strong closure
puts the two factor images under the intrinsic commuting-pair specification.
An elementary smaller image lifts to an elementary smaller original factor:
both lifts lie in the involution span, and the action is injective on its
intersection with the fixed Sylow subgroup. Incomparability then contradicts
the model output. The ambient kernel is never asserted to have odd order.

The conditional transport theorem is retained as a separate interface. The
unconditional binary-unitary theorem discharges its model premise with the
proved automorphism-overgroup rigidity theorem, including the case q = 4.
It retains the actual quotient isomorphism, matrix-field order q² and
Hermitian fixed-field order q.

Source: Aschbacher (1975), Lemma 3.4, pp.94–96, terminal appeal to Theorem 3.3;
GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII

private theorem le_of_elementary_image_le
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q)
    (P L A B : Subgroup G) (hAP : A ≤ P) (hBP : B ≤ P)
    (hinjA : Function.Injective (φ.comp A.subtype))
    (hinjB : Function.Injective (φ.comp B.subtype))
    (hinjL : Function.Injective (φ.comp (P ⊓ L).subtype))
    (hAi : ∀ a ∈ A, IsInvolution a → a ∈ L)
    (hBi : ∀ b ∈ B, IsInvolution b → b ∈ L)
    (hAB : A.map φ ≤ B.map φ) (hA2 : ∀ a ∈ A.map φ, a ^ 2 = 1) : A ≤ B := by
  intro a ha
  obtain ⟨b, hb, he⟩ := hAB (mem_map_of_mem φ ha)
  have ha2 : a ^ 2 = 1 := by
    have heq : (⟨a, ha⟩ : A) ^ 2 = 1 := by
      apply hinjA
      rw [map_pow, map_one]
      exact hA2 (φ a) (mem_map_of_mem φ ha)
    exact congrArg Subtype.val heq
  have hb2 : b ^ 2 = 1 := by
    have heq : (⟨b, hb⟩ : B) ^ 2 = 1 := by
      apply hinjB
      rw [map_pow, map_one]
      change φ b ^ 2 = 1
      rw [he, ← map_pow, ha2, map_one]
    exact congrArg Subtype.val heq
  have haL : a ∈ L := by
    by_cases heq : a = 1
    · simp [heq]
    · exact hAi a ha ⟨heq, ha2⟩
  have hbL : b ∈ L := by
    by_cases heq : b = 1
    · simp [heq]
    · exact hBi b hb ⟨heq, hb2⟩
  have heq : (⟨b, hBP hb, hbL⟩ : (P ⊓ L : Subgroup G)) = ⟨a, hAP ha, haL⟩ := hinjL he
  have hba : b = a := congrArg Subtype.val heq
  exact hba ▸ hb

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Conditional reduction to the intrinsic unitary fusion input. -/
theorem terminal_factors_le_span_unitary_of_pair_rigidity
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    {E : Type*} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃*
        BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hcalc : J.StronglyClosedPairRigidity) :
    A₁ ≤ closure (terminalInvolutions A₁ A₂) ∧
      A₂ ≤ closure (terminalInvolutions A₁ A₂) := by
  let L := closure (terminalInvolutions A₁ A₂)
  have hL : L.Normal := (terminalInvolutions_productDisconnected h f hp).closure_normal
  let ρ := terminalQuotientAction hL
  let φ := (MulAut.congr e).toMonoidHom.comp ρ
  let ψ := φ.rangeRestrict
  let K := φ.range
  let T : Sylow 2 K := S.mapSurjective φ.rangeRestrict_surjective
  let B₁ := A₁.map ψ
  let B₂ := A₂.map ψ
  have hinj (A : Subgroup G) (hA : Function.Injective (ρ.comp A.subtype)) :
      Function.Injective (ψ.comp A.subtype) := by
    intro x y hxy
    apply hA
    apply (MulAut.congr e).injective
    exact congrArg Subtype.val hxy
  have hi₁ := hinj A₁ (terminalQuotientAction_factors_injective hL h hs).1
  have hi₂ := hinj A₂ (terminalQuotientAction_factors_injective hL h hs).2
  have hiL : Function.Injective (ψ.comp ((S : Subgroup G) ⊓ L).subtype) := by
    apply hinj
    exact terminalQuotientAction_injective_on_twoSubgroup hL h.left_rank hs _
      (S.isPGroup'.to_le inf_le_left) (fun _ hx _ => hx.2)
  have hinner : (MulAut.conj : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L) (e.symm x)
    refine ⟨l, ?_⟩
    change MulAut.congr e (terminalQuotientAction hL (l : G)) = MulAut.conj x
    rw [terminalQuotientAction_inner, hl]
    ext y
    simp [MulAut.congr, MulAut.conj_apply]
  have hrank (A : Subgroup G) (hA : TwoRankAtLeastTwo A)
      (hi : Function.Injective (ψ.comp A.subtype)) : TwoRankAtLeastTwo (A.map ψ) := by
    apply hA.map_of_injective (ψ.subgroupMap A)
    intro x y hxy
    apply hi
    exact congrArg Subtype.val hxy
  have hclosed : IsStronglyClosedSet ((B₁ : Set K) ∪ B₂) (T : Subgroup K) ⊤ := by
    have hh := f.closed.image S ψ φ.rangeRestrict_surjective
    simpa only [B₁, B₂, T, Set.image_union, coe_map, Sylow.coe_mapSurjective] using hh
  have hi : ∀ b : K, b ∈ (B₁ : Set K) ∪ B₂ → IsInvolution b →
      (b : MulAut (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) ∈
        (MulAut.conj : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
    have hgen (A : Subgroup G) (hin : Function.Injective (ψ.comp A.subtype))
        (hAL : ∀ a ∈ A, IsInvolution a → a ∈ L)
        (b : K) (hb : b ∈ A.map ψ) (hbi : IsInvolution b) :
        (b : MulAut (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) ∈
          (MulAut.conj : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
      obtain ⟨a, ha, rfl⟩ := hb
      have ha2 : (⟨a, ha⟩ : A) ^ 2 = 1 := by
        apply hin
        rw [map_pow, map_one]
        exact hbi.sq_eq_one
      have hai : IsInvolution a := ⟨fun he => hbi.ne_one (he ▸ ψ.map_one),
        congrArg Subtype.val ha2⟩
      let aL : L := ⟨a, hAL a ha hai⟩
      refine ⟨e (QuotientGroup.mk' _ aL), ?_⟩
      change MulAut.conj _ = MulAut.congr e (ρ a)
      rw [show ρ a = MulAut.conj (QuotientGroup.mk' _ aL) from terminalQuotientAction_inner hL aL]
      ext y
      simp [MulAut.congr, MulAut.conj_apply]
    intro b hb hbi
    rcases hb with hb | hb
    · exact hgen A₁ hi₁
        (fun _ ha hai => subset_closure (mem_terminalInvolutions (Or.inl ha) hai)) b hb hbi
    · exact hgen A₂ hi₂
        (fun _ ha hai => subset_closure (mem_terminalInvolutions (Or.inr ha) hai)) b hb hbi
  have hc : ⁅B₁, B₂⁆ = ⊥ := by
    change ⁅A₁.map ψ, A₂.map ψ⁆ = ⊥
    rw [← map_commutator, h.commute, Subgroup.map_bot]
  have hout := hcalc K hinner T B₁ B₂ (map_mono h.left_le) (map_mono h.right_le)
    hc (hrank A₁ h.left_rank hi₁) (hrank A₂ h.right_rank hi₂) hclosed hi
  rcases hout with ⟨hle, hsq⟩ | ⟨hle, hsq⟩
  · exact False.elim (h12 (le_of_elementary_image_le ψ _ L A₁ A₂ h.left_le h.right_le hi₁ hi₂ hiL
      (fun _ ha hai => subset_closure (mem_terminalInvolutions (Or.inl ha) hai))
      (fun _ ha hai => subset_closure (mem_terminalInvolutions (Or.inr ha) hai)) hle hsq))
  · exact False.elim (h21 (le_of_elementary_image_le ψ _ L A₂ A₁ h.right_le h.left_le hi₂ hi₁ hiL
      (fun _ ha hai => subset_closure (mem_terminalInvolutions (Or.inr ha) hai))
      (fun _ ha hai => subset_closure (mem_terminalInvolutions (Or.inl ha) hai)) hle hsq))

/-- The binary PSU₃ quotient case of terminal factor placement. The intrinsic
overgroup theorem forces nesting, contradicting the given incomparability. -/
theorem terminal_factors_le_span_unitary
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (n : ℕ) (hn : 2 ≤ n)
    {E : Type*} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2^n)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃*
        BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    A₁ ≤ closure (terminalInvolutions A₁ A₂) ∧
      A₂ ≤ closure (terminalInvolutions A₁ A₂) := by
  exact terminal_factors_le_span_unitary_of_pair_rigidity h f hp hs h12 h21 J e
    (BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs.stronglyClosedPairRigidity
      J hn hJ hcard hfixed)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end
