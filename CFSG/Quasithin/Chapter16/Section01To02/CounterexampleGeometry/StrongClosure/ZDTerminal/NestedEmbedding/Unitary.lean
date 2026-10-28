module
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Transfer
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.QuotientAction

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Unitary.Action
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Unitary.Innerness
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Unitary.Kernel

/-!
# Involution absorption and strong embedding in the nested unitary case

There are two separate inputs: innerness of the original factor's
action on the span modulo its odd core, and odd order of the kernel of that
action inside the normal closure of A₁. Innerness alone does not control this
kernel. Under both inputs the normal closure equals the involution span:
modulo the span, its elements come from the odd kernel, whereas its original
generators form a two-group. Their quotient image is therefore trivial.

The unitary assembly proves both inputs from the actual projective unitary
model. `Unitary.Innerness` and `Unitary.Action` give innerness of both factor
actions, and `Unitary.Kernel` then proves oddness of the kernel inside the
normal closure. This discharges the absorption premise of the normal-closure
transfer and gives strong embedding in the normal closure of A₁ in either
nesting orientation. The conditional reductions remain available separately.

Source: Aschbacher (1975), Lemma 3.4, printed pp.94–96, terminal application
of Theorem 3.3; GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII

private theorem normalClosure_le_of_inner_image_of_odd_kernel
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    (A L : Subgroup G) [L.Normal] (ρ : G →* Q)
    (hA : IsPGroup 2 A) (hLN : L ≤ normalClosure (A : Set G))
    (himage : A.map ρ ≤ L.map ρ)
    (hodd : Odd (Nat.card (normalClosure (A : Set G) ⊓ ρ.ker : Subgroup G))) :
    normalClosure (A : Set G) ≤ L := by
  let N := normalClosure (A : Set G)
  let K := N ⊓ ρ.ker
  let q := QuotientGroup.mk' L
  let D := K.map q
  have hNK : N ≤ L ⊔ ρ.ker :=
    normalClosure_le_normal (map_le_map_iff.mp himage)
  have hND : ∀ x ∈ N, q x ∈ D := by
    intro x hx
    obtain ⟨l, hl, k, hk, he⟩ := mem_sup_of_normal_right.mp (hNK hx)
    have hkN : k ∈ N := by
      have hkx : k = l⁻¹ * x := by rw [← he]; group
      rw [hkx]
      exact N.mul_mem (N.inv_mem (hLN hl)) hx
    refine ⟨k, ⟨hkN, hk⟩, ?_⟩
    have hql : q l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [← he, map_mul, hql, one_mul]
  have hDo : Odd (Nat.card D) := hodd.of_dvd_nat (K.card_map_dvd q)
  have hAp : IsPGroup 2 (A.map q) := hA.map q
  obtain ⟨r, hr⟩ := hAp.exists_card_eq
  have hdis : Disjoint (A.map q) D := disjoint_of_coprime_natCard (by
    rw [hr]
    exact hDo.coprime_two_left.pow_left r)
  apply normalClosure_le_normal
  intro a ha
  apply (QuotientGroup.eq_one_iff a).mp
  exact hdis.le_bot ⟨mem_map_of_mem q ha, hND a (subset_normalClosure ha)⟩

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Inner factor action and an odd kernel in its normal closure imply equality
with the involution span. The normal closure remains that of A₁. -/
theorem terminal_normalClosure_eq_span_of_inner_action_of_odd_kernel
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (hi : A₁.map (terminalQuotientAction hL) ≤
      (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range)
    (hk : Odd (Nat.card (normalClosure (A₁ : Set G) ⊓
      (terminalQuotientAction hL).ker : Subgroup G))) :
    normalClosure (A₁ : Set G) = closure (terminalInvolutions A₁ A₂) := by
  let := hL
  have hLN := terminal_span_le_normalClosure_left h f hp hs
  apply le_antisymm ?_ hLN
  apply normalClosure_le_of_inner_image_of_odd_kernel A₁ _ (terminalQuotientAction hL)
    (S.isPGroup'.to_le h.left_le) hLN ?_ hk
  rwa [terminalQuotientAction_span_image]

/-- The exact absorption premise of the normal-closure transfer, under the
two independent quotient-action inputs. -/
theorem terminal_involution_absorption_of_inner_action_of_odd_kernel
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (hi : A₁.map (terminalQuotientAction hL) ≤
      (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range)
    (hk : Odd (Nat.card (normalClosure (A₁ : Set G) ⊓
      (terminalQuotientAction hL).ker : Subgroup G))) :
    ∀ z ∈ normalClosure (A₁ : Set G), z ∈ intersectionGenerated A₁ A₂ →
      IsInvolution z → z ∈ closure (terminalInvolutions A₁ A₂) := by
  intro z hz _ _
  rwa [← terminal_normalClosure_eq_span_of_inner_action_of_odd_kernel h f hp hs hL hi hk]

/-- Conditional unitary assembly. The intrinsic model calculation and the odd
kernel inside the normal closure are explicit, undischarged inputs. -/
theorem terminal_nested_involution_absorption_unitary_of_model_and_odd_kernel
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    {E : Type*} [Field E] [Finite E] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃*
        BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hcalc : UnitaryNestedPairInnerness J)
    (hk : let hL := (terminalInvolutions_productDisconnected h f hp).closure_normal
      Odd (Nat.card (normalClosure (A₁ : Set G) ⊓
        (terminalQuotientAction hL).ker : Subgroup G))) :
    ∀ z ∈ normalClosure (A₁ : Set G), z ∈ intersectionGenerated A₁ A₂ →
      IsInvolution z → z ∈ closure (terminalInvolutions A₁ A₂) := by
  exact terminal_involution_absorption_of_inner_action_of_odd_kernel h f hp hs _
    (terminal_nested_unitary_actions_inner_of_model h f hp hs hn J e hcalc).1 hk

/-- In the unitary model case, every involution of the intersection-generated
subgroup lying in the normal closure of A₁ belongs to the involution span.
Both the model innerness and the normal-closure kernel premises are discharged. -/
theorem terminal_nested_involution_absorption_unitary
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    (n : ℕ) (hn₂ : 2 ≤ n)
    {E : Type*} [Field E] [Finite E] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2^n)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃*
        BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    ∀ z ∈ normalClosure (A₁ : Set G), z ∈ intersectionGenerated A₁ A₂ →
      IsInvolution z → z ∈ closure (terminalInvolutions A₁ A₂) := by
  have hcalc := unitary_nested_pair_innerness J hn₂ hJ hcard hfixed
  have hinner := terminal_nested_unitary_actions_inner_of_model h f hp hs hn J e hcalc
  exact terminal_nested_involution_absorption_unitary_of_model_and_odd_kernel
    h f hp hs hn J e hcalc
    (terminal_nested_unitary_normalClosure_kernel_odd h f hp hs hn n hn₂
      J hJ hcard hfixed e hinner)

/-- The unitary branch of the nested strong-embedding conclusion of Asc75
Lemma 3.4, in the actual normal closure of A₁ in both nesting orientations. -/
theorem terminal_nested_stronglyEmbedded_in_normalClosure_unitary
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    (n : ℕ) (hn₂ : 2 ≤ n)
    {E : Type*} [Field E] [Finite E] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2^n)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃*
        BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    BenderSuzuki.IsStronglyEmbedded
      ((intersectionGenerated A₁ A₂).subgroupOf (normalClosure (A₁ : Set G))) := by
  exact terminal_stronglyEmbedded_in_normalClosure_of_involution_absorption h f hp hs
    (terminal_nested_involution_absorption_unitary h f hp hs hn n hn₂
      J hJ hcard hfixed e)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
