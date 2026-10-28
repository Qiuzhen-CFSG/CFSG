module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span

/-!
# The normal-closure transfer for the nested Asc75 case

The span argument supplies strong embedding in the normal involution span.  The
remaining transfer has two separate ingredients: involution fusion gives a
factorisation of the ambient group by the span and the intersection-generated
subgroup, and the nested-case argument must show that every involution of the
target intersection which lies in the normal closure is already in the span.
The latter absorption is kept explicit here; it is the source-theoretic
obligation which the nested-case source argument must discharge.

Source: M. Aschbacher, *On finite groups of component type* (1975),
Lemma 3.4, alternative (2), printed p.94 and final paragraph p.96;
GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
  BenderSuzuki.PFAppendixIII

universe u
variable {G : Type u} [Group G] [Finite G]
  {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

private theorem nested_involution_mem_terminal
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    {z : G} (hzL : z ∈ closure (terminalInvolutions A₁ A₂))
    (hz : IsInvolution z) : z ∈ terminalInvolutions A₁ A₂ := by
  let L := closure (terminalInvolutions A₁ A₂)
  obtain ⟨a, _, haZ, hai⟩ := terminalInvolutions_left_seed (A₂ := A₂) h.left_rank
  obtain ⟨g, hg⟩ := (terminal_stronglyEmbedded_in_span h f hp hs).involutions_conjugate
    (BenderSuzuki.IsInvolution.subtype hai (show a ∈ L from subset_closure haZ))
    (BenderSuzuki.IsInvolution.subtype hz hzL)
  have he : (g : G)⁻¹ * a * (g : G) = z := congrArg Subtype.val hg
  simpa only [MulAut.conj_apply, inv_inv, he] using
    terminalInvolutions_invariant (g : G)⁻¹ haZ

/-! The factorisation is the exact transport consequence of involution fusion.
It is useful independently of the absorption premise below. -/
theorem terminal_span_generated_factorization
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) (g : G) :
    ∃ l ∈ closure (terminalInvolutions A₁ A₂),
      ∃ m ∈ intersectionGenerated A₁ A₂, g = l * m := by
  let L := closure (terminalInvolutions A₁ A₂)
  obtain ⟨a, ha, haZ, hai⟩ := terminalInvolutions_left_seed (A₂ := A₂) h.left_rank
  have hzZ := terminalInvolutions_invariant g haZ
  obtain ⟨l, hl⟩ := (terminal_stronglyEmbedded_in_span h f hp hs).involutions_conjugate
    (BenderSuzuki.IsInvolution.subtype hai (show a ∈ L from subset_closure haZ))
    (BenderSuzuki.IsInvolution.subtype (terminalInvolutions_involutions hzZ)
      (show MulAut.conj g a ∈ L from subset_closure hzZ))
  have he : (l : G)⁻¹ * a * (l : G) = g * a * g⁻¹ := congrArg Subtype.val hl
  have hu := f.unique a (Or.inl ha) hai.ne_one
  have hm : (l : G) * g ∈ intersectionGenerated A₁ A₂ := by
    apply (hu.2 _).mp
    have hfix : ((l : G) * g)⁻¹ * a * ((l : G) * g) = a := by
      calc
        _ = g⁻¹ * ((l : G)⁻¹ * a * (l : G)) * g := by group
        _ = a := by rw [he]; group
    rw [hfix]
    exact hu.1
  exact ⟨(l : G)⁻¹, L.inv_mem l.property, (l : G) * g, hm, by group⟩

/-- Strong embedding transfers to the actual normal closure once the nested
case supplies absorption of its involutions into the involution span. -/
theorem terminal_stronglyEmbedded_in_normalClosure_of_involution_absorption
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (habs : ∀ z ∈ normalClosure (A₁ : Set G),
      z ∈ intersectionGenerated A₁ A₂ → IsInvolution z →
        z ∈ closure (terminalInvolutions A₁ A₂))
    : BenderSuzuki.IsStronglyEmbedded
      ((intersectionGenerated A₁ A₂).subgroupOf (normalClosure (A₁ : Set G))) := by
  let N := normalClosure (A₁ : Set G)
  let H := intersectionGenerated A₁ A₂
  have hLN := terminal_span_le_normalClosure_left h f hp hs
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    apply (terminal_stronglyEmbedded_in_span h f hp hs).ne_top
    exact subgroupOf_eq_top.mpr (hLN.trans (subgroupOf_eq_top.mp ht))
  · obtain ⟨a, ha, _, hai⟩ := terminalInvolutions_left_seed (A₂ := A₂) h.left_rank
    have haN : a ∈ N := subset_normalClosure ha
    exact ⟨⟨a, haN⟩, (f.unique a (Or.inl ha) hai.ne_one).1,
      BenderSuzuki.IsInvolution.subtype hai haN⟩
  · intro g hg x hxH hxg hxi
    have hi : IsInvolution (x : G) :=
      BenderSuzuki.IsInvolution.map_of_injective hxi N.subtype N.subtype_injective
    have hxL := habs x x.property hxH hi
    have hxZ := nested_involution_mem_terminal h f hp hs hxL hi
    have hu := terminalInvolutions_unique f hxZ hxH
    have hxconj := BenderSuzuki.rightConjugateElem_mem_of_mem_rightConjugate
      (g := g⁻¹) (by simpa only [inv_inv] using hxg)
    have hh : (g : G) * (x : G) * (g : G)⁻¹ ∈ H := by
      simpa only [rightConjugateElem, mem_subgroupOf, coe_mul, coe_inv, inv_inv] using hxconj
    apply hg
    change (g : G) ∈ H
    simpa only [inv_inv] using
      H.inv_mem ((hu.2 (g : G)⁻¹).mp (by simpa only [inv_inv] using hh))

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
