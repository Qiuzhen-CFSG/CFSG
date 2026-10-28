module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span

/-!
# Involution reductions for the factor alternatives in Asc75 Lemma 3.4

Strong embedding in the terminal involution span makes all its involutions
conjugate. Thus every involution of that span is distinguished, and those in
the fixed Sylow subgroup lie in the factor union. A product of involutions
exclusive to the two commuting factors would violate this union condition.
Consequently the involutions of one factor belong to the other, and their
intersection contains an elementary four. In particular the order-two
intersection in source alternative (3) is impossible under the terminal
fusion assumptions.

The same fusion assumptions put the fixed Sylow subgroup in H: a central
involution in its nontrivial normal intersection with the span has unique
conjugate membership in H. Each factor also meets the centralizer of the
span trivially. These are reductions toward subgroup containment; containment
of involutions alone does not establish containment of the whole factors.

Source: M. Aschbacher, *On finite groups of component type* (1975),
Lemma 3.4, pp.94–96, especially its final appeal to Theorem 3.3 on p.96;
GLS, Volume 4, Chapter 2, Theorem ZD.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Every involution in the terminal span belongs to the distinguished set. -/
theorem terminal_involution_mem_distinguished (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    {z : G} (hzL : z ∈ closure (terminalInvolutions A₁ A₂)) (hz : IsInvolution z) :
    z ∈ terminalInvolutions A₁ A₂ := by
  let L := closure (terminalInvolutions A₁ A₂)
  obtain ⟨a, ha, haZ, hai⟩ := terminalInvolutions_left_seed (A₂ := A₂) h.left_rank
  let aL : L := ⟨a, subset_closure haZ⟩
  let zL : L := ⟨z, hzL⟩
  obtain ⟨g, hg⟩ := (terminal_stronglyEmbedded_in_span h f hp hs).involutions_conjugate
    (BenderSuzuki.IsInvolution.subtype hai aL.property)
    (BenderSuzuki.IsInvolution.subtype hz zL.property)
  have he : (g : G)⁻¹ * a * (g : G) = z := congrArg Subtype.val hg
  simpa only [MulAut.conj_apply, inv_inv, he] using
    terminalInvolutions_invariant (g : G)⁻¹ haZ

private theorem mixed_involutions_mem_factor (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂)
    (hai : IsInvolution a) (hbi : IsInvolution b) : a ∈ A₂ ∨ b ∈ A₁ := by
  by_contra hn
  push Not at hn
  have hab : Commute a b :=
    ((mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp h.commute) ha)) b hb).symm
  have hne : a * b ≠ 1 := by
    intro he
    have he' : a = b := by simpa [hbi.inv_eq_self] using (mul_eq_one_iff_eq_inv.mp he)
    exact hn.1 (he' ▸ hb)
  have hi : IsInvolution (a * b) := ⟨hne, by rw [hab.mul_pow, hai.sq_eq_one, hbi.sq_eq_one, one_mul]⟩
  have hL : a * b ∈ closure (terminalInvolutions A₁ A₂) :=
    mul_mem (subset_closure (mem_terminalInvolutions (Or.inl ha) hai))
      (subset_closure (mem_terminalInvolutions (Or.inr hb) hbi))
  have hS : a * b ∈ (S : Subgroup G) := mul_mem (h.left_le ha) (h.right_le hb)
  rcases terminalInvolutions_mem_union f (terminal_involution_mem_distinguished h f hp hs hL hi) hS with habA | habB
  · exact hn.2 ((A₁.mul_mem_cancel_left ha).mp habA)
  · exact hn.1 ((A₂.mul_mem_cancel_right hb).mp habB)

/-- The involutions of one factor all lie in the other factor. -/
theorem terminal_factor_involutions_nested (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    (∀ a ∈ A₁, IsInvolution a → a ∈ A₂) ∨ (∀ a ∈ A₂, IsInvolution a → a ∈ A₁) := by
  classical
  by_cases hh : ∀ a ∈ A₁, IsInvolution a → a ∈ A₂
  · exact Or.inl hh
  · right
    push Not at hh
    obtain ⟨a, ha, hai, ha₂⟩ := hh
    intro b hb hbi
    exact (mixed_involutions_mem_factor h f hp hs ha hb hai hbi).resolve_left ha₂

omit [Finite G] in
private theorem rank_intersection {A B : Subgroup G}
    (hA : TwoRankAtLeastTwo A)
    (hh : ∀ a ∈ A, IsInvolution a → a ∈ B) : TwoRankAtLeastTwo (A ⊓ B : Subgroup G) := by
  obtain ⟨E, hE, hsq⟩ := hA
  have hmem : ∀ x : E, ((x : A) : G) ∈ A ⊓ B := by
    intro x
    refine ⟨(x : A).property, ?_⟩
    by_cases hx : x = 1
    · subst x; exact B.one_mem
    · exact hh _ (x : A).property ⟨fun he => hx (Subtype.ext (Subtype.ext he)),
        congrArg (fun y : E => ((y : A) : G)) (hsq x)⟩
  let φ : E →* (A ⊓ B : Subgroup G) :=
    { toFun := fun x => ⟨((x : A) : G), hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : (A ⊓ B : Subgroup G) => (z : G)) he))
  refine ⟨(⊤ : Subgroup E).map φ, ?_, ?_⟩
  · rw [card_map_of_injective hφ, card_top, hE]
  · rintro ⟨x, a, _, rfl⟩
    apply Subtype.ext
    change φ a ^ 2 = 1
    rw [← map_pow, hsq, map_one]

/-- The factor intersection contains an actual elementary four-group. -/
theorem terminal_intersection_twoRank (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) : TwoRankAtLeastTwo (A₁ ⊓ A₂ : Subgroup G) := by
  rcases terminal_factor_involutions_nested h f hp hs with h₁ | h₂
  · exact rank_intersection h.left_rank h₁
  · rw [inf_comm]; exact rank_intersection h.right_rank h₂

/-- The terminal fusion assumptions exclude the source exception, whose
intersection has order two. They do not yet prove factor containment. -/
theorem terminal_not_exceptional (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) : ¬ Exceptional A₁ A₂ := by
  intro he
  obtain ⟨E, hE, _⟩ := terminal_intersection_twoRank h f hp hs
  have hd := E.card_subgroup_dvd_card
  rw [hE, he.2.2] at hd
  norm_num at hd

/-- Each factor acts faithfully on the terminal span by conjugation: its
intersection with the pointwise centralizer is trivial. -/
theorem terminal_factors_inf_centralizer_span (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    A₁ ⊓ centralizer (closure (terminalInvolutions A₁ A₂) : Set G) = ⊥ ∧
    A₂ ⊓ centralizer (closure (terminalInvolutions A₁ A₂) : Set G) = ⊥ := by
  have he : ∀ x ∈ (A₁ : Set G) ∪ A₂,
      x ∈ centralizer (closure (terminalInvolutions A₁ A₂) : Set G) → x = 1 := by
    intro x hx hc
    by_contra hn
    apply (terminal_stronglyEmbedded_in_span h f hp hs).ne_top
    apply subgroupOf_eq_top.mpr
    intro g hg
    apply ((f.unique x hx hn).2 g).mp
    have hgx := mem_centralizer_iff.mp hc g hg
    rw [mul_assoc, ← hgx, inv_mul_cancel_left]
    exact (f.unique x hx hn).1
  constructor <;> apply le_antisymm _ bot_le
  · rintro x ⟨hx, hc⟩
    exact mem_bot.mpr (he x (Or.inl hx) hc)
  · rintro x ⟨hx, hc⟩
    exact mem_bot.mpr (he x (Or.inr hx) hc)

/-- A central involution of the Sylow intersection with the normal span
puts the entire fixed Sylow subgroup in the intersection-generated subgroup. -/
theorem terminal_sylow_le_intersectionGenerated (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) : (S : Subgroup G) ≤ intersectionGenerated A₁ A₂ := by
  let L := closure (terminalInvolutions A₁ A₂)
  have hL : L.Normal := (terminalInvolutions_productDisconnected h f hp).closure_normal
  let N := L.subgroupOf (S : Subgroup G)
  have hN : N.Normal := inferInstance
  obtain ⟨a, ha, haZ, hai⟩ := terminalInvolutions_left_seed (A₂ := A₂) h.left_rank
  have hNne : N ≠ ⊥ := by
    intro he
    have hh : (⟨a, h.left_le ha⟩ : S) ∈ N := subset_closure haZ
    rw [he, mem_bot] at hh
    exact hai.ne_one (congrArg Subtype.val hh)
  have hNt : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hNne
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  obtain ⟨Z, _, hZN, hZcard, hZcenter⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N hNt
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZcard])
  let t : G := ((z : S) : G)
  have ht : IsInvolution t := by
    have ho : orderOf t = 2 := by simpa [t] using hz
    exact ⟨(orderOf_eq_prime_iff.mp ho).2, (orderOf_eq_prime_iff.mp ho).1⟩
  have htL : t ∈ L := hZN z.property
  have htU := terminalInvolutions_mem_union f (terminal_involution_mem_distinguished h f hp hs htL ht)
    (z : S).property
  intro g hg
  apply ((f.unique t htU ht.ne_one).2 g).mp
  have hcomm : g * t = t * g :=
    congrArg Subtype.val (mem_center_iff.mp (hZcenter z.property) (⟨g, hg⟩ : S))
  simpa [← hcomm, mul_assoc] using (f.unique t htU ht.ne_one).1

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
