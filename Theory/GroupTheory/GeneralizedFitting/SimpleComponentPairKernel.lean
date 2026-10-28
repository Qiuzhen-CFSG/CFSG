module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.DisjointCommutingProduct
public import Mathlib.GroupTheory.PGroup

/-!
# A kernel avoiding a pair of centerless components

A normal subgroup avoiding both components centralizes them by the
component dichotomy. The commuting centerless product has trivial center,
so the kernel intersects that product trivially. If the product has
two-group quotient, the kernel embeds in that quotient and is a two-group.

Source: the component calculus in Aschbacher--Smith A.1, applied in the
two-component Borel lift in 13.6.14, printed p.929.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem isTwoGroup_of_normal_avoiding_component_pair
    (A B N : Subgroup G) (hA : IsComponent G A) (hB : IsComponent G B)
    (hne : A ≠ B) (hZA : center A = ⊥) (hZB : center B = ⊥)
    [(A ⊔ B).Normal] [N.Normal] (hquot : IsPGroup 2 (G ⧸ (A ⊔ B)))
    (hAN : ¬ A ≤ N) (hBN : ¬ B ≤ N) : IsPGroup 2 N := by
  have hc : A ≤ centralizer (B : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hA.commutator_eq_bot_of_ne hB hne)
  have hd : Disjoint A B := by
    apply disjoint_def.mpr
    intro x hxA hxB
    have hz : (⟨x, hxA⟩ : A) ∈ center A := mem_center_iff.mpr fun a =>
      Subtype.ext ((hc a.property x hxB).symm)
    have he : (⟨x,hxA⟩ : A) = 1 := mem_bot.mp (hZA ▸ hz)
    exact congrArg (fun a : A => (a : G)) he
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  have hNA : N ≤ centralizer (A : Set G) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp ((hA.normal_dichotomy N).resolve_left hAN))
  have hNB : N ≤ centralizer (B : Set G) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp ((hB.normal_dichotomy N).resolve_left hBN))
  have hdis : Disjoint (A ⊔ B) N := by
    apply disjoint_def.mpr
    intro x hxD hxN
    obtain ⟨⟨a,b⟩, hab⟩ := e.surjective ⟨x,hxD⟩
    have hx : x = (a : G) * (b : G) := (congrArg Subtype.val hab).symm.trans (he a b)
    have haC : (a : G) ∈ centralizer (A : Set G) := by
      have hbC := (le_centralizer_iff.mp hc) b.property
      exact (centralizer (A : Set G)).mul_mem_cancel_right hbC |>.mp (hx ▸ hNA hxN)
    have hbC : (b : G) ∈ centralizer (B : Set G) :=
      (centralizer (B : Set G)).mul_mem_cancel_left (hc a.property) |>.mp (hx ▸ hNB hxN)
    have ha : a = 1 := mem_bot.mp (hZA ▸
      (show a ∈ center A from mem_center_iff.mpr fun c => Subtype.ext (haC c c.property)))
    have hb : b = 1 := mem_bot.mp (hZB ▸
      (show b ∈ center B from mem_center_iff.mpr fun c => Subtype.ext (hbC c c.property)))
    simpa only [ha,hb,coe_one,one_mul] using hx
  let f := (QuotientGroup.mk' (A ⊔ B)).comp N.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp hdis ((QuotientGroup.eq_one_iff _).mp hx) x.property
  exact hquot.of_injective f hf

end Theory.GroupTheory
