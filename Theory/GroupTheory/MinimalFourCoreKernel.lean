module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Index

/-!
# Small normal images in an irreducible four-element core

A normal two-subgroup whose image has order at most two cannot have a
nontrivial image in a minimal normal four-element two-core. We state the
bound as an actual index-two subgroup contained in the kernel, so the
local geometry consumer retains its original pointwise kernel.

This repairs the index calculation in I.5.7(6), printed p.421: the
index-two subgroup belongs to Q₀, not Q₁.
-/

public section
namespace MonoidHom
open Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G]

theorem normal_two_le_ker_of_index_two
    (f : G →* H) (hf : Function.Surjective f)
    (Q N : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hNQ : N ≤ Q) (hNk : N ≤ f.ker) (hc : Nat.card Q = Nat.card N * 2)
    (hfour : Nat.card (pCore 2 H) = 4)
    (hmin : ∀ A : Subgroup H, A.Normal → A ≤ pCore 2 H → A = ⊥ ∨ A = pCore 2 H) :
    Q ≤ f.ker := by
  have hn : (Q.map f).Normal := Normal.map inferInstance f hf
  have hle : Q.map f ≤ pCore 2 H := le_sSup ⟨hn, hQ.map f⟩
  rcases hmin _ hn hle with hb | he
  · exact (map_eq_bot_iff Q).mp hb
  · have hNk' : N.subgroupOf Q ≤ (f.domRestrict Q).ker := by
      intro a ha
      exact hNk ha
    have hcard := card_le_of_le hNk'
    rw [Nat.card_congr (subgroupOfEquivOfLe hNQ).toEquiv] at hcard
    have hcount := (f.domRestrict Q).ker.card_mul_index
    rw [index_ker, domRestrict_range, he, hfour, hc] at hcount
    have hpos := Nat.card_pos (α := N)
    omega

end MonoidHom
