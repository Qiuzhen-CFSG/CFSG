module

public import CFSG.Quasithin.ChapterF.Section06.Elementary

/-!
# Odd images of the normal subgroup in the F.6.16 contradiction

When the ambient two-core is trivial, F.6.8 makes the actual normal subgroup
odd, rather than only its quotient by the two-core. Restrict the common Sylow
subgroup and show that this restriction is trivial; then use divisibility of
orders to pass oddness to any homomorphic image. This is the obstruction used
for the preimage of the quaternion two-core in the last paragraph of F.6.16.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
F.6.8 and proof of F.6.16, printed pp.305, 308–309.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

-- F.6.8 in the core-free situation, on the actual normal subgroup.
theorem odd_card_normal_of_local_intersections (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (W : Subgroup G) [W.Normal]
    (h₁ : G₁ ⊓ W ≤ (pCore 2 G₁).map G₁.subtype)
    (h₂ : G₂ ⊓ W ≤ (pCore 2 G₂).map G₂.subtype) : Odd (Nat.card W) := by
  obtain ⟨S, hS⟩ := h.subnormal_intersection_sylow W (Normal.isSubnormal inferInstance)
  have hb : (S : Subgroup W) = ⊥ := by
    rw [hS]
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    have hm := h.normal_intersection_le_twoCore W h₁ h₂ ⟨hx, x.property⟩
    simpa only [hcore, mem_bot, coe_one, subtype_apply] using hm
  have hn := S.not_dvd_index
  rw [hb, index_bot] at hn
  exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn)

theorem odd_card_image_of_local_intersections {J : Type*} [Group J]
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (W : Subgroup G) [W.Normal] (f : G →* J)
    (h₁ : G₁ ⊓ W ≤ (pCore 2 G₁).map G₁.subtype)
    (h₂ : G₂ ⊓ W ≤ (pCore 2 G₂).map G₂.subtype) : Odd (Nat.card (W.map f)) :=
  (odd_card_normal_of_local_intersections h hcore W h₁ h₂).of_dvd_nat (card_map_dvd W f)


end CFSG.Quasithin.ChapterF.Noncyclic
