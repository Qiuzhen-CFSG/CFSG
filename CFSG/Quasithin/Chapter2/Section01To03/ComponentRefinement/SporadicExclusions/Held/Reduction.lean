module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions

/-!
# Reductions for the Held local calculation

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the proof of
2.3.9(7), printed p.526; GLS, volume 3, Table 5.3p, printed p.277.

The actual Held quotient is nontrivial, so quasisimplicity makes the two-core
of the component central. Its inner involution action then puts the embedded
two-core inside M. Neither argument makes that kernel trivial.

For the local groups of shape E₆₄.(3A₆.2), a block whose actual two-core
quotient is a triple cover of A₆ cannot be a χ₀ block: that quotient has order
1080, incompatible with all the concrete χ₀ models. This uses orders only to
exclude an isomorphism, never to identify a group or a representation.

`LocalGeometry` separates the construction and generation of the local family
from its subnormal-block calculation. No such family for Held is constructed
here, and the block obstruction below retains its local-calculation premise.
In particular these reductions do not prove the Held exclusion. The two
classes marked (↔) in Table 5.3p are fused by Aut(He), so choosing a single
E₆₄ normalizer requires an invariance proof for the supplied Sylow subgroup.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

open Subgroup ChapterC Theory.GroupTheory

variable {G : Type*} [Group G]

/-- The two-kernel in the actual Held quotient is central, but is not
discarded. Nontriviality is supplied by the concrete carrier. -/
theorem twoCore_le_center {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .he) :
    pCore 2 L ≤ center L := by
  let : IsQuasisimple L := h.quasisimple
  have e : (L ⧸ pCore 2 L) ≃* Held.He := d.quotientIso
  let : Nontrivial (L ⧸ pCore 2 L) := e.symm.injective.nontrivial
  rcases IsQuasisimple.normal_le_center_or_eq_top (pCore 2 L) with hc | ht
  · exact hc
  · exact (QuotientGroup.nontrivial_iff.mp inferInstance ht).elim

/-- The entire embedded two-kernel is retained inside M. -/
theorem twoCore_le_M {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .he) :
    L.pCoreIn 2 ≤ M := by
  exact (map_mono (twoCore_le_center h d)).trans
    (h.center_le_of_inner_action d.action d.conjugation d.inner)

variable {B : Type*} [Group B]

/-- The order of 3A₆ is incompatible with every χ₀ quotient. This is an
obstruction only, not recognition of an arbitrary group of order 1080. -/
theorem not_chiZero_of_quotient_card_1080
    (hq : Nat.card (B ⧸ pCore 2 B) = 1080) : ¬ IsChiZeroBlock B := by
  intro h
  rcases LieType.chiZero_order_module h with ⟨n, _, he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · have hn4 : n < 4 := by
      by_contra hn4
      have hl : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have hr : 2 ^ 8 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      have hp := Nat.mul_le_mul hl (Nat.sub_le_sub_right hr 1)
      rw [← he, hq] at hp
      norm_num at hp
    interval_cases n <;> norm_num [hq] at he
  · omega
  · omega

/-- An actual central quotient A₆ and a center of order three give the
order of its triple cover. Quasisimplicity is unnecessary for this count. -/
theorem card_of_triple_cover_altSix (hc : Nat.card (center B) = 3)
    (he : Nonempty ((B ⧸ center B) ≃* alternatingGroup (Fin 6))) :
    Nat.card B = 1080 := by
  obtain ⟨e⟩ := he
  have hq : Nat.card (B ⧸ center B) = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hm := (center B).card_mul_index
  change Nat.card (center B) * Nat.card (B ⧸ center B) = Nat.card B at hm
  rw [hc, hq] at hm
  exact hm.symm

/-- A local quotient with the actual central quotient A₆ and center of
order three cannot be the quotient of a χ₀ block. Central two-kernels
below that quotient remain arbitrary. -/
theorem not_chiZero_of_triple_cover_altSix
    (hc : Nat.card (center (B ⧸ pCore 2 B)) = 3)
    (he : Nonempty (((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃*
      alternatingGroup (Fin 6))) : ¬ IsChiZeroBlock B :=
  not_chiZero_of_quotient_card_1080 (card_of_triple_cover_altSix hc he)

/-- The exceptional A-hat₆ block is excluded by its actual acting quotient;
no dimension-only identification of its module is needed. -/
theorem not_chiZero_of_exceptionalAhatSix (h : IsExceptionalAhat6Block B) :
    ¬ IsChiZeroBlock B :=
  not_chiZero_of_triple_cover_altSix h.2.2.1 h.2.2.2.1

/-- Convert a calculation for all moved short subnormal subgroups into a
block obstruction. Subnormality is relative to K, and the triple-cover
alternative specifies the actual central quotient rather than a family tag. -/
theorem blockObstruction_of_triple_cover_altSix {M S K : Subgroup G} {z : G}
    (hc : centralizer ({z} : Set G) ≤ M)
    (hcalc : ∀ B : Subgroup K, B.IsSubnormal → IsShort B →
      B.map K.subtype = ⁅B.map K.subtype, Stellmacher.elementaryAbelianMaxJ S⁆ →
      B.map K.subtype ≤ centralizer ({z} : Set G) ∨
        pCore 2 B ≤ center B ∨
          (Nat.card (center (B ⧸ pCore 2 B)) = 3 ∧
            Nonempty (((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃*
              alternatingGroup (Fin 6)))) :
    BlockObstruction M S K := by
  intro B hb hm
  rcases hcalc B hb.1.subnormal hb.1.short hm with hfix | hcore | ⟨hcenter, he⟩
  · exact hfix.trans hc
  · exact (hb.1.short.blockU_ne_bot
      (commutator_top_right_eq_bot_iff_le_center.mpr hcore)).elim
  · exact (not_chiZero_of_triple_cover_altSix hcenter he hb.2).elim

/-- Construction contract for the actual local family, before the block
calculation. Its members contain the supplied S and have nontrivial
self-centralizing two-core. An inhabitant must be constructed from the
specified Held quotient and its actual action; this record is no such proof. -/
structure LocalGeometry (L S : Subgroup G) (z : G) where
  locals : Set (Subgroup G)
  generated : L ≤ centralizer ({z} : Set G) ⊔ sSup locals
  within : ∀ K ∈ locals, K ≤ L ⊔ S
  even : ∀ K ∈ locals, K ∈ Chapter1.HeOver G (S : Set G)

/-- Conditional final assembly. The constructor of the actual family and
the proof of every local block obstruction are separate obligations. -/
def LocalGeometry.toCentralizerBlockCover {L M S : Subgroup G} {z : G}
    (c : LocalGeometry L S z)
    (ho : ∀ K ∈ c.locals, BlockObstruction M S K) :
    CentralizerBlockCover L M S z where
  locals := c.locals
  generated := c.generated
  within := c.within
  even := c.even
  obstruction := ho

end CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

end
