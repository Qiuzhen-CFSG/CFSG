module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoLocal
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoComplement.Binary

/-!
# Relators in elementary lifts of the literal J4 max1 core

The five words used by the binary extension certificate are identities in the
certified 24-star action. Its faithful identification with the action on the
actual core puts each word in that core. In any exponent-two core preimage,
the word lifts therefore centralize the whole preimage. The final application
keeps the original `localProjection` of a perfect central cover.

Source: the ATLAS `J4G1-max1W1` coordinate and star certificates;
Aschbacher–Smith I.1.1–I.1.5, printed pp.407–408, and GLS3 Section 6.1.
The words are multiplied in their displayed order, matching successive right
conjugation. No assertion that the local extension splits is used.
-/

@[expose] public section
namespace Janko4.TwoPrimary.InvariantComplement
open Cardinality Cardinality.QuotientCount Cardinality.QuotientCount.Image
open Subgroup

abbrev x : Local := localX matrixA_mul_self matrixB_pow_four
abbrev y : Local := localY matrixA_mul_self matrixB_pow_four

/-- A positive group word, in exactly the order used for right conjugation. -/
def wordValue {G : Type*} [Group G] (a b : G) (w : List Bool) : G :=
  (w.map fun s => if s then b else a).prod

theorem map_wordValue {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b : G) (w : List Bool) : f (wordValue a b w) = wordValue (f a) (f b) w := by
  simp only [wordValue, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  cases s <;> rfl

private noncomputable def starProjection : Local →* Equiv.Perm (Fin 24) :=
  StarGroup.subtype.comp ((actionImageEquivStarGroup matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
    (action matrixA_mul_self matrixB_pow_four).rangeRestrict)

private theorem starProjection_x : starProjection x = starX :=
  actionImageEquivStarGroup_x matrixA_mul_self matrixB_pow_four
private theorem starProjection_y : starProjection y = starY :=
  actionImageEquivStarGroup_y matrixA_mul_self matrixB_pow_four

private theorem starProjection_ker : starProjection.ker = Core := by
  rw [starProjection, MonoidHom.ker_comp_of_injective _ _ StarGroup.subtype_injective,
    MonoidHom.ker_comp_of_injective _ _
      (actionImageEquivStarGroup matrixA_mul_self matrixB_pow_four).injective]
  rw [MonoidHom.ker_rangeRestrict]
  exact LocalStructure.action_ker_eq_localKernel matrixA_mul_self matrixB_pow_four

set_option maxRecDepth 10000 in
private theorem star_relators : ∀ r : Fin 5, wordValue starX starY (relator r) = 1 := by
  decide +kernel

/-- These are relations of the actual M24 quotient; the group words themselves
need only lie in the elementary core. -/
theorem relator_mem_core (r : Fin 5) : wordValue x y (relator r) ∈ Core := by
  rw [← starProjection_ker, MonoidHom.mem_ker, map_wordValue,
    starProjection_x, starProjection_y]
  exact star_relators r

variable {L : Type*} [Group L]

/-- Exponent two makes the entire core preimage abelian. -/
theorem elementary_preimage_commute (q : L →* Local) (he : ElementaryPreimage q)
    {a b : L} (ha : q a ∈ Core) (hb : q b ∈ Core) : Commute a b := by
  have inv (g : L) (hg : q g ∈ Core) : g⁻¹ = g :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using he g hg)
  have hab : q (a * b) ∈ Core := by rw [map_mul]; exact Core.mul_mem ha hb
  show a * b = b * a
  calc
    a * b = (a * b)⁻¹ := (inv (a * b) hab).symm
    _ = b * a := by rw [mul_inv_rev, inv b hb, inv a ha]

/-- Every relator lift acts trivially on the elementary preimage. This is the
literal group-theoretic premise of the binary lower-row certificate. -/
theorem lifted_relator_conj (q : L →* Local) (he : ElementaryPreimage q)
    (a b : L) (ha : q a = x) (hb : q b = y) (r : Fin 5)
    (n : L) (hn : q n ∈ Core) :
    (wordValue a b (relator r))⁻¹ * n * wordValue a b (relator r) = n := by
  have hw : q (wordValue a b (relator r)) ∈ Core := by
    rw [map_wordValue, ha, hb]
    exact relator_mem_core r
  have hc := elementary_preimage_commute q he hw hn
  rw [mul_assoc, ← hc.eq, inv_mul_cancel_left]

/-- The relator identities apply to the original restricted covering map,
with the source's elementary-preimage hypothesis retained verbatim. -/
theorem localProjection_relator_conj {E : Type*} [Group E]
    (f : PerfectCentralCovering.Cover E Model) (he : ElementaryPreimage (localProjection f)) :
    ∃ a b : Local.comap f.toMonoidHom,
      localProjection f a = x ∧ localProjection f b = y ∧
        ∀ (r : Fin 5) (n : Local.comap f.toMonoidHom),
          localProjection f n ∈ Core →
            (wordValue a b (relator r))⁻¹ * n * wordValue a b (relator r) = n := by
  have hq := f.toMonoidHom.subgroupComap_surjective_of_surjective Local f.surjective
  obtain ⟨a, ha⟩ := hq x
  obtain ⟨b, hb⟩ := hq y
  exact ⟨a, b, ha, hb, fun r n hn => lifted_relator_conj _ he a b ha hb r n hn⟩

end Janko4.TwoPrimary.InvariantComplement
