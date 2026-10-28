module
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.PrimeOrderConjugation
public import Theory.GroupTheory.NormalizerActionFixer
/-!
# Prime actors moving perfect subgroups through a prime-group kernel

A prime-order subgroup that does not normalize a subgroup has trivial
intersection with its normalizer. Its conjugates are therefore indexed
injectively by that prime-order subgroup. If a homomorphism has a
prime-group kernel normalizing the perfect subgroup, the normalizer lifts
exactly; hence the actor retains both its order and its free conjugation
orbit in the image.

The kernel-normalization premise is essential. The Cartan application
proves it from the actual Sylow subgroup before quotienting by the local
two-core. Source: Aschbacher--Smith 5.1.13 and 5.2.2, pp.636 and 648.
-/

public section
open Subgroup
namespace Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- A prime-order actor moving a subgroup meets its normalizer trivially. -/
theorem prime_actor_disjoint_normalizer {A D : Subgroup G}
    (hp : (Nat.card D).Prime) (hmove : ¬ D ≤ normalizer (A : Set G)) :
    Disjoint D (normalizer (A : Set G)) := by
  let : Fact (Nat.card D).Prime := ⟨hp⟩
  rcases ((normalizer (A : Set G)).subgroupOf D).eq_bot_or_eq_top_of_prime_card with hb | ht
  · apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hx' : (⟨x,hx.1⟩ : D) ∈ (normalizer (A : Set G)).subgroupOf D := hx.2
    rw [hb] at hx'
    exact congrArg Subtype.val (mem_bot.mp hx')
  · exact (hmove (subgroupOf_eq_top.mp ht)).elim

/-- A normalized prime-group kernel loses neither the prime actor nor its movement. -/
theorem prime_actor_image_disjoint_normalizer {r : ℕ}
    (f : G →* Q) (A D : Subgroup G)
    (hA : IsPPerfect r A) (hk : IsPGroup r f.ker)
    (hn : f.ker ≤ normalizer (A : Set G))
    (hp : (Nat.card D).Prime) (hmove : ¬ D ≤ normalizer (A : Set G)) :
    Nat.card (D.map f) = Nat.card D ∧
      Disjoint (D.map f) (normalizer (A.map f : Set Q)) := by
  have hd := prime_actor_disjoint_normalizer hp hmove
  have hdis : Disjoint D f.ker := hd.mono_right hn
  have hi : Function.Injective (f.subgroupMap D) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply hdis.le_bot
    exact ⟨x.property,congrArg Subtype.val hx⟩
  let e := MulEquiv.ofBijective (f.subgroupMap D) ⟨hi,f.subgroupMap_surjective D⟩
  refine ⟨(Nat.card_congr e.toEquiv).symm,?_⟩
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  rintro y ⟨⟨x,hx,rfl⟩,hy⟩
  have hxN : x ∈ normalizer (A : Set G) := by
    rw [← comap_normalizer_map_of_pPerfect f A hA hk hn]
    exact hy
  change f x = 1
  rw [hd.le_bot ⟨hx,hxN⟩,map_one]

/-- The distinct conjugates are indexed injectively by the actual actor. -/
theorem conjugates_injective_of_disjoint_normalizer {A D : Subgroup G}
    (hd : Disjoint D (normalizer (A : Set G))) :
    Function.Injective (fun d : D => A.conjBy (d : G)) := by
  intro x y he
  have hn : (x : G)⁻¹ * y ∈ normalizer (A : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (conjBy_inv_mul_cancel A he)
  have hh := hd.le_bot ⟨D.mul_mem (D.inv_mem x.property) y.property,hn⟩
  exact Subtype.ext (inv_mul_eq_one.mp hh)

/-- Moving a subgroup faithfully forces a faithful action on any containing group. -/
theorem normalizer_action_injective_of_disjoint_normalizer
    {A D K : Subgroup G} (hAK : A ≤ K)
    (hDN : D ≤ normalizer (K : Set G))
    (hd : Disjoint D (normalizer (A : Set G))) :
    Function.Injective (K.normalizerMonoidHom.comp (inclusion hDN)) := by
  apply (K.normalizerMonoidHom.comp (inclusion hDN)).ker_eq_bot_iff.mp
  rw [normalizer_action_ker_comap]
  apply eq_bot_iff.mpr
  intro a ha
  apply Subtype.ext
  exact hd.le_bot ⟨a.property, centralizer_le_normalizer (A : Set G)
    (centralizer_le (show (A : Set G) ⊆ (K : Set G) from hAK) ha)⟩

end Subgroup
