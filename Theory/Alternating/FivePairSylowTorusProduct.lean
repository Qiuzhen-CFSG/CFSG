module
public import Theory.Alternating.FivePairBorelTorus
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# A full torus completes the Sylow normalizer above an A₅ pair

The Sylow normalizer in A₅ × A₅ has order 144. Its Sylow two-subgroup
has order sixteen, and a subgroup of order nine in that normalizer
complements it. For a surjection with two-group kernel the equality
lifts, since the kernel is already contained in the original Sylow.

Source application: Aschbacher–Smith 9.3.2, printed p.733, the equality
TD = DT obtained from the structure of the original A₅-pair section.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.AlternatingFive
local notation "A" => alternatingGroup (Fin 5)

/-- An order-nine torus and the Sylow generate the full Sylow normalizer,
retaining an arbitrary two-group kernel. -/
theorem pair_sylow_normalizer_eq_sup_torus_of_two_kernel
    {G : Type*} [Group G] [Finite G]
    (q : G →* A × A) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (P : Sylow 2 G) (D : Subgroup G) (hD : Nat.card D = 9)
    (hDP : D ≤ normalizer (P : Set G)) :
    normalizer (P : Set G) = (P : Subgroup G) ⊔ D := by
  let Q := P.mapSurjective hq
  let E := D.map q
  have hthree : IsPGroup 3 D := IsPGroup.of_card (n := 2) hD
  have hcE : Nat.card E = 9 := by
    have hi := injective_on_three_subgroup q hk D hthree
    have he := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
    rw [MonoidHom.range_comp, range_subtype] at he
    exact he.symm.trans hD
  have hm : (normalizer (P : Set G)).map q = normalizer (Q : Set (A × A)) :=
    P.normalizer_map_surjective q hq
  have hEQ : E ≤ normalizer (Q : Set (A × A)) := (map_mono hDP).trans_eq hm
  have hQcard : Nat.card Q = 16 := by
    rw [Q.card_eq_multiplicity, Nat.card_prod, nat_card_alternatingGroup, Nat.card_fin]
    decide +kernel
  have hjoin : (Q : Subgroup (A × A)) ⊔ E = normalizer (Q : Set (A × A)) := by
    apply eq_of_le_of_card_ge (sup_le (Q : Subgroup (A × A)).le_normalizer hEQ)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hEQ
      (IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ Q.isPGroup' (hthree.map q)), hcE]
    change Nat.card (normalizer (Q : Set (A × A))) ≤ Nat.card Q * 9
    rw [pair_sylow_normalizer_card, hQcard]
  have he : ((P : Subgroup G) ⊔ D).map q = (normalizer (P : Set G)).map q := by
    rw [Subgroup.map_sup, hm]
    exact hjoin
  have hker : q.ker ≤ (P : Subgroup G) := hk.le_sylow_of_normal P
  have he' := congrArg (Subgroup.comap q) he
  have hkerN : q.ker ≤ normalizer (P : Set G) := hker.trans (P : Subgroup G).le_normalizer
  have hkerJ : q.ker ≤ (P : Subgroup G) ⊔ D := hker.trans le_sup_left
  simpa only [comap_map_eq, sup_eq_left.mpr hkerJ, sup_eq_left.mpr hkerN] using he'.symm

end Theory.AlternatingFive
