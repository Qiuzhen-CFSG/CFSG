module
public import Theory.Alternating.FivePairBorelTorus
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
/-!
# A cubic completes the Sylow normalizer above A₅

A quotient onto A₅ with two-group kernel carries the original Sylow
normalizer onto an A₄ of order twelve. Every cubic in that normalizer is
faithful modulo the kernel and complements the image Sylow four-group.
The kernel lies in the original Sylow, so the equality lifts without
splitting or discarding any covering layer.

Source application: Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.AlternatingFive
local notation "A" => alternatingGroup (Fin 5)
private theorem normalizer_card_twelve (P : Sylow 2 A) :
    Nat.card (normalizer (P : Set A))=12 := by
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P
  rw [hi,Nat.card_eq_fintype_card]
  clear P hi
  revert i
  decide +kernel

/-- The actual Sylow and its cubic generate the full normalizer. -/
theorem sylow_normalizer_eq_sup_cubic_of_two_kernel
    {G : Type*} [Group G] [Finite G]
    (q : G →* A) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (P : Sylow 2 G) (D : Subgroup G) (hD : Nat.card D=3)
    (hDP : D ≤ normalizer (P : Set G)) :
    normalizer (P : Set G) = (P : Subgroup G) ⊔ D := by
  let Q := P.mapSurjective hq
  let E := D.map q
  have hthree : IsPGroup 3 D := IsPGroup.of_card (n:=1) (by simpa using hD)
  have hcE : Nat.card E=3 := by
    have hi := injective_on_three_subgroup q hk D hthree
    have he : Nat.card E=Nat.card D := by
      have he := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
      rw [MonoidHom.range_comp,range_subtype] at he
      exact he.symm
    exact he.trans hD
  have hm : (normalizer (P : Set G)).map q=normalizer (Q : Set A) :=
    P.normalizer_map_surjective q hq
  have hEQ : E ≤ normalizer (Q : Set A) := (map_mono hDP).trans_eq hm
  have hQcard : Nat.card Q=4 := by
    rw [Q.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel
  have hjoin : (Q : Subgroup A) ⊔ E = normalizer (Q : Set A) := by
    apply eq_of_le_of_card_ge (sup_le (Q : Subgroup A).le_normalizer hEQ)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hEQ
      (IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ Q.isPGroup' (hthree.map q)),hcE]
    change Nat.card (normalizer (Q : Set A)) ≤ Nat.card Q * 3
    rw [normalizer_card_twelve,hQcard]
  have he : ((P : Subgroup G) ⊔ D).map q=(normalizer (P : Set G)).map q := by
    rw [Subgroup.map_sup,hm]
    exact hjoin
  have hker : q.ker ≤ (P : Subgroup G) := hk.le_sylow_of_normal P
  have he' := congrArg (Subgroup.comap q) he
  have hkerN : q.ker ≤ normalizer (P : Set G) := hker.trans (P : Subgroup G).le_normalizer
  have hkerJ : q.ker ≤ (P : Subgroup G) ⊔ D := hker.trans le_sup_left
  simpa only [comap_map_eq,sup_eq_left.mpr hkerJ,sup_eq_left.mpr hkerN] using he'.symm
end Theory.AlternatingFive
