module
public import Theory.SpecificGroups.Alternating.FiveSquareFitting
public import Theory.GroupAction.ModelConjugation

/-!
# Sylow actions on an alternating-five square

The automorphism group of A₅ × A₅ has two-part 128. If the ambient
two-part is divisible by 256, a full Sylow preserving this square has
a nontrivial action kernel. An involution in that kernel centralizes the
whole square, so its centralizer order is divisible by 3600.

This supplies the involution-centralizer obstruction used for the Held
and Rudvalis containing components in Aschbacher–Smith 5.2.2, p.648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.FiveSquareFitting
open FiveSquareAutomorphisms
variable {G : Type*} [Group G] [Finite G]

/-- A sufficiently large full Sylow preserving A₅ × A₅ forces an actual
ambient involution centralizing that square. -/
theorem exists_involution_centralizer_square
    (hlarge : 2^8 ∣ Nat.card G) (S : Sylow 2 G) (W : Subgroup G)
    (hSW : (S : Subgroup G) ≤ normalizer (W : Set G)) (e : W ≃* Pair) :
    ∃ z : G, orderOf z = 2 ∧ 3600 ∣ Nat.card (centralizer ({z} : Set G)) := by
  let f := Theory.GroupAction.ModelConjugation.action (S : Subgroup G) W hSW e
  have hnon : ¬ Function.Injective f := by
    intro hi
    have hd := (S.pow_dvd_card_of_pow_dvd_card hlarge).trans (card_dvd_of_injective f hi)
    rw [card_automorphism] at hd
    norm_num at hd
  have hk : f.ker ≠ ⊥ := fun hh => hnon ((MonoidHom.ker_eq_bot_iff f).mp hh)
  have hp : IsPGroup 2 f.ker := S.isPGroup'.to_subgroup f.ker
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hnpos : 0 < n := by
    by_contra! hh
    have he : n = 0 := by omega
    exact hk (f.ker.eq_bot_of_card_eq (by simpa [he] using hn))
  have hd : 2 ∣ Nat.card f.ker := by
    rw [hn]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2 hd
  let zS : S := z.val
  let zG : G := zS.val
  have hzG : orderOf zG = 2 :=
    (orderOf_injective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective zS).trans
      ((orderOf_injective f.ker.subtype f.ker.subtype_injective z).trans hz)
  have hc : zG ∈ centralizer (W : Set G) :=
    ((SetLike.ext_iff.mp
      (Theory.GroupAction.ModelConjugation.action_ker (S : Subgroup G) W hSW e)) zS).mp z.property
  have hW : W ≤ centralizer ({zG} : Set G) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (hc w hw)
  have hcard : Nat.card W = 3600 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) = 3600
    rw [Nat.card_prod,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact ⟨zG,hzG,hcard ▸ card_dvd_of_le hW⟩

end Theory.SpecificGroups.Alternating.FiveSquareFitting
