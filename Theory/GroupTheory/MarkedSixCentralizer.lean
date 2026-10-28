module
public import Theory.GroupTheory.NoncentralThreeOrderSix
public import Theory.SpecificGroups.SymmetricFourSylowFixedPoint
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Mathlib.GroupTheory.Perm.Centralizer

/-! An actual subgroup of order six containing an involution with centralizer
order eight is symmetric three, and excludes symmetric four as ambient group. -/
public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {X : Type*} [Group X] [Finite X]

/-- The original order-six subgroup is S3 when its marked element has full
centralizer order eight. The equivalence retains that literal subgroup. -/
theorem marked_six_equiv_perm_three (H : Subgroup X) (hH : Nat.card H=6)
    (u : X) (hu : u∈H) (hC : Nat.card (centralizer ({u} : Set X))=8) :
    Nonempty (H≃*Equiv.Perm (Fin 3)) := by
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' (G:=H) 3 (by rw [hH]; decide)
  apply nonempty_perm_three_of_card_six_noncentral_three hH r hr
  intro hc
  have hru : (r : X)∈centralizer ({u} : Set X) :=
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_center_iff.mp hc (⟨u,hu⟩ : H))).symm
  have hd := orderOf_dvd_natCard
    (⟨r,hru⟩ : centralizer ({u} : Set X))
  rw [orderOf_mk,orderOf_coe r,hr,hC] at hd
  norm_num at hd

set_option maxRecDepth 10000 in
private theorem fixed_involution_cycle : ∀ a : Equiv.Perm (Fin 4),
    a^2=1 → a≠1 → (∃ i,a i=i) → a.cycleType={2} := by
  decide +kernel

omit [Finite X] in
/-- A marked involution with centralizer eight cannot lie in an order-six
subgroup of an ambient group isomorphic to S4. -/
theorem not_perm_four_of_marked_six (H : Subgroup X) (hH : Nat.card H=6)
    (u : X) (hu : u∈H) (hu2 : orderOf u=2)
    (hC : Nat.card (centralizer ({u} : Set X))=8) :
    ¬Nonempty (X≃*Equiv.Perm (Fin 4)) := by
  rintro ⟨e⟩
  let K := H.map e.toMonoidHom
  have hK : Nat.card K=6 := (card_map_of_injective e.injective).trans hH
  obtain ⟨i,hi⟩ := SymmetricFour.exists_fixed_of_card_eq_six K hK
  have hfix : e u i=i := hi ⟨e u,mem_map_of_mem _ hu⟩
  have heu : orderOf (e u)=2 := (e.orderOf_eq u).trans hu2
  have hcycle := fixed_involution_cycle (e u) (heu ▸ pow_orderOf_eq_one (e u))
    (fun he => by simp [he] at heu) ⟨i,hfix⟩
  have hc : Nat.card (centralizer ({e u} : Set (Equiv.Perm (Fin 4))))=8 :=
    (Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv e u).toEquiv).symm.trans hC
  rw [Equiv.Perm.nat_card_centralizer,hcycle] at hc
  norm_num at hc

end Theory.GroupTheory
