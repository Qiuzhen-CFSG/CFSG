module
public import Theory.GroupTheory.ComponentPairNormalizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Normality of a large centerless component

Distinct conjugates of a component commute. If its center is trivial,
their join is a direct product and has the square of the component order.
Thus a centerless component whose squared order exceeds the ambient order
is normal. This elementary component argument is used on a faithful
binary symplectic four-space in Aschbacher–Smith 14.3.14–15, p.994.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem IsComponent.normal_of_card_lt_sq {D : Subgroup G}
    (hD : IsComponent G D) (hz : center D = ⊥)
    (hcard : Nat.card G < Nat.card D ^ 2) : D.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  let E := D.map (MulAut.conj g).toMonoidHom
  have hc : ⁅D,E⁆ = ⊥ :=
    hD.commutator_eq_bot_of_ne (hD.map_conj g) (fun he => hne he.symm)
  have hd : Disjoint D E := disjoint_of_commuting_of_center_eq_bot hc hz
  have hn : E ≤ normalizer (D : Set G) := by
    apply le_trans _ (centralizer_le_normalizer (D : Set G))
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  have he : Nat.card E = Nat.card D :=
    card_map_of_injective (MulAut.conj g).injective
  have hj := card_sup_eq_mul_of_normalizes_of_disjoint D E hn hd
  have hle : Nat.card (D ⊔ E : Subgroup G) ≤ Nat.card G :=
    Nat.card_le_card_of_injective _ (D ⊔ E).subtype_injective
  rw [hj,he,←pow_two] at hle
  exact hcard.not_ge hle

end Theory.GroupTheory
