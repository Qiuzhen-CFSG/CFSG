module
public import Theory.SpecificGroups.SymmetricFourWreath.CentralFactorSquareAction
public import Theory.GroupTheory.FrattiniNormalizerWitness
public import Theory.ElementaryAbelian.ExtraspecialEquiv
/-!
# Ambient transport of the intrinsic square-action kernel

If an ambient two-subgroup R is marked as (D8 wr C2) × Di and its quaternion
extraspecial Q is normal in R, then the square action of R on E=Q D has
kernel exactly E. The pointwise criterion applies to ambient elements of R
and to any chosen product coordinates E ≃ Q×D. It transports the intrinsic
central-quotient calculation without assuming the coordinates intertwine
conjugation.

Source: Aschbacher--Smith, 2.4.29, printed p.545.
-/
@[expose] public section
open Subgroup
namespace SymmetricFourWreath

variable {G Di : Type*} [Group G] [Finite G] [Group Di] [Finite Di]
  [IsElementaryAbelian 2 Di]

theorem ambient_square_action_eq_one_iff
    (R Q D : Subgroup G) [IsElementaryAbelian 2 D]
    (hQR : Q ≤ R) (hDR : D ≤ R) (hRQ : R ≤ normalizer (Q : Set G))
    (hn : R ≤ normalizer ((Q ⊔ D : Subgroup G) : Set G))
    (e : R ≃* P × Di)
    (hmark : ((MonoidHom.fst P Di).comp e.toMonoidHom).ker = D.subgroupOf R)
    (d : QuaternionCentralProductData Q) (eE : (Q ⊔ D : Subgroup G) ≃* Q × D)
    (s : R) :
    d.centralFactorWreathAction eE
      ((Q ⊔ D : Subgroup G).normalizerMonoidHom ⟨s,hn s.property⟩) = 1 ↔
      (s : G) ∈ Q ⊔ D := by
  let Qi := Q.subgroupOf R
  let E := Q ⊔ D
  have hER : E ≤ R := sup_le hQR hDR
  let : Qi.Normal := (normal_subgroupOf_iff_le_normalizer hQR).mpr hRQ
  let : IsExtraspecial 2 Qi := IsExtraspecial.of_mulEquiv (subgroupOfEquivOfLe hQR).symm d.extraspecial
  let : (E.subgroupOf R).Normal := (normal_subgroupOf_iff_le_normalizer hER).mpr hn
  have hc : Nat.card Qi = 32 := (Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv).trans d.card
  have hE : extendedCore e Qi = E.subgroupOf R := by
    change Qi ⊔ ((MonoidHom.fst P Di).comp e.toMonoidHom).ker = _
    rw [hmark,subgroupOf_sup hQR hDR]
  have hk := extendedCore_quotient_action_ker e Qi hc
  have ht : quotientAut (center (extendedCore e Qi)) (MulAut.conjNormal s) = 1 ↔
      s ∈ extendedCore e Qi := by
    change s ∈ ((quotientAut (center (extendedCore e Qi))).comp
      (MulAut.conjNormal : R →* MulAut (extendedCore e Qi))).ker ↔ _
    rw [hk]
  let j : extendedCore e Qi ≃* E := (MulEquiv.subgroupCongr hE).trans (subgroupOfEquivOfLe hER)
  have hi : quotientAut (center (extendedCore e Qi)) (MulAut.conjNormal s) = 1 ↔
      quotientAut (center E) (E.normalizerMonoidHom ⟨s,hn s.property⟩) = 1 := by
    rw [quotientAut_eq_one_iff_displacements,quotientAut_eq_one_iff_displacements]
    constructor
    · intro h x
      exact (centerCongr j ⟨_,h (j.symm x)⟩).property
    · intro h x
      exact (centerCongr j.symm ⟨_,h (j x)⟩).property
  have ha : d.centralFactorWreathAction eE
      (E.normalizerMonoidHom ⟨s,hn s.property⟩) = 1 ↔
      quotientAut (center E) (E.normalizerMonoidHom ⟨s,hn s.property⟩) = 1 := by
    change (E.normalizerMonoidHom ⟨s,hn s.property⟩) ∈ (d.centralFactorWreathAction eE).ker ↔ _
    rw [d.centralFactorWreathAction_ker]
    rfl
  apply (ha.trans (hi.symm.trans ht)).trans
  rw [hE]
  rfl
theorem ambient_square_action_ker
    (R Q D : Subgroup G) [IsElementaryAbelian 2 D]
    (hQR : Q ≤ R) (hDR : D ≤ R) (hRQ : R ≤ normalizer (Q : Set G))
    (hn : R ≤ normalizer ((Q ⊔ D : Subgroup G) : Set G))
    (e : R ≃* P × Di)
    (hmark : ((MonoidHom.fst P Di).comp e.toMonoidHom).ker = D.subgroupOf R)
    (d : QuaternionCentralProductData Q) (eE : (Q ⊔ D : Subgroup G) ≃* Q × D) :
    ((d.centralFactorWreathAction eE).comp
      ((Q ⊔ D : Subgroup G).normalizerMonoidHom.comp (inclusion hn))).ker =
      (Q ⊔ D : Subgroup G).subgroupOf R := by
  ext s
  exact ambient_square_action_eq_one_iff R Q D hQR hDR hRQ hn e hmark d eE s

end SymmetricFourWreath
