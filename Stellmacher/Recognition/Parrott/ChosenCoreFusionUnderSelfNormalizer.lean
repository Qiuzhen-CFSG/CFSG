module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaFiltration
public import Stellmacher.Recognition.Parrott.CoreOutsideDerivedOddAction
public import Theory.GroupTheory.SymmetricThreeQuotientInverter

/-!
# Excluding fusion of the supplied core involution

Under the second self-normalizer hypothesis and derived weak closure, the
chosen involution `a` cannot be conjugate to `z`. Assuming conjugacy, put
`S = C_G(z) ∩ C_G(a)`. The chosen centralizer geometry gives an S₃ quotient
of its normalizer and a characteristic index-two subgroup `Ω₁(S)`. Choose
an involution `w` in the derived two-core outside the supplied fixed join.
The quotient construction gives a three-subgroup inverted by this same `w`,
whose displacement on `Ω₁(S)` lies in `S′`. The Frattini filtration theorem
then forces the three-subgroup to centralize `z`, contradicting the order
of `C_G(z)`. The supplied fixed join and Sylow subgroup are retained.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and p.676, from “Next consider the case” to the odd-order
contradiction.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- The supplied core involution is not conjugate to z under the second
self-normalizer equality and derived weak closure. -/
public theorem parrott_not_isConj_second_involution_of_normalizer_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (z : G) (h : ParrottCentralizerHypotheses z)
    (d : ParrottSecondElementaryData z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z) :
    ¬ IsConj z (d.a : G) := by
  intro hconj
  let H := centralizer ({z} : Set G)
  let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
  let S := H ⊓ centralizer ({(d.a : G)} : Set G)
  let N := normalizer (S : Set G)
  let V := omega₁ S (p := 2)
  let : V.Characteristic := omega₁_characteristic S
  have hzS : z ∈ S := d.le_chosen_centralizer d.z_mem_inf.2
  have hS : IsPGroup 2 S := d.chosen_centralizer_isPGroup h
  have hequiv : Nonempty ((N ⧸ S.subgroupOf N) ≃* Equiv.Perm (Fin 3)) :=
    (d.chosen_center_card_eight_and_normalizer_quotient hns hN h hself hderived hconj).2
  obtain ⟨hindex, _, _, _, hdisplacement⟩ :=
    d.chosen_omega_filtration hns hN h hself hderived hconj
  obtain ⟨w, hwE, hwF, hw2, _, _⟩ :=
    d.chosen_centralizer_exists_center_moving_involution h
  obtain ⟨hwN, hwdisplacement⟩ := hdisplacement w hwE hwF
  let wN : N := ⟨w, hwN⟩
  have hwN2 : orderOf wN = 2 :=
    (orderOf_injective N.subtype N.subtype_injective wN).symm.trans hw2
  have hwNS : wN ∉ S.subgroupOf N := by
    intro hwS
    have hwEF : w ∈ E ⊓ d.F := d.inf_eq.symm ▸ ⟨hwE, hwS.2⟩
    exact hwF hwEF.2
  obtain ⟨Q, hQcard, hinverts⟩ :=
    exists_inverted_three_of_symmetric_three_quotient (S.subgroupOf N)
      hS.comap_subtype hequiv wN hwN2 hwNS
  have hQcardG : Nat.card (Q.map N.subtype) = 3 :=
    (card_map_of_injective N.subtype_injective).trans hQcard
  apply parrott_no_inverted_three_filtration z h S (Q.map N.subtype) hzS hS
    V hindex (map_subtype_le Q) hQcardG wN ?_ hwdisplacement
  rintro q ⟨q, hq, rfl⟩
  exact congrArg N.subtype (hinverts q hq)

end Stellmacher.Recognition
