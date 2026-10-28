module
public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.GroupTheory.CyclicFifteen
public import Theory.ElementaryAbelian.Basic
public import Mathlib.RingTheory.IntegralDomain

/-!
# The order-fifteen obstruction for actions on sixteen elements

A normal five-subgroup has a centralizer of odd order in any faithful
action on a group of order sixteen. Conjugation therefore embeds each
elementary four-group in the cyclic group Aut(C5), which is impossible.
A normal subgroup of order fifteen supplies a normal five-subgroup via
its characteristic Sylow subgroup.

This is the finite-action obstruction in M. Aschbacher, “A 2-local
characterization of M12”, Lemma 3.1, printed p.36. The proof does not
require a classification of subgroups of GL4(2), or even commutativity
of the sixteen-element group.
-/

public section
open Subgroup
namespace SixteenOddComplements
variable {H V : Type*} [Group H] [Finite H] [Group V] [Finite V]

/-- A faithful action on sixteen elements with a normal five-subgroup
cannot contain an elementary four-group. -/
theorem no_four_of_normal_five
    (ρ : H →* MulAut V) (hρ : Function.Injective ρ) (hV : Nat.card V = 16)
    (F : Subgroup H) [F.Normal] (hF : Nat.card F = 5)
    (P : Subgroup H) [IsElementaryAbelian 2 P] (hP : Nat.card P = 4) : False := by
  let : MulDistribMulAction H V := MulDistribMulAction.compHom V ρ
  let : FaithfulSMul H V := ⟨by
    intro a b hab
    apply hρ
    ext v
    exact hab v⟩
  have hC := card_centralizer_five_dvd_fifteen (V := V) F hF hV
  have hd : Disjoint P (centralizer (F : Set H)) :=
    disjoint_of_coprime_natCard (by
      rw [hP]
      exact (show Nat.Coprime 4 15 by decide).of_dvd_right hC)
  let f : P →* MulAut F := F.normalizerMonoidHom.comp
    (inclusion (show P ≤ normalizer (F : Set H) by rw [F.normalizer_eq_top]; exact le_top))
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro a ha
    apply Subtype.ext
    apply disjoint_def.mp hd a.property
    have hk : (inclusion (show P ≤ normalizer (F : Set H) by
        rw [F.normalizer_eq_top]; exact le_top) a) ∈ F.normalizerMonoidHom.ker := ha
    rwa [normalizerMonoidHom_ker] at hk
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic F := isCyclic_of_prime_card hF
  let e : MulAut F ≃* (ZMod 5)ˣ := by
    have he := IsCyclic.mulAutMulEquiv F
    rw [hF] at he
    exact he
  let : IsCyclic (MulAut F) := isCyclic_of_injective e.toMonoidHom e.injective
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) hP
    (isCyclic_of_injective f hf)

/-- The order-fifteen obstruction needed after Burnside transfer. -/
theorem no_four_of_normal_fifteen
    (ρ : H →* MulAut V) (hρ : Function.Injective ρ) (hV : Nat.card V = 16)
    (J : Subgroup H) [J.Normal] (hJ : Nat.card J = 15)
    (P : Subgroup H) [IsElementaryAbelian 2 P] (hP : Nat.card P = 4) : False := by
  let : IsCyclic J := isCyclic_of_card_eq_fifteen hJ
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := 5) (G := J)
  have hS : Nat.card S = 5 := by
    rw [S.card_eq_multiplicity, hJ]
    decide +kernel
  let : (S : Subgroup J).Characteristic := S.characteristic_of_normal inferInstance
  let F := (S : Subgroup J).map J.subtype
  have hF : Nat.card F = 5 := (card_map_of_injective J.subtype_injective).trans hS
  exact no_four_of_normal_five ρ hρ hV F hF P hP

end SixteenOddComplements
end
