module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base

/-!
# Noncommuting returning conjugates of the central HS involution

Two five-letter words in the original carrier generators conjugate `e0`
to rows 463 and 399 of the checked Sylow enumeration. Their products differ
at permutation point 1. The intrinsic identification of inner automorphisms
fixing the Sylow pointwise identifies the original two-central marker with
`e0` after Sylow transport. No other involution class is identified with it.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and the Bender inspection
in Proposition 2.2.2, pp.519--520 (combined 1 March 2004 manuscript).
The retained ATLAS HS tables use Lean's left permutation action.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.LeechRelated.HS
open EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData BlockNormalizer

private def markedA : Carrier := ⟨OrderCertificate.p0, by
  rw [OrderCertificate.a_eq_generator]
  exact generatorAElement.property⟩

private def markedB : Carrier := ⟨OrderCertificate.p1, by
  rw [OrderCertificate.b_eq_generator]
  exact generatorBElement.property⟩

private def firstConjugator : Carrier := markedA * markedB⁻¹ * markedA * markedB * markedA

private def secondConjugator : Carrier := markedB⁻¹ * markedB⁻¹ * markedA * markedB * markedA

private theorem row_check : ∀ p : Fin 100,
    ((firstConjugator * e0 * firstConjugator⁻¹ : Carrier) : Equiv.Perm (Fin 100)) p =
      point 463 p ∧
    ((secondConjugator * e0 * secondConjugator⁻¹ : Carrier) : Equiv.Perm (Fin 100)) p =
      point 399 p := by
  decide +kernel

private theorem noncommuting_check : point 463 (point 399 1) ≠ point 399 (point 463 1) := by
  decide +kernel

private theorem first_row : firstConjugator * e0 * firstConjugator⁻¹ = element 463 := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [element_point]
  exact (row_check p).1

private theorem second_row : secondConjugator * e0 * secondConjugator⁻¹ = element 399 := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [element_point]
  exact (row_check p).2

private theorem base_pair :
    ∃ a b : subgroup, IsConj e0 (a : Carrier) ∧
      IsConj e0 (b : Carrier) ∧ ¬Commute a b := by
  refine ⟨⟨element 463, element_mem 463⟩, ⟨element 399, element_mem 399⟩,
    isConj_iff.mpr ⟨firstConjugator, first_row⟩,
    isConj_iff.mpr ⟨secondConjugator, second_row⟩, ?_⟩
  intro h
  have he := congrArg (fun x : subgroup => ((x : Carrier) : Equiv.Perm (Fin 100)) 1) h.eq
  change (element 463 : Equiv.Perm (Fin 100)) ((element 399 : Equiv.Perm (Fin 100)) 1) =
    (element 399 : Equiv.Perm (Fin 100)) ((element 463 : Equiv.Perm (Fin 100)) 1) at he
  simp only [element_point] at he
  exact noncommuting_check he

private theorem central_marker_class (R : Sylow 2 Carrier)
    (v : Carrier) (_hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) : IsConj e0 v := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier R baseSylow
  let e := MulAut.conj g
  have hmap : (R : Subgroup Carrier).map e.toMonoidHom = subgroup :=
    congrArg Sylow.toSubgroup hg
  have hecentral : ∀ x ∈ subgroup, Commute (e v) x := by
    intro x hx
    have hxmap : x ∈ (R : Subgroup Carrier).map e.toMonoidHom := hmap.symm ▸ hx
    obtain ⟨y, hy, rfl⟩ := hxmap
    exact (hc y hy).map e.toMonoidHom
  have heq : e v = e0 := by
    apply MulAut.conj_injective_of_center_eq_bot center_carrier_eq_bot
    apply base_inner_eq_conj_e0
    · rw [MulAut.conj_orderOf_of_center_eq_bot center_carrier_eq_bot, e.orderOf_eq]
      exact ho
    · exact ⟨e v, rfl⟩
    · intro x hx
      change e v * x * (e v)⁻¹ = x
      rw [(hecentral x hx).eq]
      exact mul_inv_cancel_right x (e v)
  exact (isConj_iff.mpr ⟨g, heq⟩).symm

/-- Every original two-central HS marker has noncommuting conjugates in its
supplied Sylow subgroup, using two actual internal five-letter conjugators. -/
theorem sylow_noncommuting_conjugates (R : Sylow 2 Carrier)
    (v : Carrier) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) :
    ∃ a b : R, IsConj v (a : Carrier) ∧ IsConj v (b : Carrier) ∧ ¬Commute a b := by
  have hmarker := central_marker_class R v hv ho hc
  obtain ⟨a, b, ha, hb, hab⟩ := base_pair
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier baseSylow R
  let e := MulAut.conj g
  have hmap : subgroup.map e.toMonoidHom = (R : Subgroup Carrier) :=
    congrArg Sylow.toSubgroup hg
  have hmem (x : subgroup) : e (x : Carrier) ∈ R := by
    change e (x : Carrier) ∈ (R : Subgroup Carrier)
    rw [← hmap]
    exact mem_map_of_mem e.toMonoidHom x.property
  refine ⟨⟨e a, hmem a⟩, ⟨e b, hmem b⟩,
    hmarker.symm.trans (ha.trans (isConj_iff.mpr ⟨g, rfl⟩)),
    hmarker.symm.trans (hb.trans (isConj_iff.mpr ⟨g, rfl⟩)), ?_⟩
  intro hcomm
  apply hab
  have hh := hcomm.map (R : Subgroup Carrier).subtype
  change Commute (e (a : Carrier)) (e (b : Carrier)) at hh
  exact Subtype.ext (Commute.of_map e.injective hh).eq

end Sporadic.LeechRelated.HS
