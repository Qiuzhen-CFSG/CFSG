module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.Borel
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Lifting field-torus movement to the original group

A field torus in J/O₂(J) which lifts into N_G(T) has an odd-order lift:
Schur--Zassenhaus splits the two-kernel of its full normalizer preimage.
If an element of X induces a nonidentity coefficient automorphism on that
torus, its commutators with this odd lift cannot all belong to T. Indeed
their images would have both odd and two-power order, forcing every field
unit, and hence the field, to be fixed.

The section below is geometric input, not a component-classification
theorem. Its quotient map is literally J → J/O₂(J). Its lift condition is
the invariant-Borel normalizer calculation still required in the Suzuki
and odd-degree linear branches. No normalization of T by X is assumed.
Source: Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection

private theorem odd_lift {H Q : Type*} [Group H] [Group Q] [Finite H]
    (f : H →* Q) (hk : IsPGroup 2 f.ker) (ho : Odd (Nat.card f.range)) :
    ∃ B : Subgroup H, Odd (Nat.card B) ∧ B.map f = f.range := by
  have hi : Odd f.ker.index := by rwa [index_ker]
  have hc : Nat.Coprime (Nat.card f.ker) f.ker.index := by
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn]
    exact hi.coprime_two_left.pow_left n
  obtain ⟨B, hB⟩ := exists_right_complement'_of_coprime hc
  refine ⟨B, ?_, le_antisymm (map_le_range _ _) ?_⟩
  · rw [← hB.symm.index_eq_card]
    exact hi
  · rintro _ ⟨h, rfl⟩
    obtain ⟨⟨k, b⟩, he⟩ := hB.2 h
    change (k : H) * b = h at he
    refine ⟨b, b.property, ?_⟩
    rw [← he, map_mul, show f k = 1 from k.property, one_mul]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- A coefficient torus in the actual two-core quotient, with normalizer
lifts and the literal conjugation action of one original Cartan element.
Model producers must construct these data from genuine quotient markings. -/
structure FieldTorusSection where
  J : Subgroup G
  le_Y : J ≤ E.Y
  field : BinaryField
  torus : field.Carrierˣ →* (J ⧸ pCore 2 J)
  injective : Function.Injective torus
  actor : normalizer (J : Set G)
  actor_mem : (actor : G) ∈ E.X
  coefficient : field.Carrier ≃+* field.Carrier
  nontrivial : coefficient ≠ 1
  action : ∀ u, coreQuotientAction J actor (torus u) =
    torus (Units.map coefficient.toMonoidHom u)
  lifts : ∀ u, ∃ j : J, (j : G) ∈ normalizer (T : Set G) ∧
    QuotientGroup.mk' (pCore 2 J) j = torus u

namespace FieldTorusSection
variable {E} (s : FieldTorusSection E)

/-- The full preimage of the coordinate torus inside the actual T-normalizer. -/
def normalizerPreimage : Subgroup s.J :=
  s.torus.range.comap (QuotientGroup.mk' (pCore 2 s.J)) ⊓
    (normalizer (T : Set G)).comap s.J.subtype

private theorem units_odd : Odd (Nat.card s.field.Carrierˣ) := by
  rw [Nat.card_units, s.field.card_eq, Nat.odd_iff]
  have hp := pow_pos (by decide : 0 < (2 : ℕ)) s.field.degree
  have hd := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt s.field.degree_pos))
  omega

/-- The odd lift covers every field parameter, with its original quotient map. -/
theorem exists_odd_lift : ∃ B : Subgroup G,
    B ≤ s.J ∧ B ≤ normalizer (T : Set G) ∧ Odd (Nat.card B) ∧
      ∀ u, ∃ b : s.J, (b : G) ∈ B ∧
        QuotientGroup.mk' (pCore 2 s.J) b = s.torus u := by
  let W := s.normalizerPreimage
  let q := QuotientGroup.mk' (pCore 2 s.J)
  let f := q.comp W.subtype
  have hr : f.range = s.torus.range := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact w.property.1
    · rintro _ ⟨u, rfl⟩
      obtain ⟨j, hjN, hj⟩ := s.lifts u
      exact ⟨⟨j, ⟨⟨u, hj.symm⟩, hjN⟩⟩, hj⟩
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 s.J).comap W.subtype := by
      ext w
      exact QuotientGroup.eq_one_iff _
    rw [he]
    exact (pCore_isPGroup (p := 2) (G := s.J)).comap_subtype
  have ho : Odd (Nat.card f.range) := by
    rw [hr, ← Nat.card_congr (MonoidHom.ofInjective s.injective).toEquiv]
    exact s.units_odd
  obtain ⟨C, hCo, hC⟩ := odd_lift f hk ho
  let j := s.J.subtype.comp W.subtype
  let B := C.map j
  have hj : Function.Injective j := s.J.subtype_injective.comp W.subtype_injective
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact c.val.property
  · rintro _ ⟨c, hc, rfl⟩
    exact c.property.2
  · rwa [card_map_of_injective hj]
  · intro u
    have hu : s.torus u ∈ C.map f := by rw [hC, hr]; exact ⟨u, rfl⟩
    obtain ⟨c, hc, he⟩ := hu
    exact ⟨c, mem_map_of_mem j hc, he⟩

/-- A nontrivial coefficient action gives the shared source BorelMovement.
Only the normalizer lift is used; X need not normalize T or the odd lift. -/
theorem borel_movement (s : FieldTorusSection E) : E.BorelMovement := by
  obtain ⟨B, hBJ, hBN, hBo, hcover⟩ := s.exists_odd_lift
  refine ⟨B, hBJ.trans s.le_Y, hBN, hBo, ?_⟩
  intro hcomm
  apply s.nontrivial
  have hfix (u : s.field.Carrierˣ) : Units.map s.coefficient.toMonoidHom u = u := by
    obtain ⟨b, hb, hbu⟩ := hcover u
    let c : s.J := s.J.normalizerMonoidHom s.actor b * b⁻¹
    have hcT : (c : G) ∈ (T : Subgroup G) :=
      hcomm (commutator_mem_commutator s.actor_mem hb)
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_pow_pow_eq_one ⟨c, hcT⟩
    have hcp : c ^ (2 ^ k) = 1 := Subtype.ext (congrArg (fun t : T => (t : G)) hk)
    have hq : QuotientGroup.mk' (pCore 2 s.J) c =
        s.torus (Units.map s.coefficient.toMonoidHom u * u⁻¹) := by
      rw [map_mul]
      rw [← coreQuotientAction_apply_mk, map_inv, hbu, s.action, map_mul, map_inv]
    have hu : (Units.map s.coefficient.toMonoidHom u * u⁻¹) ^ (2 ^ k) = 1 := by
      apply s.injective
      rw [map_pow, ← hq, ← map_pow, hcp, map_one, map_one]
    have he : Units.map s.coefficient.toMonoidHom u * u⁻¹ = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (s.units_odd.coprime_two_left.pow_left k)
        (orderOf_dvd_of_pow_eq_one hu) (orderOf_dvd_natCard _))
    exact mul_inv_eq_one.mp he
  ext a
  by_cases ha : a = 0
  · simp [ha]
  · exact congrArg Units.val (hfix (Units.mk0 a ha))

end FieldTorusSection
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection
