module
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Parabolics
import all Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Parabolics
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.Mathieu.M22.CentralCover.HexadPerfect

/-!
# The two cubic subgroups of a native M₂₂ hexad

The marked pair stabilizer inside the hexad and its three-pair partition
stabilizer contain the same Sylow two-subgroup with index three. Their
ordinary maximality and different pair geometry show that they generate the
hexad stabilizer. The first S₃ quotient is its action on the three matchings
of the remaining four points; the second is the existing three-pair action.
The small normalizer certificate works only on the six hexad points.

Source: Aschbacher–Smith 14.3.6(6), printed p.994, and the native hexad
geometry of 2.3.9(7)(f). The join is the hexad stabilizer, not all of M₂₂.
-/

public section
open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22CubicHexad
open M22ValueBound.Concrete M22ValueBound.Concrete.PartitionStructure M22SolvableSylow

private abbrev Six := m22Hexad123
private def r : Equiv.Perm Six :=
  List.formPerm [⟨3, by decide +kernel⟩, ⟨18, by decide +kernel⟩,
    ⟨10, by decide +kernel⟩, ⟨20, by decide +kernel⟩] *
    Equiv.swap ⟨1, by decide +kernel⟩ ⟨2, by decide +kernel⟩
private def s : Equiv.Perm Six :=
  Equiv.swap ⟨3, by decide +kernel⟩ ⟨10, by decide +kernel⟩ *
    Equiv.swap ⟨1, by decide +kernel⟩ ⟨2, by decide +kernel⟩

private theorem r_mem : r ∈ smallMarked := by decide +kernel
private theorem s_mem : s ∈ smallMarked := by decide +kernel

attribute [local instance] fintypePerm

private theorem small_normalizer_certificate : ∀ p : Equiv.Perm Six,
    p * r * p⁻¹ ∈ smallMarked → p * s * p⁻¹ ∈ smallMarked →
      Equiv.Perm.ofSubtype p • m22Pair12 = m22Pair12 ∧
      Equiv.Perm.ofSubtype p • hexadPartition = hexadPartition := by
  decide +kernel

private def matchings : Finset (Finset (Finset (Fin 22))) :=
  {hexadPartition, {{1,2},{3,18},{10,20}}, {{1,2},{3,20},{10,18}}}

private theorem matchings_card : matchings.card = 3 := by decide +kernel

private theorem smallPair_preserves_matchings (p : smallPair) :
    Equiv.Perm.ofSubtype p.val • matchings = matchings := by
  have h : ∀ p : smallPair, Equiv.Perm.ofSubtype p.val • matchings = matchings := by
    decide +kernel
  exact h p

private def matchingAction : smallPair →* Equiv.Perm matchings :=
  (onFinset matchings).comp
    (Equiv.Perm.ofSubtype.comp smallPair.subtype |>.codRestrict
      (stabilizer (Equiv.Perm (Fin 22)) matchings) smallPair_preserves_matchings)

private theorem matchingAction_surjective : Function.Surjective matchingAction := by
  have h : ∀ q : Equiv.Perm matchings, ∃ p : smallPair, matchingAction p = q := by
    decide +kernel
  exact h

private noncomputable def toPairImage : M22SolvableSylow.pairHexad →* smallPair :=
  ((m22SetAction m22Hexad123).comp (Subgroup.inclusion inf_le_left)).codRestrict
    smallPair (by
      intro g
      change (⟨g.val, g.property.1⟩ : stabilizer M22 m22Hexad123) ∈
        smallPair.comap (m22SetAction m22Hexad123)
      rw [pairHexad_preimage]
      exact g.property)

private theorem toPairImage_surjective : Function.Surjective toPairImage := by
  intro p
  have hp : p.val ∈ (m22SetAction m22Hexad123).range := by
    rw [restriction_range]
    exact p.property.2
  obtain ⟨g, hg⟩ := hp
  have hg' : g ∈ M22SolvableSylow.pairHexad.subgroupOf
      (stabilizer M22 m22Hexad123) := by
    rw [← pairHexad_preimage]
    change m22SetAction m22Hexad123 g ∈ smallPair
    rw [hg]
    exact p.property
  exact ⟨⟨g.val, hg'⟩, Subtype.ext hg⟩

noncomputable def pairQuotientEquiv :
    (M22SolvableSylow.pairHexad ⧸ pCore 2 M22SolvableSylow.pairHexad) ≃*
      Equiv.Perm (Fin 3) := by
  let e : matchings ≃ hexadPartition := Fintype.equivOfCardEq (by
    simp only [Fintype.card_coe, matchings_card, hexadPartition_card])
  let f := e.permCongrHom.toMonoidHom.comp (matchingAction.comp toPairImage)
  exact quotientThree f
    (e.permCongrHom.surjective.comp (matchingAction_surjective.comp toPairImage_surjective))
    6 pairHexad_card

theorem pair_sup_second : M22SolvableSylow.pairHexad ⊔ second = m22HexadStabilizer := by
  have hne : M22SolvableSylow.pairHexad.subgroupOf m22HexadStabilizer ≠
      second.subgroupOf m22HexadStabilizer := by
    intro he
    have hm := congrArg (Subgroup.map m22HexadStabilizer.subtype) he
    rw [map_subgroupOf_eq_of_le inf_le_left,
      map_subgroupOf_eq_of_le (show second ≤ m22HexadStabilizer from second_le_hexad)] at hm
    apply second_not_conjugate_pairHexad 1
    change M22SolvableSylow.pairHexad.map (MonoidHom.id _) = second
    rw [Subgroup.map_id]
    exact hm
  have h := pairHexad_isCoatom.sup_eq_top_of_ne second_isCoatom hne
  change M22SolvableSylow.pairHexad.subgroupOf m22HexadStabilizer ⊔
    second.subgroupOf m22HexadStabilizer = ⊤ at h
  have hm := congrArg (Subgroup.map m22HexadStabilizer.subtype) h
  rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le inf_le_left,
    map_subgroupOf_eq_of_le (show second ≤ m22HexadStabilizer from second_le_hexad), ← MonoidHom.range_eq_map, range_subtype] at hm

@[expose] noncomputable def fixedSylow : Sylow 2 M22 :=
  Sylow.ofCard (first ⊓ second) (by
    rw [intersection_card, m22_order]
    decide +kernel)

theorem fixedSylow_coe : (fixedSylow : Subgroup M22) = first ⊓ second := rfl

theorem fixedSylow_le_pair : (fixedSylow : Subgroup M22) ≤ M22SolvableSylow.pairHexad :=
  le_inf (inf_le_right.trans second_le_hexad) inf_le_left

theorem fixedSylow_index_pair : (fixedSylow : Subgroup M22).relIndex
    M22SolvableSylow.pairHexad = 3 := by
  have h := ((fixedSylow : Subgroup M22).subgroupOf M22SolvableSylow.pairHexad).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe fixedSylow_le_pair).toEquiv,
    show Nat.card fixedSylow = 128 from intersection_card, pairHexad_card] at h
  change 128 * (fixedSylow : Subgroup M22).relIndex _ = 384 at h
  omega

theorem fixedSylow_index_second : (fixedSylow : Subgroup M22).relIndex second = 3 := by
  have h := ((fixedSylow : Subgroup M22).subgroupOf second).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show (fixedSylow : Subgroup M22) ≤ second from
    inf_le_right)).toEquiv, show Nat.card fixedSylow = 128 from intersection_card,
    second_card] at h
  change 128 * (fixedSylow : Subgroup M22).relIndex _ = 384 at h
  omega

end Sporadic.Mathieu.M22CubicHexad
