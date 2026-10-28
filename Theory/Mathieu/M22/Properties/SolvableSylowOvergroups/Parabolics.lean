module

public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Geometry
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Maximality
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure
public import Theory.GroupTheory.SmallIndexSolvable

/-!
# Two different hexad parabolics in the natural M₂₂ action

The pair–hexad intersection and the three-pair stabilizer both contain the
pointwise hexad kernel and have order 384. Hence both are ordinary maximal
subgroups of the hexad stabilizer. They are not conjugate in M₂₂: the first
preserves a two-point set, whereas the second preserves none. The latter
assertion uses the free kernel action outside the hexad and two explicit
permutations on its six points.

The finite calculations enumerate only the six-point restriction groups
and the fifteen pairs in the hexad. No subgroup table is assumed.

These are the distinct candidates that must be retained in the subgroup step
of Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973); compare E.4.3(2).
This module does not assert that every subgroup from the source inputs is
conjugate to one of these candidates.
-/

@[expose] public section

open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22SolvableSylow
open M22ValueBound.Concrete M22ValueBound.Concrete.PartitionStructure

/-- The stabilizer of the marked pair inside its marked hexad. -/
noncomputable abbrev pairHexad : Subgroup M22 := m22HexadStabilizer ⊓ m22PairStabilizer

theorem kernel_le_pairHexad : m22HexadPointwiseKernel m22Hexad123 ≤ pairHexad := by
  refine le_inf (m22HexadPointwiseKernel_le _) ?_
  intro u hu
  apply mem_stabilizer_finset'.mpr
  intro a ha
  rw [(mem_m22HexadPointwiseKernel _ u).mp hu a
    (subset_hexad_of_mem pair_mem_hexadPartition ha)]
  exact ha

theorem kernel_le_second : m22HexadPointwiseKernel m22Hexad123 ≤ second := by
  intro u hu
  apply mem_stabilizer_finset'.mpr
  intro S hS
  have he : u • S = S := by
    apply mem_stabilizer_finset'.mpr
    intro a ha
    rw [(mem_m22HexadPointwiseKernel _ u).mp hu a (subset_hexad_of_mem hS ha)]
    exact ha
  rwa [he]

private def smallPair : Subgroup (Equiv.Perm m22Hexad123) :=
  ((stabilizer (Equiv.Perm (Fin 22)) m22Pair12).comap Equiv.Perm.ofSubtype) ⊓
    alternatingGroup m22Hexad123

private instance : DecidablePred (· ∈ smallPair) := fun g =>
  inferInstanceAs (Decidable (Equiv.Perm.ofSubtype g • m22Pair12 = m22Pair12 ∧
    Equiv.Perm.sign g = 1))

private theorem smallPair_card : Nat.card smallPair = 24 := by
  let : Fintype (Equiv.Perm m22Hexad123) := fintypePerm
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem pairHexad_preimage : smallPair.comap (m22SetAction m22Hexad123) =
    pairHexad.subgroupOf (stabilizer M22 m22Hexad123) := by
  ext g
  change (_ • m22Pair12 = m22Pair12 ∧ _ ∈ alternatingGroup _) ↔
    (g.val ∈ stabilizer M22 m22Hexad123 ∧ g.val • m22Pair12 = m22Pair12)
  rw [restriction_agrees g (subset_hexad_of_mem pair_mem_hexadPartition)]
  simp only [restriction_mem_alternating, and_true, g.property, true_and]

theorem pairHexad_card : Nat.card pairHexad = 384 := by
  have h := card_comap_of_le_range (m22SetAction m22Hexad123) smallPair
    (by rw [restriction_range]; exact inf_le_right)
  rw [pairHexad_preimage,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show pairHexad ≤ stabilizer M22 m22Hexad123 from
      inf_le_left)).toEquiv,
    m22HexadKernel_card m22Hexad123_mem, smallPair_card] at h
  exact h

theorem pairHexad_isCoatom : IsCoatom (pairHexad.subgroupOf (stabilizer M22 m22Hexad123)) :=
  isCoatom_of_card_384 m22Hexad123_mem pairHexad inf_le_left kernel_le_pairHexad pairHexad_card

theorem second_isCoatom : IsCoatom (second.subgroupOf (stabilizer M22 m22Hexad123)) :=
  isCoatom_of_card_384 m22Hexad123_mem second second_le_hexad kernel_le_second second_card

private theorem swaps_move_pair :
    ∀ S : ↥(m22Hexad123.powersetCard 2),
      Equiv.Perm.ofSubtype smallSwap₁.val • S.val ≠ S.val ∨
      Equiv.Perm.ofSubtype smallSwap₂.val • S.val ≠ S.val := by
  decide +kernel

theorem second_not_le_pair (S : Finset (Fin 22)) (hc : S.card = 2) :
    ¬ second ≤ stabilizer M22 S := by
  intro hS
  have hsub := small_invariant_subset_hexad m22Hexad123_mem S (by omega)
    (kernel_le_second.trans hS)
  have hfix (p : smallGroup) : Equiv.Perm.ofSubtype p.val • S = S := by
    obtain ⟨g, hg⟩ := toSmall_surjective p
    have he := congrArg Subtype.val hg
    change m22SetAction m22Hexad123
      (⟨g.val, second_le_hexad g.property⟩ : stabilizer M22 m22Hexad123) = p.val at he
    rw [← he, restriction_agrees _ hsub]
    exact hS g.property
  rcases swaps_move_pair ⟨S, Finset.mem_powersetCard.mpr ⟨hsub, hc⟩⟩ with h | h
  · exact h (hfix smallSwap₁)
  · exact h (hfix smallSwap₂)

theorem second_not_conjugate_pairHexad (g : M22) :
    pairHexad.map (MulAut.conj g).toMonoidHom ≠ second := by
  intro he
  apply second_not_le_pair (g • m22Pair12) (by simp [m22Pair12])
  rw [← he, stabilizer_smul_eq_stabilizer_map_conj]
  exact map_mono (show pairHexad ≤ m22PairStabilizer from inf_le_right)


/-- The two distinct parabolic types contain the same ambient Sylow subgroup. -/
theorem exists_sylow_le_pairHexad_inf_second :
    ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ pairHexad ⊓ second := by
  obtain ⟨U, hU⟩ := exists_sylow_le_first_inf_second
  exact ⟨U, le_inf (le_inf ((hU.trans inf_le_right).trans second_le_hexad)
    (hU.trans inf_le_left)) (hU.trans inf_le_right)⟩

/-- An order-384 subgroup containing an ambient Sylow two-subgroup is solvable. -/
theorem solvable_of_card_384 (X : Subgroup M22) (hc : Nat.card X = 384)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) : Group.IsSolvable X := by
  obtain ⟨U, hU⟩ := hU
  let : Group.IsNilpotent U := U.isPGroup'.isNilpotent
  have hcardU : Nat.card U = 128 := by
    rw [U.card_eq_multiplicity, m22_order]
    decide +kernel
  apply (U : Subgroup M22).isSolvable_of_relIndex_le_four X
  have he := (U : Subgroup M22).subgroupOfEquivOfLe hU
  have h := ((U : Subgroup M22).subgroupOf X).card_mul_index
  rw [Nat.card_congr he.toEquiv, hcardU, hc] at h
  change ((U : Subgroup M22).subgroupOf X).index ≤ 4
  omega

/-- The pair–hexad candidate is solvable, so it genuinely satisfies the seed
hypotheses by taking the normal seed to be the whole candidate. -/
theorem pairHexad_solvable : Group.IsSolvable pairHexad := by
  obtain ⟨U, hU⟩ := exists_sylow_le_pairHexad_inf_second
  exact solvable_of_card_384 pairHexad pairHexad_card ⟨U, hU.trans inf_le_left⟩

/-- The three-pair candidate is also solvable. -/
theorem second_solvable : Group.IsSolvable second := by
  obtain ⟨U, hU⟩ := exists_sylow_le_pairHexad_inf_second
  exact solvable_of_card_384 second second_card ⟨U, hU.trans inf_le_right⟩

end Sporadic.Mathieu.M22SolvableSylow
