module
public import Theory.SpecificGroups.SymplecticFour.ThompsonInner
/-!
# Unconditional two-rank of binary symplectic automorphisms

For a field of order `2^n` with `n ≥ 2`, identify the normal inner subgroup
of `Aut(Sp₄(F))` with `Sp₄(F)`. Its conjugation action transported through
this identification is the defining action of the automorphism group.
The source Sylow/Thompson theorem puts every maximum elementary subgroup
of an automorphism Sylow inside this inner group, whose two-rank is `3n`.
The same bound follows for the derived matrix carrier and the genuine
derived projective quotient by their proved equivalences.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
the two-rank table on printed p.356 and the Sylow calculation of 2.5.7
on printed pp.554–555.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.EvenTwoRank
open DiagramAutomorphisms.InvolutionNormalForms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private noncomputable def sourceInnerEquiv : Sp F ≃* MulAut.innerSubgroup (Sp F) :=
  MonoidHom.ofInjective inner_injective

omit [Finite F] in
private theorem sourceInnerEquiv_apply (x : Sp F) :
    (sourceInnerEquiv x : MulAut (Sp F)) = MulAut.conj x := rfl

omit [Finite F] in
private theorem source_inner_action (a : MulAut (Sp F)) :
    ThompsonInner.action (MulAut.innerSubgroup (Sp F)) sourceInnerEquiv.symm a = a := by
  let f := ThompsonInner.action (MulAut.innerSubgroup (Sp F)) sourceInnerEquiv.symm
  have hf (x : Sp F) : f (MulAut.conj x) = MulAut.conj x := by
    have hx := ThompsonInner.action_on_K (MulAut.innerSubgroup (Sp F))
      sourceInnerEquiv.symm (sourceInnerEquiv x)
    rw [MulEquiv.symm_apply_apply] at hx
    simpa only [sourceInnerEquiv_apply] using hx
  have hc (b : MulAut (Sp F)) (x : Sp F) :
      b * MulAut.conj x * b⁻¹ = MulAut.conj (b x) := by
    ext y
    simp
  apply MulEquiv.ext
  intro x
  apply inner_injective
  change MulAut.conj (f a x) = MulAut.conj (a x)
  calc
    _ = f a * MulAut.conj x * (f a)⁻¹ := (hc (f a) x).symm
    _ = f (a * MulAut.conj x * a⁻¹) := by rw [map_mul, map_mul, map_inv, hf]
    _ = f (MulAut.conj (a x)) := congrArg f (hc a x)
    _ = MulAut.conj (a x) := hf (a x)

omit [CharP F 2] in
/-- The full automorphism group has two-rank at most the inner group's rank. -/
theorem automorphism_rank_le {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    primeRank 2 (MulAut (Sp F)) ≤ 3 * n := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  obtain ⟨S, hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨A, hA⟩ := Stellmacher.elementaryAbelianMaxSubgroups_nonempty (S : Subgroup (MulAut (Sp F)))
  have hAi := ThompsonInner.maxElementary_action_inner
    (MulAut.innerSubgroup (Sp F)) sourceInnerEquiv.symm (by omega : 1 < n) hF S A hA
  have hinner : A ≤ MulAut.innerSubgroup (Sp F) := by
    intro a ha
    have hh := hAi (mem_map_of_mem _ ha)
    rwa [source_inner_action] at hh
  have hrI : primeRank 2 (MulAut.innerSubgroup (Sp F)) = 3 * n :=
    (primeRank_equiv 2 (sourceInnerEquiv (F := F))).symm.trans (rank hF (by omega))
  let : IsElementaryAbelian 2 A := hA.2.1
  let B := A.subgroupOf (MulAut.innerSubgroup (Sp F))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hinner
  have hc := (primeRank_le_iff_elementary_card_le (MulAut.innerSubgroup (Sp F))).mp
    hrI.le B inferInstance
  rw [Nat.card_congr (subgroupOfEquivOfLe hinner).toEquiv] at hc
  exact (hA.2.2 E hES hE).trans hc

omit [CharP F 2] in
/-- The bound on the actual derived matrix carrier. -/
theorem derived_automorphism_rank_le {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    primeRank 2 (MulAut (commutator (Sp F))) ≤ 3 * n := by
  rw [primeRank_equiv 2 (MulAut.congr (derivedEquiv hF hn))]
  exact automorphism_rank_le hF hn

omit [CharP F 2] in
/-- The bound on the derived subgroup of the actual projective quotient. -/
theorem projective_derived_automorphism_rank_le {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    primeRank 2 (MulAut (commutator (Sp F ⧸ center (Sp F)))) ≤ 3 * n := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let e := (projectiveDerivedEquiv hF hn).trans EvenProjective.equiv.symm
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact automorphism_rank_le hF hn

end Theory.SpecificGroups.SymplecticFour.EvenTwoRank
