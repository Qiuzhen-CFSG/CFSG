module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.SpecificGroups.PSL3Two.OuterInvolutionSinger
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.GroupTheory.PrimeRankElementary

/-!
# A direct reduction of the binary automorphism FF exclusion

The actual automorphism group of SL₃(2) has elementary two-rank at most two.
An outer involution has a commutator conjugate to the specified Singer element,
so it displaces at least three dimensions whenever that Singer element displaces
six. For inner elementary subgroups, generation by two or three conjugates gives
the corresponding bound by intersecting fixed spaces. This works on every
finite-dimensional module, with no irreducibility or splitting hypothesis.

`InnerGeneration` records only the remaining concrete subgroup geometry.
The displacement lower bound is a separate explicit input. The final inequalities
and FF exclusion here are conditional on these inputs; this module does not yet
assert the unconditional automorphism FF theorem. The matrix-to-linear transport
uses the actual `MulAut.congr (slEquivLinear 3)`.

Source: Aschbacher–Smith, C.1.32 proof, printed pp.135–136, and the binary
SL₃ specialization of B.4.2 and B.5.1, printed pp.86 and 99–103, combined
manuscript of 1 March 2004. The direct route avoids assuming `G = J(G,V)`.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.AutomorphismNoFF

abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
abbrev AutSL := MulAut SL
abbrev singer := Matrix.PSL3Two.OuterInvolutionSinger.singer
/-- The specified order-seven inner automorphism of the literal matrix group. -/
def singerActor : AutSL := MulAut.conj singer
/-- The Singer element still has order seven after the faithful inner embedding. -/
theorem singerActor_order : orderOf singerActor = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · change (MulAut.conj singer) ^ 7 = 1
    rw [← map_pow, show singer ^ 7 = 1 by decide, map_one]
  · intro he
    have hinj := MulAut.conj_injective_of_center_eq_bot
      (BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 3))
    have hh : singer = 1 := hinj (he.trans (MulAut.conj.map_one).symm)
    exact (by decide : singer ≠ 1) hh

/-- Inverse transpose inverts this symmetric Singer matrix and its inner action. -/
theorem graph_inverts_singerActor :
    BinaryLinear.OuterCyclic.graphSL 3 * singerActor *
        (BinaryLinear.OuterCyclic.graphSL 3)⁻¹ = singerActor⁻¹ := by
  have hgraph : BinaryLinear.OuterCyclic.graphSL 3 singer = singer⁻¹ := by decide
  have hconj : BinaryLinear.OuterCyclic.graphSL 3 * singerActor *
      (BinaryLinear.OuterCyclic.graphSL 3)⁻¹ =
      MulAut.conj (BinaryLinear.OuterCyclic.graphSL 3 singer) := by
    ext x : 1
    simp only [singerActor, MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply,
      map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [hconj, hgraph, map_inv, singerActor]

/-- Conjugation of a subgroup inside the full automorphism group. -/
noncomputable def conjugate (A : Subgroup AutSL) (g : AutSL) : Subgroup AutSL :=
  A.map (MulAut.conj g).toMonoidHom

/-- Concrete generation input: three conjugates suffice for a rank-one inner
subgroup, and two for an inner four-group. Only containment of the fixed Singer
actor is needed, although generation of the whole inner group suffices. -/
def InnerGeneration : Prop :=
  ∀ A : Subgroup AutSL, IsElementaryTwo A → A ≤ MulAut.innerSubgroup SL →
    (rank A = 1 ∧ ∃ b c : AutSL,
      singerActor ∈ (A ⊔ conjugate A b) ⊔ conjugate A c) ∨
    (rank A = 2 ∧ ∃ b : AutSL, singerActor ∈ A ⊔ conjugate A b)

private theorem fixedCodim_mono {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G} (h : A ≤ B) :
    fixedCodim ρ A ≤ fixedCodim ρ B := by
  have hm := Submodule.finrank_mono (ρ.invariants_comp_subtype_antitone h)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  change Module.finrank (ZMod 2) (fixedSpace ρ B) ≤
    Module.finrank (ZMod 2) (fixedSpace ρ A) at hm
  omega

private theorem fixedCodim_sup_le {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A B : Subgroup G) :
    fixedCodim ρ (A ⊔ B) ≤ fixedCodim ρ A + fixedCodim ρ B := by
  have hs : fixedSpace ρ (A ⊔ B) = fixedSpace ρ A ⊓ fixedSpace ρ B :=
    ρ.invariants_comp_sup A B
  have hd := (fixedSpace ρ A).finrank_sup_add_finrank_inf_eq (fixedSpace ρ B)
  have hm := Submodule.finrank_le (fixedSpace ρ A ⊔ fixedSpace ρ B)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  have hAB := fixedCodim_add_finrank ρ (A ⊔ B)
  rw [hs] at hAB
  omega

/-- Every elementary abelian two-subgroup of the actual automorphism group has
rank at most two, transported through the checked PSL₂(7) isomorphism. -/
theorem elementary_rank_le_two (A : Subgroup AutSL) (hA : IsElementaryAbelian 2 A) :
    rank A ≤ 2 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) ≃* SL :=
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.trans Matrix.PSL3Two.equiv.symm
  have hr : primeRank 2 AutSL ≤ 2 := by
    rw [← Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)]
    exact Theory.PSL2.primeField_automorphism_two_rank (by decide : 3 < 7)
  have hc := (primeRank_le_iff_elementary_card_le AutSL).mp hr A hA
  have hl := Nat.log_monotone (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hl

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) AutSL V)

/-- An outer involution displaces at least three dimensions if the Singer
actor displaces at least six. -/
theorem three_le_outer_fixedCodim
    (hs : 6 ≤ fixedCodim ρ (Subgroup.zpowers singerActor))
    (a : AutSL) (ha : a ^ 2 = 1) (hout : a ∉ MulAut.innerSubgroup SL) :
    3 ≤ fixedCodim ρ (Subgroup.zpowers a) := by
  obtain ⟨b, c, hbc⟩ :=
    Matrix.PSL3Two.OuterInvolutionSinger.exists_commutator_conjugate_singer a ha
      (fun g hg => hout ⟨g, hg.symm⟩)
  have hcomm : a * MulAut.conj b * a⁻¹ * (MulAut.conj b)⁻¹ =
      MulAut.conj c * singerActor * (MulAut.conj c)⁻¹ := by
    have hab : a * MulAut.conj b * a⁻¹ = MulAut.conj (a b) := by
      ext x : 1
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply,
        map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hab, ← map_inv, ← map_mul, hbc]
    simp only [map_mul, map_inv, singerActor]
  have hc := fixedCodim_commutator_le_twice ρ a (MulAut.conj b)
  rw [hcomm, fixedCodim_zpowers_conj] at hc
  omega

/-- The two concrete inputs force every nontrivial elementary actor to have
strictly larger fixed codimension than its rank, on arbitrary modules. -/
theorem rank_lt_fixedCodim_of_singer_bound (hgen : InnerGeneration)
    (hs : 6 ≤ fixedCodim ρ (Subgroup.zpowers singerActor))
    (A : Subgroup AutSL) (hA : IsElementaryTwo A) : rank A < fixedCodim ρ A := by
  have hr := elementary_rank_le_two A hA.2
  by_cases hi : A ≤ MulAut.innerSubgroup SL
  · rcases hgen A hA hi with ⟨hrank, b, c, hbc⟩ | ⟨hrank, b, hb⟩
    · have hm := fixedCodim_mono ρ (Subgroup.zpowers_le.mpr hbc)
      have hab := fixedCodim_sup_le ρ A (conjugate A b)
      have habc := fixedCodim_sup_le ρ (A ⊔ conjugate A b) (conjugate A c)
      have hb : fixedCodim ρ (conjugate A b) = fixedCodim ρ A :=
        fixedCodim_map_conj ρ A b
      have hc : fixedCodim ρ (conjugate A c) = fixedCodim ρ A :=
        fixedCodim_map_conj ρ A c
      omega
    · have hm := fixedCodim_mono ρ (Subgroup.zpowers_le.mpr hb)
      have hab := fixedCodim_sup_le ρ A (conjugate A b)
      have hb : fixedCodim ρ (conjugate A b) = fixedCodim ρ A :=
        fixedCodim_map_conj ρ A b
      omega
  · obtain ⟨a, ha, hout⟩ := Set.not_subset.mp hi
    let : IsElementaryAbelian 2 A := hA.2
    have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
    have hl := three_le_outer_fixedCodim ρ hs a ha2 hout
    have hm := fixedCodim_mono ρ (Subgroup.zpowers_le.mpr ha)
    omega

/-- Bridge from the displacement argument to the existing binary FF predicate.
The concrete generation and displacement inputs remain explicit. -/
theorem not_isFFModule_of_singer_bound (hgen : InnerGeneration)
    (hs : 6 ≤ fixedCodim ρ (Subgroup.zpowers singerActor)) : ¬ IsFFModule ρ := by
  rintro ⟨A, hA⟩
  exact Nat.not_le_of_gt (rank_lt_fixedCodim_of_singer_bound ρ hgen hs A hA.1) hA.2

/-- The equivalent strict cardinality inequality, with the same two inputs. -/
theorem card_mul_fixed_lt_of_singer_bound (hgen : InnerGeneration)
    (hs : 6 ≤ fixedCodim ρ (Subgroup.zpowers singerActor))
    (A : Subgroup AutSL) (hA : IsElementaryTwo A) :
    Nat.card A * Nat.card (fixedSpace ρ A) < Nat.card V := by
  have hl := rank_lt_fixedCodim_of_singer_bound ρ hgen hs A hA
  have hn := fixedCodim_add_finrank ρ A
  rw [hA.card_eq_two_pow_rank,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod, ← pow_add]
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega)

/-- The actual transport from matrix automorphisms to linear-group automorphisms. -/
noncomputable def linearAutEquiv : AutSL ≃*
    MulAut (BinaryLinear.OuterCyclic.LinearGroup 3) :=
  MulAut.congr (BinaryLinear.OuterCyclic.slEquivLinear 3)

/-- Conditional exclusion on the exact linear-group model used by the MS quotient. -/
theorem not_isFFModule_linear_of_singer_bound
    (σ : Representation (ZMod 2) (MulAut (BinaryLinear.OuterCyclic.LinearGroup 3)) V)
    (hgen : InnerGeneration)
    (hs : 6 ≤ fixedCodim (σ.comp linearAutEquiv.toMonoidHom)
      (Subgroup.zpowers singerActor)) : ¬ IsFFModule σ := by
  intro hff
  apply not_isFFModule_of_singer_bound (σ.comp linearAutEquiv.toMonoidHom) hgen hs
  apply hff.map_equivariant σ (σ.comp linearAutEquiv.toMonoidHom)
    linearAutEquiv.symm.toMonoidHom linearAutEquiv.symm.injective
    (LinearEquiv.refl (ZMod 2) V)
  intro g v
  simp only [LinearEquiv.refl_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]

end CFSG.Quasithin.ChapterC.BinaryMS.AutomorphismNoFF
