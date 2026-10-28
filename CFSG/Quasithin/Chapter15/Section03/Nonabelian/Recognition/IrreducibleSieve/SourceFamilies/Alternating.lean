module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SmallBinaryCases
public import Theory.SpecificGroups.AlternatingSix.SylowFixedAction
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.Representation.SL2.BinaryInvolutionDisplacement
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.MarkedAutomorphism
public import Theory.Representation.AlternatingSixInvolutionDisplacement
public import Theory.Representation.AlternatingSixInvolutionDegree
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The alternating branch of the original irreducible component sieve

The solvable groups of degree at most four cannot be the nonsolvable normal
component. In degrees five and six, conjugation by the marked involution is
permutation induced; for degree six this follows from its pointwise Sylow
fixing. An odd involutory permutation in these degrees fixes a cubic element,
contrary to the original centralizer condition. Thus the marked involution
belongs to the component, using the binary Schur argument.

The SL₂(4) displacement bound excludes A₅. For A₆, three conjugate involutions
bound the irreducible degree by six, and the intrinsic small-degree theorem
then contradicts the source lower bound. The existing cubic-centralizer
argument excludes degrees seven and eight. These applications use the actual
source representation and retain no module-identification premises.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.58,
printed p.1149; the binary A₆ small-degree calculation is the elementary
permutation-module argument of §B.3.
-/

public noncomputable section

open Subgroup Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Alternating


private theorem three_dvd_odd_involution_centralizer {n : ℕ}
    (hn : n = 5 ∨ n = 6) (p : Equiv.Perm (Fin n)) (hp : p ^ 2 = 1)
    (he : p ∉ alternatingGroup (Fin n)) :
    3 ∣ Nat.card (centralizer ({p} : Set (Equiv.Perm (Fin n)))) := by
  have hc := Equiv.Perm.cycleType_of_pow_prime_eq_one hp
  have hb := p.sum_cycleType_le
  rw [hc, Multiset.sum_replicate] at hb
  simp only [Fintype.card_fin, smul_eq_mul] at hb
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, hc,
    Multiset.sum_replicate, Multiset.card_replicate] at he
  have hzero : p.cycleType.card ≠ 0 := by
    intro hz
    norm_num [hz] at he
  have htwo : p.cycleType.card ≠ 2 := by
    intro hz
    norm_num [hz] at he
  rw [Equiv.Perm.nat_card_centralizer, hc]
  rcases hn with rfl | rfl
  · have hk : p.cycleType.card = 1 := by omega
    norm_num [hk, Multiset.replicate_succ, Nat.factorial]
  · have hk : p.cycleType.card = 1 ∨ p.cycleType.card = 3 := by omega
    rcases hk with hk | hk <;> norm_num [hk, Multiset.replicate_succ, Nat.factorial]

private theorem natural_involution_inner_or_cubic {n : ℕ}
    (hn : n = 5 ∨ n = 6) (p : Equiv.Perm (Fin n)) (hp : p ^ 2 = 1) :
    p ∈ alternatingGroup (Fin n) ∨
      ∃ b : alternatingGroup (Fin n), orderOf b = 3 ∧
        MulAut.conjNormal p b = b := by
  classical
  by_cases he : p ∈ alternatingGroup (Fin n)
  · exact Or.inl he
  right
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3
    (three_dvd_odd_involution_centralizer hn p hp he)
  have hb3 : orderOf (b : Equiv.Perm (Fin n)) = 3 := (Subgroup.orderOf_coe b).trans hb
  have hbEven : (b : Equiv.Perm (Fin n)) ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have hp : Equiv.Perm.sign (b : Equiv.Perm (Fin n)) ^ 3 = 1 := by
      rw [← map_pow, ← hb3, pow_orderOf_eq_one, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (b : Equiv.Perm (Fin n))) with h | h
    · exact h
    · rw [h] at hp
      exact ((by decide : (-1 : ℤˣ) ^ 3 ≠ 1) hp).elim
  refine ⟨⟨b, hbEven⟩, (Subgroup.orderOf_mk _ _).trans hb3, ?_⟩
  apply Subtype.ext
  change p * (b : Equiv.Perm (Fin n)) * p⁻¹ = b
  have hcomm := mem_centralizer_singleton_iff.mp b.property
  rw [← hcomm, mul_inv_cancel_right]

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

private theorem marked_mem_of_permutation_action (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {n : ℕ} (hn : n = 5 ∨ n = 6)
    (e : K ≃* alternatingGroup (Fin n))
    (p : Equiv.Perm (Fin n))
    (hp : let : K.Normal := hK.normal
      MulAut.conjNormal p = MulAut.congr e (MulAut.conjNormal (H := K) v)) : v ∈ K := by
  let : K.Normal := hK.normal
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  have hv2 : v ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one v
  have hp2 : p ^ 2 = 1 := by
    apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
    rw [map_pow, hp, ← map_pow, ← map_pow, hv2, map_one, map_one, map_one]
  rcases natural_involution_inner_or_cubic hn p hp2 with he | ⟨b,hb,hfix⟩
  · apply BinaryIrreducibleCentralizer.inner_square_one_mem ρ K h.faithful
      hK.center_eq_bot hv2
    apply (MulAut.congr_inner_iff e _).mp
    exact ⟨⟨p,he⟩, hp.symm.trans (MulAut.conjNormal_val (H := alternatingGroup (Fin n)) (h := ⟨p,he⟩))⟩
  · exact (h.no_model_cubic_commuting e b hb
      ((h.marked_automorphism_data hK e).2.2 b |>.mp (hp ▸ hfix))).elim

private theorem marked_mem_five (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* alternatingGroup (Fin 5)) : v ∈ K := by
  let : K.Normal := hK.normal
  obtain ⟨p,hp⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide)).surjective (MulAut.congr e (MulAut.conjNormal (H := K) v))
  exact marked_mem_of_permutation_action h hK (Or.inl rfl) e p hp

private theorem marked_mem_six (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* alternatingGroup (Fin 6)) : v ∈ K := by
  let : K.Normal := hK.normal
  obtain ⟨ha,⟨S,hS⟩,_⟩ := h.marked_automorphism_data hK e
  obtain ⟨p,hp⟩ := AlternatingSix.ShadowLocal.involution_mem_natural_of_fixes_sylow
    S (MulAut.congr e (MulAut.conjNormal (H := K) v)) ha hS
  exact marked_mem_of_permutation_action h hK (Or.inr rfl) e p hp

/-- A normal A₅ component is impossible under the original source hypotheses.
The source marked involution is inner, so the binary SL₂ displacement bound
forces degree at most four. -/
theorem not_five_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* alternatingGroup (Fin 5)) : False := by
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  let F := GaloisField 2 2
  let q : SL(2,F) ≃* alternatingGroup (Fin 5) :=
    Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
        (by change Nat.card (GaloisField 2 2) = 4
            rw [GaloisField.card 2 2 (by decide)]; norm_num)).some
  let E : K ≃* SL(2,F) := e.trans q.symm
  let σ := (ρ.comp K.subtype).comp E.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    E.symm.toMonoidHom E.symm.surjective (ρ.comp K.subtype)).mpr hK.irreducible
  have hv := marked_mem_five h hK e
  let t : K := ⟨v,hv⟩
  have ht : orderOf t = 2 := (Subgroup.orderOf_coe t).symm.trans h.involution
  have htE : E t ≠ 1 := by
    intro he
    have ht1 : t = 1 := E.injective (he.trans E.map_one.symm)
    simp [ht1] at ht
  have hσ : Function.Injective σ :=
    (h.faithful.comp Subtype.val_injective).comp E.symm.injective
  have hbound := Representation.SL2.binary_involution_displacement σ
    ⟨E t, fun he => htE (hσ (he.trans σ.map_one.symm))⟩ (E t) htE
    (by rw [← map_pow, show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t, map_one])
  have haction : σ (E t) = ρ v := by
    change ρ (E.symm (E t) : H) = ρ v
    rw [E.symm_apply_apply]
  rw [haction] at hbound
  change Module.finrank (ZMod 2) W ≤ 2 * Module.finrank (ZMod 2) (displacement ρ v) at hbound
  rw [h.displacement_rank] at hbound
  exact h.degree_not_le_four hbound

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
/-- The solvable alternating groups cannot be the source's nonsolvable
minimal normal subgroup. -/
theorem not_small_component (hK : ComponentData ρ K) {n : ℕ} (hn : n ≤ 4)
    (e : K ≃* alternatingGroup (Fin n)) : False := by
  have hs : Group.IsSolvable (alternatingGroup (Fin n)) := by
    by_cases he : n = 4
    · subst n; exact alternatingGroup_fin_four_isSolvable
    · let := alternatingGroup.isMulCommutative_of_card_le_three
        (α := Fin n) (by simpa using (show n ≤ 3 by omega))
      exact Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
  let := hs
  exact hK.nonsolvable (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

/-- A normal A₆ component is impossible under the original source hypotheses.
The marked involution is inner. Three conjugates bound the degree by six,
where the intrinsic binary simple-degree theorem leaves only one and four. -/
theorem not_six_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* alternatingGroup (Fin 6)) : False := by
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  let σ := (ρ.comp K.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective (ρ.comp K.subtype)).mpr hK.irreducible
  have hv := marked_mem_six h hK e
  let t : K := ⟨v,hv⟩
  have ht : orderOf (e t) = 2 :=
    (e.orderOf_eq t).trans ((Subgroup.orderOf_coe t).symm.trans h.involution)
  have hσ : Function.Injective σ :=
    (h.faithful.comp Subtype.val_injective).comp e.symm.injective
  have haction : σ (e t) = ρ v := by
    change ρ (e.symm (e t) : H) = ρ v
    rw [e.symm_apply_apply]
  apply AlternatingSix.InvolutionDisplacement.not_six_le_finrank σ hσ (e t) ht
    (by rw [haction]; exact h.displacement_rank)
  exact h.six_le_degree

/-- Every alternating group of degree at most eight is excluded in the
literal irreducible source configuration. -/
theorem not_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {n : ℕ} (hn : n ≤ 8)
    (e : K ≃* alternatingGroup (Fin n)) : False := by
  by_cases hn4 : n ≤ 4
  · exact not_small_component hK hn4 e
  have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases hn with rfl | rfl | rfl | rfl
  · exact not_five_component h hK e
  · exact not_six_component h hK e
  · exact SmallBinaryCases.not_alternating_component h hK (Or.inl rfl) e
  · exact SmallBinaryCases.not_alternating_component h hK (Or.inr rfl) e

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Alternating
