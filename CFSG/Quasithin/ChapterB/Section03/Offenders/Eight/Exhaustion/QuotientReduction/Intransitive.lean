module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.QuotientReduction.FixedSpace
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.QuotientReduction.CharacterBound
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Displacement bounds for intransitive actions on eight points

For an elementary abelian permutation group of rank `r`, the annihilators of
its orbit stabilizers span the dual actor space. Each contains the actual
constant-displacement character space, of dimension `t`. If the orbit sizes
are `2 ^ wᵢ` and there are `k` orbits, the dimension formula therefore gives
`r + (k - 1) * t ≤ ∑ wᵢ`, without assuming independent orbit actions.

If `t > 0`, every orbit has at least two points. Intransitivity in degree eight
then forces all orbit sizes to be two or four, so `∑ wᵢ = 4` and `k ≥ 2`.
The common-character bound gives `r + t + k ≤ 6`. This is the intransitive
estimate used in the necessity argument for the deleted and natural modules
in Aschbacher–Smith, *The Classification of Quasithin Groups*, Proposition
B.3.2(4),(6), printed pp. 83–84. The estimate is proved directly from the action
and the displacement map, independently of the offender classification.
-/

public section

open scoped BigOperators IsMulCommutative
open Module
namespace CFSG.Quasithin.ChapterB.Offenders.EightExhaustion

/-- Spanning subspaces sharing `D` contribute its dimension only once. -/
private theorem common_subspace_bound {K V I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype I]
    (D : Submodule K V) (W : I → Submodule K V)
    (hD : ∀ i, D ≤ W i) (hW : iSup W = ⊤) :
    finrank K V + Fintype.card I * finrank K D ≤
      (∑ i, finrank K (W i)) + finrank K D := by
  classical
  have hb (s : Finset I) : finrank K ↥(s.sup W) + s.card * finrank K D ≤
      (∑ i ∈ s, finrank K (W i)) + finrank K D := by
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty]
      simp
    | @insert a s ha ih =>
      rw [Finset.sup_insert, Finset.card_insert_of_notMem ha,
        Finset.sum_insert ha]
      by_cases hs : s = ∅
      · subst s
        rw [Finset.sup_empty, sup_bot_eq]
        simp
      · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        have hle : D ≤ W a ⊓ s.sup W :=
          le_inf (hD a) ((hD b).trans (Finset.le_sup hb))
        have hm := Submodule.finrank_mono hle
        have he := Submodule.finrank_sup_add_finrank_inf_eq (W a) (s.sup W)
        nlinarith
  have h := hb Finset.univ
  rw [Finset.sup_univ_eq_iSup, hW, finrank_top] at h
  simpa only [Finset.card_univ] using h

open BinaryPermutation Representation.BinaryOffender
open BinaryPermutation.QuotientFixedSpace

universe u
variable {Ω : Type u} [Fintype Ω]

private noncomputable def stabilizerSpace (A : Subgroup (Equiv.Perm Ω))
    [IsElementaryAbelian 2 A] (x : Ω) : Submodule (ZMod 2) (Additive A) :=
  AddSubgroup.toZModSubmodule 2 (MulAction.stabilizer A x).toAddSubgroup

omit [Fintype Ω] in
/-- Faithfulness and commutativity make the representative stabilizers intersect trivially. -/
private theorem stabilizerSpace_iInf (A : Subgroup (Equiv.Perm Ω))
    [IsElementaryAbelian 2 A] :
    (⨅ q : MulAction.orbitRel.Quotient A Ω, stabilizerSpace A q.out) = ⊥ := by
  apply bot_unique
  intro a ha
  change a = 0
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Equiv.ext
  intro x
  let q : MulAction.orbitRel.Quotient A Ω := Quotient.mk'' x
  have hx : x ∈ MulAction.orbit A q.out :=
    MulAction.orbitRel_apply.mp (Quotient.exact (Quotient.out_eq q).symm)
  obtain ⟨b, hb⟩ := hx
  have haf : a.toMul.val q.out = q.out :=
    (show a ∈ stabilizerSpace A q.out from
      (iInf_le (fun q : MulAction.orbitRel.Quotient A Ω => stabilizerSpace A q.out) q) ha)
  change b.val q.out = x at hb
  change a.toMul.val x = x
  rw [← hb]
  calc
    a.toMul.val (b.val q.out) = b.val (a.toMul.val q.out) :=
      congrArg (fun c : A => c.val q.out) (mul_comm a.toMul b)
    _ = b.val q.out := congrArg b.val haf

private noncomputable def displacementToDual (A : Subgroup (Equiv.Perm Ω))
    [IsElementaryAbelian 2 A] (x : Ω) :
    LinearMap.range (displacement A x) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive A) :=
  { toFun := fun v => (show Additive A →+ ZMod 2 from
      { toFun := fun a => v.val a.toMul
        map_zero' := by
          obtain ⟨w, hw⟩ := v.property
          rw [← hw]
          change w.val x - w.val x = 0
          exact sub_self _
        map_add' := by
          intro a b
          obtain ⟨w, hw⟩ := v.property
          rw [← hw]
          exact displacement_mul A x w a.toMul b.toMul }).toZModLinearMap 2
    map_add' := by intros; ext a; rfl
    map_smul' := by intros; ext a; rfl }

omit [Fintype Ω] in
private theorem displacementToDual_injective (A : Subgroup (Equiv.Perm Ω))
    [IsElementaryAbelian 2 A] (x : Ω) : Function.Injective (displacementToDual A x) := by
  intro v w h
  apply Subtype.ext
  funext a
  exact congrArg (fun c : Module.Dual (ZMod 2) (Additive A) => c (Additive.ofMul a)) h

omit [Fintype Ω] in
private theorem displacementToDual_range_le (A : Subgroup (Equiv.Perm Ω))
    [IsElementaryAbelian 2 A] (x y : Ω) :
    LinearMap.range (displacementToDual A x) ≤ (stabilizerSpace A y).dualAnnihilator := by
  rintro _ ⟨v, rfl⟩
  rw [Submodule.mem_dualAnnihilator]
  intro a ha
  obtain ⟨w, hw⟩ := v.property
  change v.val a.toMul = 0
  rw [← hw]
  exact displacement_eq_zero_of_fixes A x w a.toMul (y := y) ha

private theorem orbit_card_eq_pow_annihilator (A : Subgroup (Equiv.Perm Ω))
    [IsElementaryAbelian 2 A] (x : Ω) :
    Nat.card (MulAction.orbit A x) =
      2 ^ finrank (ZMod 2) (stabilizerSpace A x).dualAnnihilator := by
  let S := stabilizerSpace A x
  have hc (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
      Nat.card V = 2 ^ finrank (ZMod 2) V := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V))
  have he : S ≃ MulAction.stabilizer A x :=
    { toFun := fun a => ⟨a.val.toMul, a.property⟩
      invFun := fun a => ⟨Additive.ofMul a.val, a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : Nat.card (MulAction.stabilizer A x) = 2 ^ finrank (ZMod 2) S :=
    (Nat.card_congr he).symm.trans (hc S)
  have hA : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) :=
    (Nat.card_congr (Additive.toMul : Additive A ≃ A)).symm.trans (hc (Additive A))
  have ho := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A x)
  rw [Nat.card_prod, hs, hA] at ho
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  rw [← hd, pow_add, mul_comm] at ho
  exact Nat.mul_left_cancel (by positivity : 0 < 2 ^ finrank (ZMod 2) S) ho

noncomputable local instance (A : Subgroup (Equiv.Perm Ω)) :
    Fintype (MulAction.orbitRel.Quotient A Ω) := Fintype.ofFinite _

/-- Orbit logarithms bound the displacement dimension, and their sum bounds
the actor rank plus the repeated common-character constraints. -/
private theorem displacement_orbit_dimensions (A : Subgroup (Equiv.Perm Ω))
    (hA : IsElementaryTwo A) (x : Ω) :
    ∃ w : MulAction.orbitRel.Quotient A Ω → ℕ,
      (∀ q, Nat.card q.orbit = 2 ^ w q) ∧
      (∀ q, displacementRank A x ≤ w q) ∧
      rank A + Fintype.card (MulAction.orbitRel.Quotient A Ω) * displacementRank A x ≤
        (∑ q, w q) + displacementRank A x := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let W (q : MulAction.orbitRel.Quotient A Ω) := (stabilizerSpace A q.out).dualAnnihilator
  let D := LinearMap.range (displacementToDual A x)
  have hD : finrank (ZMod 2) D = displacementRank A x :=
    LinearMap.finrank_range_of_inj (displacementToDual_injective A x)
  have hle : ∀ q, D ≤ W q := fun q => displacementToDual_range_le A x q.out
  have hW : iSup W = ⊤ := by
    rw [show W = fun q : MulAction.orbitRel.Quotient A Ω =>
      (stabilizerSpace A q.out).dualAnnihilator from rfl,
      ← Subspace.dualAnnihilator_iInf_eq, stabilizerSpace_iInf, Submodule.dualAnnihilator_bot]
  have hr : finrank (ZMod 2) (Additive A) = rank A := by
    apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
    change 2 ^ finrank (ZMod 2) (Additive A) = 2 ^ rank A
    rw [← hA.card_eq_two_pow_rank]
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_congr (Additive.toMul : Additive A ≃ A)] at hc
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hc.symm
  refine ⟨fun q => finrank (ZMod 2) (W q), ?_, ?_, ?_⟩
  · intro q
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    exact orbit_card_eq_pow_annihilator A q.out
  · intro q
    rw [← hD]
    exact Submodule.finrank_mono (hle q)
  · have hb := common_subspace_bound D W hle hW
    rwa [Subspace.dual_finrank_eq, hr, hD] at hb

private theorem eight_orbit_arithmetic {Q : Type*} [Fintype Q]
    (w : Q → ℕ) (r t : ℕ) (ht : 0 < t)
    (hk : 2 ≤ Fintype.card Q) (hw : ∀ q, t ≤ w q)
    (hsum : ∑ q, 2 ^ w q = 8)
    (hbound : r + Fintype.card Q * t ≤ (∑ q, w q) + t) :
    r + t + Fintype.card Q ≤ 6 := by
  classical
  have hn : Nontrivial Q := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hsmall (q : Q) : w q = 1 ∨ w q = 2 := by
    obtain ⟨p, hp⟩ := exists_ne q
    have hpair : 2 ^ w q + 2 ^ w p ≤ 8 := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun q => 2 ^ w q) (show {q, p} ⊆ Finset.univ by simp)
        (fun _ _ _ => Nat.zero_le _)
      simpa [Finset.sum_pair hp.symm, hsum] using h
    have hp2 : 2 ≤ 2 ^ w p := by
      change 2 ^ 1 ≤ 2 ^ w p
      exact (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mpr (by have := hw p; omega)
    have hq3 : w q < 3 := by
      apply (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp
      norm_num
      omega
    have := hw q
    omega
  have hwSum : ∑ q, w q = 4 := by
    have he : (∑ q, 2 ^ w q) = 2 * ∑ q, w q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rcases hsmall q with h | h <;> simp [h]
    omega
  rw [hwSum] at hbound
  have hm := Nat.mul_le_mul_left (Fintype.card Q - 2) ht
  have hd : Fintype.card Q - 2 + 2 = Fintype.card Q := by omega
  nlinarith

/-- Positive displacement in an intransitive elementary action on eight points
forces the rank-orbit sum below the natural-offender threshold. -/
theorem rank_add_displacementRank_add_orbits_le_six_of_intransitive
    {A : Subgroup (Equiv.Perm (Fin 8))} (hA : IsElementaryTwo A)
    (ht : ¬ (∀ x y : Fin 8, ∃ a : A, a.val x = y))
    (hd : 0 < displacementRank A (0 : Fin 8)) :
    rank A + displacementRank A (0 : Fin 8) +
      Nat.card (MulAction.orbitRel.Quotient A (Fin 8)) ≤ 6 := by
  classical
  obtain ⟨w, hw, htw, hb⟩ := displacement_orbit_dimensions A hA (0 : Fin 8)
  have hk : 2 ≤ Fintype.card (MulAction.orbitRel.Quotient A (Fin 8)) := by
    by_contra h
    have hi : Subsingleton (MulAction.orbitRel.Quotient A (Fin 8)) :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    apply ht
    intro x y
    have he : (Quotient.mk'' y : MulAction.orbitRel.Quotient A (Fin 8)) =
        Quotient.mk'' x := Subsingleton.elim _ _
    exact MulAction.orbitRel_apply.mp (Quotient.exact he)
  have hsum : (∑ q : MulAction.orbitRel.Quotient A (Fin 8), 2 ^ w q) = 8 := by
    simp_rw [← hw]
    simpa only [Nat.card_sigma, Nat.card_fin] using
      (Nat.card_congr (MulAction.selfEquivSigmaOrbits' A (Fin 8))).symm
  simpa only [Nat.card_eq_fintype_card] using
    eight_orbit_arithmetic w (rank A) (displacementRank A (0 : Fin 8)) hd hk htw hsum hb

end CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
