module

public import BenderSuzuki.SE.Models
public import BenderSuzuki.ZD.ProductClosedCentralFactor.ModelGeometry
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.GroupAction.AutomorphismFixedTransport
public import BenderSuzuki.Converse.PSL2
public import BenderSuzuki.External.Huppert.II.theorem_6_13
public import BenderSuzuki.MatrixGroups.UnitarySL2Centralizer
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Algebra.CharP.CharAndCard

public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction
public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions

/-!
# Unitary automorphisms and the fixed-group obstruction

For the exact PSU₃ model in `SE.Models`, an inner automorphism whose square is
one has an elementary four-group in its fixed subgroup. Simplicity and
noncommutativity first make its conjugating element square to one. The existing
Bender-model involution geometry supplies a distinct commuting conjugate.
The identity case follows from the block SL₂ embedding over the stored
Hermitian fixed field.

PSL₂ over that field has a four-group and no normal Sylow 2-subgroup: simplicity
would force a normal Sylow subgroup to be the whole group, making the group
cyclic, contrary to its four-group. Actual fixed-subgroup equivalences therefore
give both required obstructions for outer automorphisms. The actual graph
action and its fixed-group equivalence come from `ProjectiveGraphFixed`;
`ProjectiveOuterInvolutions` conjugates every outer involution to that action.
Together these prove the obstruction for every automorphism squaring to one.

Source: GLS, Volume 4, Chapter 4, Lemma 3.4(b,c), used in Chapter 2,
Proposition 4.4 (lines 655–660 of the local TeX source). The conditional
assembly interfaces are retained, and the final theorems discharge their
outer fixed-group and arbitrary-automorphism coverage premises. Both
matrix-field and fixed-field cardinalities remain in the final interface.
-/

open scoped Matrix
open BenderSuzuki.MatrixGroups BenderSuzuki.PFchapter1section1
namespace BenderSuzuki.ZD.UnitaryAutomorphisms

private theorem exists_scalar {F : Type*} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) : ∃ y : F, y ≠ 0 ∧ y ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  have hlt : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card := by
    simp only [Finset.card_pair (zero_ne_one : (0 : F) ≠ 1), Finset.card_univ]
    rw [Nat.card_eq_fintype_card] at hF
    omega
  obtain ⟨y, _, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨y, by simpa using hy⟩

private theorem linear_twoRank {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) : TwoRankAtLeastTwo (PSL2MatrixGroup F) := by
  obtain ⟨y, hy, hy1⟩ := exists_scalar hF
  exact Converse.twoRank y hy hy1

private theorem specialLinear_twoRank {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) :
    TwoRankAtLeastTwo (Matrix.SpecialLinearGroup (Fin 2) F) := by
  let e := MulEquiv.ofBijective (Converse.pi F)
    ⟨Converse.pi_injective, Converse.pi_surjective⟩
  exact (linear_twoRank hF).map_of_injective e.symm.toMonoidHom e.symm.injective

private theorem no_normal_sylow_of_simple_twoRank
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : TwoRankAtLeastTwo G) :
    ¬ ∃ P : Sylow 2 G, (P : Subgroup G).Normal := by
  rintro ⟨P, hP⟩
  obtain ⟨V, hVcard, hVsq⟩ := hG
  have hdiv : 2 ∣ Nat.card G := by
    have h := V.card_subgroup_dvd_card
    rw [hVcard] at h
    exact dvd_trans (by decide : 2 ∣ 4) h
  have htop : (P : Subgroup G) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ hP).resolve_left
      (P.ne_bot_of_dvd_card hdiv)
  have hp : IsPGroup 2 G := by
    have h := P.isPGroup'
    rw [htop] at h
    exact h.of_equiv Subgroup.topEquiv
  let : Group.IsNilpotent G := hp.isNilpotent
  let : IsCyclic G := inferInstance
  let : Finite V := inferInstance
  obtain ⟨v, hv⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := V)
  have h := orderOf_dvd_of_pow_eq_one (hVsq v)
  rw [hv, hVcard] at h
  norm_num at h

variable {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E)

omit [Finite E] in
/-- Cardinality of the actual fixed subfield of the stored conjugation. -/
public theorem fixedField_card {n : ℕ}
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n) :
    Nat.card (FixedBy.subfield E J.conj) = 2 ^ n := hfixed

private theorem four_le_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n := by
  exact (show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn)

/-- The source field cardinality forces characteristic two. -/
public theorem matrixField_charTwo {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2) :
    CharP E 2 := by
  let := Fintype.ofFinite E
  apply charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
  simpa [Nat.card_eq_fintype_card, pow_mul] using hcard

/-- PSL₂ over the Hermitian fixed field contains an elementary four-group. -/
public theorem fixedField_psl2_twoRank {n : ℕ} (hn : 2 ≤ n)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n) :
    TwoRankAtLeastTwo (PSL2MatrixGroup (FixedBy.subfield E J.conj)) := by
  let F := FixedBy.subfield E J.conj
  let := Fintype.ofFinite F
  have hcard : Nat.card F = 2 ^ n := fixedField_card J hfixed
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa [Nat.card_eq_fintype_card] using hcard)
  exact linear_twoRank (hcard ▸ four_le_pow hn)

/-- PSL₂ over this fixed field has no normal Sylow 2-subgroup. -/
public theorem fixedField_psl2_no_normal_sylow {n : ℕ} (hn : 2 ≤ n)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n) :
    ¬ ∃ P : Sylow 2 (PSL2MatrixGroup (FixedBy.subfield E J.conj)),
      (P : Subgroup (PSL2MatrixGroup (FixedBy.subfield E J.conj))).Normal := by
  have hcard : 4 ≤ Nat.card (FixedBy.subfield E J.conj) := by
    rw [fixedField_card J hfixed]
    exact four_le_pow hn
  let := External.huppert_II_6_13 (K := FixedBy.subfield E J.conj) 2 le_rfl
    (Or.inr (by omega)) (Or.inr (by omega))
  exact no_normal_sylow_of_simple_twoRank (fixedField_psl2_twoRank J hn hfixed)

/-- The block SL₂ embedding supplies an elementary four-group in the actual PSU₃. -/
public theorem psu3_twoRank {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n) :
    TwoRankAtLeastTwo (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : CharP E 2 := matrixField_charTwo hcard
  have hF : 4 ≤ Nat.card (FixedBy.subfield E J.conj) := by
    rw [fixedField_card J hfixed]
    exact four_le_pow hn
  obtain ⟨f, hf⟩ := exists_sl2_embedding_centralizing_norm_one_torus J hJ 1 (by simp)
  have h := (specialLinear_twoRank hF).map_of_injective f hf
  exact h.map_of_injective _ (Subgroup.subtype_injective _)

/-- The identity automorphism is included in the required rank bound. -/
public theorem identity_fixedSubgroup_twoRank {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n) :
    TwoRankAtLeastTwo (1 : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)).fixedSubgroup := by
  have htop : (1 : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)).fixedSubgroup = ⊤ := by
    ext x
    simp [MulAut.mem_fixedSubgroup]
  rw [htop]
  let e : (⊤ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J := Subgroup.topEquiv
  exact (psu3_twoRank J hn hJ hcard hfixed).map_of_injective
    e.symm.toMonoidHom e.symm.injective

private theorem benderModel {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n) :
    IsSimpleBenderGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  .isPSU3 ⟨n, hn, E, inferInstance, inferInstance, J, hJ, hcard, hfixed, ⟨MulEquiv.refl _⟩⟩

private theorem sq_eq_one_of_conj_sq_eq_one
    {G : Type*} [Group G] [Finite G] (hG : IsSimpleBenderGroup G)
    (b : G) (hb : (MulAut.conj b) ^ 2 = 1) : b ^ 2 = 1 := by
  let := hG.isSimple
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact False.elim (hG.not_commutative (fun x y =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm))
  have hconj : MulAut.conj (b ^ 2) = 1 := by rwa [map_pow]
  have hmem : b ^ 2 ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun f : MulAut G => f x) hconj
    change b ^ 2 * x * (b ^ 2)⁻¹ = x at hx
    exact ((mul_inv_eq_iff_eq_mul).mp hx).symm
  rwa [hcenter, Subgroup.mem_bot] at hmem

private theorem involution_centralizer_twoRank
    {G : Type*} [Group G] [Finite G] (hG : IsSimpleBenderGroup G)
    (b : G) (hb : PFAppendixIII.IsInvolution b) :
    TwoRankAtLeastTwo (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨g, hne, hcomm⟩ := hG.exists_distinct_commuting_conjugate b hb
  let C := Subgroup.centralizer ({b} : Set G)
  let x : C := ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let y : C := ⟨MulAut.conj g b, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq.symm⟩
  have hy : PFAppendixIII.IsInvolution (MulAut.conj g b) := by
    constructor
    · intro h
      exact hb.1 ((MulAut.conj g).injective (h.trans (map_one _).symm))
    · rw [← map_pow, hb.2, map_one]
  let : IsKleinFour (Subgroup.closure ({x, y} : Set C)) :=
    Subgroup.isKleinFour_closure_pair x y
      (by apply Subtype.ext; change b * b = 1; exact (pow_two b ▸ hb.2))
      (by
        apply Subtype.ext
        change MulAut.conj g b * MulAut.conj g b = 1
        simpa only [pow_two] using hy.2)
      (fun h => hb.1 (congrArg Subtype.val h))
      (fun h => hy.1 (congrArg Subtype.val h))
      (fun h => hne (congrArg Subtype.val h).symm)
      (Subtype.ext hcomm.eq)
  refine ⟨Subgroup.closure ({x, y} : Set C), IsKleinFour.card_four, ?_⟩
  intro v
  simpa only [IsKleinFour.exponent_two] using Monoid.pow_exponent_eq_one v

/-- Every inner automorphism squaring to one has an elementary four-group in
its fixed subgroup, including the identity automorphism. -/
public theorem inner_fixedSubgroup_twoRank {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (hinner : ∃ b, a = MulAut.conj b) : TwoRankAtLeastTwo a.fixedSubgroup := by
  obtain ⟨b, rfl⟩ := hinner
  have hB := benderModel J hn hJ hcard hfixed
  by_cases hb : b = 1
  · subst b
    rw [show MulAut.conj (1 : ProjectiveSpecialUnitaryMatrixGroup J) = 1 from map_one MulAut.conj]
    exact identity_fixedSubgroup_twoRank J hn hJ hcard hfixed
  · rw [MulAut.fixedSubgroup_conj]
    exact involution_centralizer_twoRank hB b
      ⟨hb, sq_eq_one_of_conj_sq_eq_one hB b ha⟩

/-- An actual PSL₂ fixed-group isomorphism gives both obstructions required
from an outer involution. This lemma does not assert the existence of that
isomorphism. -/
public theorem fixedSubgroup_obstructions_of_equiv {n : ℕ} (hn : 2 ≤ n)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (e : a.fixedSubgroup ≃* PSL2MatrixGroup (FixedBy.subfield E J.conj)) :
    TwoRankAtLeastTwo a.fixedSubgroup ∧
      ¬ ∃ P : Sylow 2 a.fixedSubgroup, (P : Subgroup a.fixedSubgroup).Normal := by
  refine ⟨(fixedField_psl2_twoRank J hn hfixed).map_of_injective
    e.symm.toMonoidHom e.symm.injective, ?_⟩
  intro hP
  exact fixedField_psl2_no_normal_sylow J hn hfixed
    ((e.exists_normal_sylow_iff 2).mp hP)

/-- Conditional assembly from arbitrary outer-involution coverage by the
actual fixed-field PSL₂ model. The unconditional theorem below supplies it. -/
public theorem fixedSubgroup_obstructions_of_outer_classification {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (houter : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), a ^ 2 = 1 →
      (¬ ∃ b, a = MulAut.conj b) →
      Nonempty (a.fixedSubgroup ≃* PSL2MatrixGroup (FixedBy.subfield E J.conj)))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1) :
    TwoRankAtLeastTwo a.fixedSubgroup ∧
      ((∃ P : Sylow 2 a.fixedSubgroup, (P : Subgroup a.fixedSubgroup).Normal) →
        ∃ b, a = MulAut.conj b) := by
  by_cases hi : ∃ b, a = MulAut.conj b
  · exact ⟨inner_fixedSubgroup_twoRank J hn hJ hcard hfixed a ha hi, fun _ => hi⟩
  · obtain ⟨e⟩ := houter a ha hi
    obtain ⟨hrank, hnotnormal⟩ := fixedSubgroup_obstructions_of_equiv J hn hfixed a e
    exact ⟨hrank, fun hP => False.elim (hnotnormal hP)⟩

/-- Final assembly from two independent inputs: the fixed group of the
specified graph action, and conjugacy coverage of arbitrary outer involutions. -/
public theorem fixedSubgroup_obstructions_of_graph_data {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (eγ : γ.fixedSubgroup ≃* PSL2MatrixGroup (FixedBy.subfield E J.conj))
    (hcover : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), a ^ 2 = 1 →
      (¬ ∃ b, a = MulAut.conj b) →
      ∃ c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), MulAut.congr c γ = a)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1) :
    TwoRankAtLeastTwo a.fixedSubgroup ∧
      ((∃ P : Sylow 2 a.fixedSubgroup, (P : Subgroup a.fixedSubgroup).Normal) →
        ∃ b, a = MulAut.conj b) := by
  apply fixedSubgroup_obstructions_of_outer_classification J hn hJ hcard hfixed
    (a := a) (ha := ha)
  intro a ha houter
  obtain ⟨c, hc⟩ := hcover a ha houter
  subst a
  exact ⟨(MulAut.fixedSubgroupCongr c γ).symm.trans eγ⟩

/-- Every outer involution fixes an actual copy of PSL₂ over the stored
Hermitian fixed field, as in GLS IV, Chapter 4, Lemma 3.4(c). The graph action,
its fixed-group equivalence and arbitrary-automorphism coverage are proved
from the exact unitary-model parameters. -/
public theorem outer_fixedSubgroup_equiv {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ b, a = MulAut.conj b) :
    Nonempty (a.fixedSubgroup ≃* PSL2MatrixGroup (FixedBy.subfield E J.conj)) := by
  obtain ⟨γ, hγ, ⟨eγ⟩⟩ := J.exists_projectiveGraphAut_fixedEquiv hJ hn hcard hfixed
  obtain ⟨c, hc⟩ := J.outer_involution_conjugate n hn hJ hcard hfixed hγ a ha houter
  subst a
  exact ⟨(MulAut.fixedSubgroupCongr c γ).symm.trans eγ⟩

/-- The unitary fixed-subgroup obstructions used in GLS IV, Chapter 2,
Proposition 4.4: every automorphism squaring to one fixes a four-group, and
a normal Sylow 2-subgroup of its fixed group forces the automorphism to be
inner. This includes the identity automorphism. -/
public theorem fixedSubgroup_obstructions {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1) :
    TwoRankAtLeastTwo a.fixedSubgroup ∧
      ((∃ P : Sylow 2 a.fixedSubgroup, (P : Subgroup a.fixedSubgroup).Normal) →
        ∃ b, a = MulAut.conj b) := by
  exact fixedSubgroup_obstructions_of_outer_classification J hn hJ hcard hfixed
    (outer_fixedSubgroup_equiv J hn hJ hcard hfixed) a ha

/-- Every involutory automorphism of the unitary model, including identity,
has an elementary four-group in its fixed subgroup. -/
public theorem fixedSubgroup_twoRank {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1) :
    TwoRankAtLeastTwo a.fixedSubgroup :=
  (fixedSubgroup_obstructions J hn hJ hcard hfixed a ha).1

/-- A normal Sylow 2-subgroup inside the actual fixed group forces an
involutory automorphism of the unitary model to be inner. -/
public theorem inner_of_fixedSubgroup_normalSylow {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (hP : ∃ P : Sylow 2 a.fixedSubgroup, (P : Subgroup a.fixedSubgroup).Normal) :
    ∃ b, a = MulAut.conj b :=
  (fixedSubgroup_obstructions J hn hJ hcard hfixed a ha).2 hP

end BenderSuzuki.ZD.UnitaryAutomorphisms
