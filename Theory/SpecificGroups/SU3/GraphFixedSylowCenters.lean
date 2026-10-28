module

public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.GroupTheory.EmbeddedCenterMap
public import Mathlib.GroupTheory.Sylow

/-!
# Graph-fixed Sylow subgroups are whole unitary Sylow centers

For the antidiagonal Hermitian form over a field of order q², q = 2ⁿ,
every Sylow two-subgroup of the graph-fixed subgroup of PSU₃(q) is the
entire center of an actual Sylow two-subgroup of PSU₃(q), with both
subgroups embedded in that same projective group.

Huppert's root group has order q³ and center equal to its commutator
subgroup, of order q. In Heisenberg coordinates every commutator has
first coordinate zero; its remaining entry is fixed by field conjugation
in characteristic two. Thus the whole center is graph-fixed. The order
formulas for PSU₃(q) and the graph-fixed SL₂(q) show that the root group
and its center are Sylow in their respective groups. Conjugacy inside
the fixed subgroup supplies every other Sylow subgroup and preserves
the equality of embedded centers.

Sources: Huppert, II.10.12; Aschbacher–Smith, *The Classification of
Quasithin Groups*, proof of 16.3.4, printed p.1178 / PDF p.1195.
The graph convention is 16.1.3, printed p.1171. This calculation uses
the explicit entrywise graph automorphism; classification of arbitrary
involutory automorphisms is a separate input to ambient applications.
-/

open Matrix Subgroup
open scoped Matrix commutatorElement
open BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.GraphFixedSylowCenters
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 3 F)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private theorem root_fixed_of_fst_zero (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    hermitianUnipotentPSU J hJ z ∈ (J.projectiveGraphAut hJ).fixedSubgroup := by
  have hb : J.conj z.val.2 = z.val.2 := by
    have ht := z.property
    simp only [hz, map_zero, zero_mul, add_zero] at ht
    exact (eq_neg_of_add_eq_zero_right ht).trans (CharTwo.neg_eq _)
  have hp : hermitianUnipotentPSU J hJ z =
      J.specialToProjective (hermitianUnipotentSU J hJ z) := by
    apply Subtype.ext
    rw [hermitianUnipotentPSU_val, specialToProjective_apply_val]
    rfl
  rw [MulAut.mem_fixedSubgroup, hp, J.projectiveGraphAut_specialToProjective hJ]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [specialGraphAut_apply_val]
  change (hermitianUnipotentMatrix J z).map J.conj = hermitianUnipotentMatrix J z
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianUnipotentMatrix, hz, hb]

private theorem root_commutator_fixed (z w : hermitianUnipotentCoord J) :
    ⁅hermitianUnipotentPSU J hJ z, hermitianUnipotentPSU J hJ w⁆ ∈
      (J.projectiveGraphAut hJ).fixedSubgroup := by
  rw [← map_commutatorElement, hermitianUnipotent_commutator]
  exact root_fixed_of_fst_zero J hJ _ rfl

private theorem exists_root [Finite F] (q : ℕ) (hF : Nat.card F = q ^ 2)
    (hf : Nat.card {x : F // J.conj x = x} = q) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
        (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ∧
    ∃ R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      Nat.card R = q ^ 3 ∧ Nat.card (center R) = q ∧
      (center R).map R.subtype ≤ (J.projectiveGraphAut hJ).fixedSubgroup := by
  obtain ⟨_, _, _, _, _, _, hroots, _, horder, _⟩ := huppert_II_10_12 J q hF hf hJ
  obtain ⟨R, _, _, _, _, _, _, _, hR, hcomm, hcenter, _, _, ⟨e, he⟩, _⟩ := hroots
  refine ⟨horder, R, hR, hcomm ▸ hcenter, ?_⟩
  have hcoord (z : hermitianUnipotentCoord J) :
      (e z : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, hp⟩ := he z
    apply Subtype.ext
    rw [hermitianUnipotentPSU_val, hp]
    congr 1
    apply Units.ext
    exact hM
  rw [← hcomm, map_le_iff_le_comap, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  change ⁅(x : ProjectiveSpecialUnitaryMatrixGroup J),
    (y : ProjectiveSpecialUnitaryMatrixGroup J)⁆ ∈ (J.projectiveGraphAut hJ).fixedSubgroup
  obtain ⟨z, rfl⟩ := e.surjective x
  obtain ⟨w, rfl⟩ := e.surjective y
  rw [hcoord, hcoord]
  exact root_commutator_fixed J hJ z w

private theorem fixed_card [Finite F] {q : ℕ}
    (hf : Nat.card {x : F // J.conj x = x} = q) :
    Nat.card (J.projectiveGraphAut hJ).fixedSubgroup = q * (q ^ 2 - 1) := by
  let e := (J.projectiveGraphFixedEquivSpecial hJ).trans (J.specialGraphFixedEquivSL2 hJ)
  rw [Nat.card_congr e.toEquiv, huppert614_card_specialLinearGroup]
  have hk : Nat.card (FixedBy.subfield F J.conj) = q := hf
  rw [hk]

private theorem exists_sylow_of_card_mul_odd {G : Type*} [Group G] (R : Subgroup G)
    {k d : ℕ} (hR : Nat.card R = 2 ^ k) (hG : Nat.card G = 2 ^ k * d)
    (hd : Odd d) : ∃ S : Sylow 2 G, (S : Subgroup G) = R := by
  have hi : R.index = d := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) k)
    rw [← hR, R.card_mul_index, hG, hR]
  exact ⟨(IsPGroup.of_card hR).toSylow (hi ▸ hd.not_two_dvd_nat), rfl⟩

private theorem exists_root_sylow [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (hf : Nat.card {x : F // J.conj x = x} = 2 ^ n) :
    ∃ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      Nat.card (center S) = 2 ^ n ∧
      (center S).map (S : Subgroup _).subtype ≤ (J.projectiveGraphAut hJ).fixedSubgroup := by
  obtain ⟨horder, R, hR, hZ, hfix⟩ := exists_root J hJ (2 ^ n) hF hf
  let q := 2 ^ n
  have hq : 0 < q := pow_pos (by decide) _
  have heven : Even q := by simp [q, Nat.even_pow, show n ≠ 0 by omega]
  have ho : Odd ((q ^ 3 + 1) * (q ^ 2 - 1)) :=
    (heven.pow_of_ne_zero (by decide : 3 ≠ 0)).add_one.mul
      (Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity))
        (heven.pow_of_ne_zero (by decide : 2 ≠ 0)) odd_one)
  have hd : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * (q ^ 2 - 1) := by
    apply dvd_mul_of_dvd_right
    have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    rw [hfac]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (q + 1)) _
  have hodd : Odd (((q ^ 3 + 1) * (q ^ 2 - 1)) / Nat.gcd 3 (q + 1)) := by
    apply Nat.not_even_iff_odd.mp
    intro h
    exact ho.not_two_dvd_nat (h.two_dvd.trans (Nat.div_dvd_of_dvd hd))
  have hc : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
      2 ^ (n * 3) * (((q ^ 3 + 1) * (q ^ 2 - 1)) / Nat.gcd 3 (q + 1)) := by
    rw [horder, pow_mul, ← Nat.mul_div_assoc _ hd]
    congr 1
    ring
  obtain ⟨S, hS⟩ := exists_sylow_of_card_mul_odd R
    (by simpa [q, pow_mul] using hR) hc hodd
  exact ⟨S, hS ▸ hZ, hS ▸ hfix⟩

private theorem conjugate_centers {G : Type*} [Group G] [Finite G] (W : Subgroup G)
    (S : Sylow 2 G) (P₀ : Sylow 2 W)
    (h : (center S).map (S : Subgroup G).subtype = (P₀ : Subgroup W).map W.subtype)
    (P : Sylow 2 W) :
    ∃ T : Sylow 2 G, (center T).map (T : Subgroup G).subtype =
      (P : Subgroup W).map W.subtype := by
  obtain ⟨w, rfl⟩ := MulAction.exists_smul_eq W P₀ P
  let e := MulAut.conj (w : G)
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (center ((S : Subgroup G).map e.toMonoidHom)).map
    ((S : Subgroup G).map e.toMonoidHom).subtype = _
  rw [← Subgroup.map_embeddedCenter _ e.toMonoidHom e.injective, h]
  change ((P₀ : Subgroup W).map W.subtype).map e.toMonoidHom =
    ((P₀ : Subgroup W).map (MulAut.conj w).toMonoidHom).map W.subtype
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- Every Sylow two-subgroup of the actual graph-fixed subgroup is the whole
embedded center of a Sylow two-subgroup of the projective unitary group. -/
public theorem exists_sylow_center_eq [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (hf : Nat.card {x : F // J.conj x = x} = 2 ^ n)
    (P : Sylow 2 (J.projectiveGraphAut hJ).fixedSubgroup) :
    ∃ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      (center S).map (S : Subgroup _).subtype =
        (P : Subgroup _).map (J.projectiveGraphAut hJ).fixedSubgroup.subtype := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  obtain ⟨S, hS, hfix⟩ := exists_root_sylow J hJ hn hF hf
  let W := (J.projectiveGraphAut hJ).fixedSubgroup
  let Z : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (center S).map (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype
  let U := Z.subgroupOf W
  have hZ : Nat.card Z = 2 ^ n := by
    rw [Subgroup.card_map_of_injective Subtype.coe_injective]
    exact hS
  have hU : Nat.card U = 2 ^ n :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hfix).toEquiv).trans hZ
  have heven : Even (2 ^ n) := by simp [Nat.even_pow, show n ≠ 0 by omega]
  have ho : Odd ((2 ^ n) ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity))
      (heven.pow_of_ne_zero (by decide : 2 ≠ 0)) odd_one
  obtain ⟨P₀, hP₀⟩ := exists_sylow_of_card_mul_odd U hU (fixed_card J hJ hf) ho
  apply conjugate_centers W S P₀ _ P
  rw [hP₀]
  exact (Subgroup.map_subgroupOf_eq_of_le hfix).symm

end BenderSuzuki.MatrixGroups.HermitianForm.GraphFixedSylowCenters
