module

public import Theory.SpecificGroups.BenderBorelCyclicQuotient
public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Escaping normalizers of the full unitary Borel torus

The Hermitian Weyl element acts on the quadratic-field torus by conjugate
inversion. This torus is cyclic, so the Weyl element normalizes every one
of its subgroups. Its nonzero lower-left matrix entry places it outside
the actual root–torus Borel, including after passage to projective scalars.

Source: Huppert II.10.12; Aschbacher–Smith 4.4.13(1), pp.623–624.
The full quadratic-field torus here is distinct from the fixed-field
subtorus on which the same Weyl element acts by inversion.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped Pointwise
namespace Theory.SpecificGroups.UnitaryBorel
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- The full quadratic-field torus conjugation formula. -/
theorem weyl_mul_torus (a : Eˣ) :
    hermitianWeylPSU J hJ * hermitianTorusPSU J hJ a =
      hermitianTorusPSU J hJ ((Units.map J.conj.toMonoidHom a)⁻¹) *
        hermitianWeylPSU J hJ := by
  apply Subtype.ext
  change ProjGenLinGroup.mk hermitianWeylGL * ProjGenLinGroup.mk (hermitianTorusGL J a) =
    ProjGenLinGroup.mk (hermitianTorusGL J ((Units.map J.conj.toMonoidHom a)⁻¹)) *
      ProjGenLinGroup.mk hermitianWeylGL
  rw [← map_mul, ← map_mul]
  apply congrArg ProjGenLinGroup.mk
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusGL, hermitianTorusMatrix, hermitianWeylGL,
      hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      J.conj_involutive (a : E), mul_comm]

theorem weyl_conj_torus (a : Eˣ) :
    hermitianWeylPSU J hJ * hermitianTorusPSU J hJ a * (hermitianWeylPSU J hJ)⁻¹ =
      hermitianTorusPSU J hJ ((Units.map J.conj.toMonoidHom a)⁻¹) := by
  rw [weyl_mul_torus, mul_inv_cancel_right]

variable [Finite E]

theorem fullTorus_isCyclic : IsCyclic (hermitianTorusPSU J hJ).range :=
  isCyclic_of_surjective _ (hermitianTorusPSU J hJ).rangeRestrict_surjective

theorem weyl_mem_fullTorus_normalizer :
    hermitianWeylPSU J hJ ∈ normalizer ((hermitianTorusPSU J hJ).range : Set _) := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  apply mem_normalizer_fintype
  rintro _ ⟨a,rfl⟩
  exact ⟨_, (weyl_conj_torus J hJ a).symm⟩

theorem weyl_not_mem_borel :
    hermitianWeylPSU J hJ ∉ BenderBorel.unitaryBorel J hJ := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let U := (hermitianUnipotentPSU J hJ).range
  let T := (hermitianTorusPSU J hJ).range
  have hn : T ≤ normalizer (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rintro _ ⟨a,rfl⟩
    apply mem_normalizer_fintype
    rintro _ ⟨z,rfl⟩
    refine ⟨hermitianTorusAction J a z,?_⟩
    rw [hermitianTorusPSU_mul_unipotent,mul_assoc,mul_inv_cancel,mul_one]
  intro hw
  have hh : hermitianWeylPSU J hJ ∈
      (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (T : Set _) := by
    rw [← coe_mul_of_right_le_normalizer_left U T hn]
    exact hw
  obtain ⟨u,⟨z,rfl⟩,t,⟨a,rfl⟩,he⟩ := hh
  have hp : ProjGenLinGroup.mk (hermitianUnipotentGL J z * hermitianTorusGL J a) =
      ProjGenLinGroup.mk hermitianWeylGL := by
    simpa only [map_mul,Subgroup.coe_mul,hermitianUnipotentPSU_val,
      hermitianTorusPSU_val,hermitianWeylPSU_val] using congrArg Subtype.val he
  obtain ⟨c,hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have hh := congrArg (fun A : GL (Fin 3) E => A.val 2 0) hc
  simp [GeneralLinearGroup.coe_scalar,hermitianWeylGL,hermitianWeylMatrix,
    hermitianUnipotentGL,hermitianUnipotentMatrix,hermitianTorusGL,
    hermitianTorusMatrix,Matrix.mul_apply,Fin.sum_univ_three] at hh

/-- Every subgroup of the full Borel torus has an escaping normalizer. -/
theorem normalizer_not_le_borel (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A ≤ (hermitianTorusPSU J hJ).range) :
    ¬ normalizer (A : Set _) ≤ BenderBorel.unitaryBorel J hJ := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let := fullTorus_isCyclic J hJ
  exact fun hn => weyl_not_mem_borel J hJ
    (hn (normalizer_le_normalizer_of_le_cyclic A _ hA (weyl_mem_fullTorus_normalizer J hJ)))

private theorem supplement_index_dvd {G : Type*} [Group G] [Finite G]
    (U T : Subgroup G) [U.Normal] (hgen : U ⊔ T = ⊤) : T.index ∣ Nat.card U := by
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes U T le_normalizer_of_normal
  rw [hgen, card_top, ← T.card_mul_index] at h
  have he : Nat.card U = Nat.card (U ⊓ T : Subgroup G) * T.index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := T))
    calc
      Nat.card U * Nat.card T = Nat.card (U ⊓ T : Subgroup G) *
          (Nat.card T * T.index) := h
      _ = (Nat.card (U ⊓ T : Subgroup G) * T.index) * Nat.card T := by ac_rfl
  rw [he]
  exact dvd_mul_left _ _

private theorem exists_conj_le_of_prime_not_dvd_index
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T A : Subgroup G) (hindex : ¬ p ∣ T.index) (hA : IsPGroup p A) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ T := by
  let P : Sylow p T := default
  have hP : ¬ p ∣ ((P : Subgroup T).map T.subtype).index := by
    rw [index_map_subtype]
    exact fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim P.not_dvd_index hindex
  let Q := (P.isPGroup'.map T.subtype).toSylow hP
  obtain ⟨R,hR⟩ := hA.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G R Q
  refine ⟨g, le_trans ?_ (map_subtype_le (P : Subgroup T))⟩
  change A.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G)
  rw [← hg]
  exact map_mono hR

/-- Odd-primary subgroups of the literal Borel are conjugate, within that
Borel, into its full quadratic-field torus. -/
theorem exists_borel_conj_le_fullTorus [CharP E 2] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : IsPGroup p A) (hAB : A ≤ BenderBorel.unitaryBorel J hJ) :
    ∃ g : BenderBorel.unitaryBorel J hJ,
      A.map (MulAut.conj (g : ProjectiveSpecialUnitaryMatrixGroup J)).toMonoidHom ≤
        (hermitianTorusPSU J hJ).range := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let B := BenderBorel.unitaryBorel J hJ
  let U := (hermitianUnipotentPSU J hJ).range
  let T := (hermitianTorusPSU J hJ).range
  let UB := U.subgroupOf B
  let TB := T.subgroupOf B
  let : UB.Normal := BenderBorel.hermitian_root_normal J hJ
  have hU : IsPGroup 2 UB :=
    ((BenderBorel.hermitian_root_isPGroup J).of_surjective
      (hermitianUnipotentPSU J hJ).rangeRestrict
      (hermitianUnipotentPSU J hJ).rangeRestrict_surjective).comap_subtype
  have hgen : UB ⊔ TB = ⊤ := by
    rw [← subgroupOf_sup (show U ≤ B from le_sup_left) (show T ≤ B from le_sup_right)]
    exact subgroupOf_self B
  have hcop : ¬ p ∣ TB.index := by
    obtain ⟨n,hn⟩ := hU.exists_card_eq
    have hc : Nat.Coprime p (Nat.card UB) := by
      rw [hn]
      exact hp.coprime_two_right.pow_right n
    exact fun hd => (Fact.out : p.Prime).ne_one
      (Nat.eq_one_of_dvd_coprimes hc (dvd_refl p)
        (hd.trans (supplement_index_dvd UB TB hgen)))
  obtain ⟨g,hg⟩ := exists_conj_le_of_prime_not_dvd_index TB (A.subgroupOf B)
    hcop hA.comap_subtype
  refine ⟨g, ?_⟩
  rintro _ ⟨a,ha,rfl⟩
  exact hg ⟨⟨a,hAB ha⟩,ha,rfl⟩

/-- The full unitary Borel model supplies an escaping normalizer for every
odd-primary subgroup, with no selected-subtorus containment premise. -/
theorem odd_normalizer_not_le_borel [CharP E 2] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : IsPGroup p A) (hAB : A ≤ BenderBorel.unitaryBorel J hJ) :
    ¬ normalizer (A : Set _) ≤ BenderBorel.unitaryBorel J hJ := by
  obtain ⟨g,hg⟩ := exists_borel_conj_le_fullTorus J hJ hp A hA hAB
  apply mt (fun hn => ?_) (normalizer_not_le_borel J hJ _ hg)
  rw [← map_equiv_normalizer_eq]
  rintro _ ⟨x,hx,rfl⟩
  exact (BenderBorel.unitaryBorel J hJ).mul_mem
    ((BenderBorel.unitaryBorel J hJ).mul_mem g.property (hn hx))
    ((BenderBorel.unitaryBorel J hJ).inv_mem g.property)

end Theory.SpecificGroups.UnitaryBorel
