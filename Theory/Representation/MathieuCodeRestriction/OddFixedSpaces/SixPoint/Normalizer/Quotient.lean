module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.Conjugacy
public import Theory.Representation.MathieuCodeRestriction.CodeLocal
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-!
# The faithful six-point quotient of the cubic normalizer

For the explicit cubic, five fixed points lie in an octad and the sixth
lies outside. The octad pointwise kernel moves that sixth point through
sixteen points while fixing the first five. Orbit–stabilizer inside the
order-48 five-point stabilizer bounds the six-point pointwise stabilizer
by three; the cubic already attains this bound. Native conjugacy transports
the equality to every order-three subgroup with six fixed points.

Thus the kernel of the actual restricted normalizer permutation is exactly
the cubic, normal inside its normalizer. The first isomorphism theorem,
using the proved surjectivity, gives the genuine quotient and its action
compatibility. This proves the group-action assertion in Aschbacher–Smith
H.15.7(2), printed pp.401–402, without asserting the separate sextet complement.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.SixPoint
noncomputable section
open scoped Pointwise

private def representativeFive : Fin 5 ↪ Fin 24 where
  toFun := ![7,8,11,12,20]
  inj' := by decide +kernel

private theorem representativeFive_fixed (i : Fin 5) :
    representativeFive i ∈ MulAction.fixedPoints cubicSubgroup (Fin 24) := by
  rw [cubicSubgroup, mem_fixedPoint_zpowers_iff]
  revert i
  decide +kernel

private theorem representativeLast_fixed :
    (22 : Fin 24) ∈ MulAction.fixedPoints cubicSubgroup (Fin 24) := by
  rw [cubicSubgroup, mem_fixedPoint_zpowers_iff]
  decide +kernel

private def representativeOctad : Octad :=
  ⟨m24GolayWord 1409, m24GolayWord_mem_blocks_of_card_eq_eight _ (by decide +kernel)⟩

private theorem representativeFive_mem_octad (i : Fin 5) :
    representativeFive i ∈ representativeOctad.val := by
  revert i
  decide +kernel

private theorem representativeLast_not_mem_octad : (22 : Fin 24) ∉ representativeOctad.val := by
  decide +kernel

/-- The literal pointwise stabilizer of the representative's six fixed points. -/
theorem cubic_fixedPointStabilizer :
    fixingSubgroup M24 (MulAction.fixedPoints cubicSubgroup (Fin 24)) = cubicSubgroup := by
  classical
  let H := fixingSubgroup M24 (Set.range representativeFive)
  let T := fixingSubgroup M24 (MulAction.fixedPoints cubicSubgroup (Fin 24))
  have hTH : T ≤ H := by
    intro g hg
    apply (mem_fixingSubgroup_iff M24).mpr
    rintro i ⟨j, rfl⟩
    exact (mem_fixingSubgroup_iff M24).mp hg _ (representativeFive_fixed j)
  have hTS : T.subgroupOf H ≤ MulAction.stabilizer H (22 : Fin 24) := by
    intro g hg
    exact (mem_fixingSubgroup_iff M24).mp hg _ representativeLast_fixed
  have horbit : 16 ≤ Nat.card (MulAction.orbit H (22 : Fin 24)) := by
    let f : {i : Fin 24 // i ∉ representativeOctad.val} →
        MulAction.orbit H (22 : Fin 24) := fun i => ⟨i.val, by
      obtain ⟨g, hg⟩ := octad_kernel_transitive representativeOctad 22 i.val
        representativeLast_not_mem_octad i.property
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨⟨g.val, (mem_fixingSubgroup_iff M24).mpr ?_⟩, hg⟩
      rintro j ⟨k, rfl⟩
      exact (mem_octadPointwiseKernel representativeOctad g.val).mp g.property _
        (representativeFive_mem_octad k)⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Subtype.ext (congrArg (fun z : MulAction.orbit H (22 : Fin 24) => z.val) hij)
    have hc : Nat.card {i : Fin 24 // i ∉ representativeOctad.val} = 16 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_fin, Fintype.card_coe, m24Blocks_card _ representativeOctad.property]
    simpa only [hc] using Nat.card_le_card_of_injective f hf
  have hH : Nat.card H = 48 := fivePointStabilizer_card representativeFive
  have hprod : Nat.card (MulAction.stabilizer H (22 : Fin 24)) *
      Nat.card (MulAction.orbit H (22 : Fin 24)) = 48 := by
    simpa only [MulAction.index_stabilizer, Nat.card_coe_set_eq, hH] using
      (MulAction.stabilizer H (22 : Fin 24)).card_mul_index
  have hS : Nat.card (MulAction.stabilizer H (22 : Fin 24)) ≤ 3 := by
    have hh := Nat.mul_le_mul_left (Nat.card (MulAction.stabilizer H (22 : Fin 24))) horbit
    rw [hprod] at hh
    omega
  have hT : Nat.card T ≤ 3 := by
    have ht := Subgroup.card_le_of_le hTS
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv] at ht
    exact ht.trans hS
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · intro d hd
    exact (mem_fixingSubgroup_iff M24).mpr fun i hi => hi ⟨d, hd⟩
  · simpa only [cubicSubgroup_card] using hT

private theorem conjugate_inverse (D : Subgroup M24) (g : M24) :
    (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = D := by
  have hh : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id M24 := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_map, hh, Subgroup.map_id]

private theorem smul_fixedPoints_conjugate (D : Subgroup M24) (g : M24)
    (i : FixedPoint D) :
    g • i.val ∈ MulAction.fixedPoints (D.map (MulAut.conj g).toMonoidHom) (Fin 24) := by
  intro d
  obtain ⟨x, hx, he⟩ := d.property
  change d.val • (g • i.val) = g • i.val
  rw [← he]
  change (g * x * g⁻¹) • (g • i.val) = _
  rw [mul_smul, mul_smul, inv_smul_smul]
  exact congrArg (g • ·) (i.property ⟨x, hx⟩)

/-- Conjugation transports the literal fixed-point set by the native permutation. -/
theorem fixedPoints_conjugate (D : Subgroup M24) (g : M24) :
    g • MulAction.fixedPoints D (Fin 24) =
      MulAction.fixedPoints (D.map (MulAut.conj g).toMonoidHom) (Fin 24) := by
  apply Set.Subset.antisymm
  · rintro i ⟨j, hj, rfl⟩
    exact smul_fixedPoints_conjugate D g ⟨j, hj⟩
  · intro i hi
    refine ⟨g⁻¹ • i, ?_, smul_inv_smul g i⟩
    have hh := smul_fixedPoints_conjugate (D.map (MulAut.conj g).toMonoidHom) g⁻¹ ⟨i, hi⟩
    rwa [conjugate_inverse] at hh

/-- Six fixed points recover the cubic as their full native pointwise stabilizer. -/
theorem fixedPointStabilizer_eq (D : Subgroup M24)
    (hD : Nat.card D = 3) (hfix : Nat.card (FixedPoint D) = 6) :
    fixingSubgroup M24 (MulAction.fixedPoints D (Fin 24)) = D := by
  obtain ⟨g, hg⟩ := cubicSubgroup_conjugacy D hD hfix
  have hh := SubMulAction.fixingSubgroup_map_conj_eq (fixedPoints_conjugate D g)
  rw [hg, cubic_fixedPointStabilizer] at hh
  exact Subgroup.map_injective (MulAut.conj g).injective (hh.trans hg.symm)

/-- The kernel is the cubic viewed inside its normalizer, with no ambient normality assertion. -/
theorem normalizerPerm_ker (D : Subgroup M24)
    (hD : Nat.card D = 3) (hfix : Nat.card (FixedPoint D) = 6) :
    (normalizerPerm D).ker = D.comap (Subgroup.normalizer (D : Set M24)).subtype := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  change (normalizerPerm D) n = 1 ↔ n.val ∈ D
  have he : (n.val ∈ fixingSubgroup M24 (MulAction.fixedPoints D (Fin 24))) = (n.val ∈ D) :=
    congrArg (fun A : Subgroup M24 => n.val ∈ A) (fixedPointStabilizer_eq D hD hfix)
  rw [← he]
  constructor
  · intro h
    apply (mem_fixingSubgroup_iff M24).mpr
    intro i hi
    exact congrArg (fun σ : Equiv.Perm (FixedPoint D) => (σ ⟨i, hi⟩).val) h
  · intro h
    apply Equiv.ext
    intro i
    exact Subtype.ext ((mem_fixingSubgroup_iff M24).mp h i.val i.property)

/-- Normality is relative to the actual normalizer. -/
instance cubic_normal_in_normalizer (D : Subgroup M24) :
    (D.comap (Subgroup.normalizer (D : Set M24)).subtype).Normal :=
  inferInstanceAs (D.subgroupOf (Subgroup.normalizer (D : Set M24))).Normal

/-- The genuine quotient isomorphism induced by restriction to the fixed points. -/
def normalizerQuotientEquiv (D : Subgroup M24)
    (hD : Nat.card D = 3) (hfix : Nat.card (FixedPoint D) = 6) :
    (Subgroup.normalizer (D : Set M24)) ⧸
        D.comap (Subgroup.normalizer (D : Set M24)).subtype ≃* Equiv.Perm (FixedPoint D) :=
  (QuotientGroup.quotientMulEquivOfEq (normalizerPerm_ker D hD hfix).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (normalizerPerm D)
      (normalizerPerm_surjective D hD hfix))

@[simp] theorem normalizerQuotientEquiv_mk (D : Subgroup M24)
    (hD : Nat.card D = 3) (hfix : Nat.card (FixedPoint D) = 6)
    (n : Subgroup.normalizer (D : Set M24)) :
    normalizerQuotientEquiv D hD hfix (QuotientGroup.mk n) = normalizerPerm D n := rfl

theorem normalizer_card (D : Subgroup M24)
    (hD : Nat.card D = 3) (hfix : Nat.card (FixedPoint D) = 6) :
    Nat.card (Subgroup.normalizer (D : Set M24)) = 2160 := by
  have hk : Nat.card (normalizerPerm D).ker = 3 := by
    rw [normalizerPerm_ker D hD hfix]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.le_normalizer).toEquiv).trans hD
  have hr : Nat.card (normalizerPerm D).range = 720 := by
    rw [MonoidHom.range_eq_top.mpr (normalizerPerm_surjective D hD hfix), Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_perm,
      ← Nat.card_eq_fintype_card (α := FixedPoint D), hfix]
    decide
  have hh := (normalizerPerm D).ker.card_mul_index
  rw [Subgroup.index_ker, hk, hr] at hh
  exact hh.symm

end
end MathieuCode.SixPoint
