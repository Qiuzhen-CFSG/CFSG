module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.Quaternion
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.NormalCentralizer.Plane

/-!
# Normality and centralizer containment for the quaternion core

Let C be the full centralizer in PSU₄(3) of the projective image of
 diag(-1,-1,1,1), and Q the image of the two coordinate quaternion groups.
We prove Q is normal in C and C_C(Q) ≤ Q.

An SU lift of an element of C either preserves or interchanges the two
coordinate planes. The quaternion group is normal in each unitary plane,
so both kinds of lifts normalize Q. For centralization, the unchanged
block forces every projective commutator scalar to be one. Commuting with
the quaternion generators then forces both blocks to be scalar. Unitarity
and determinant one make their projective image a quaternion sign pair.
The interchange case would force a nonscalar quaternion generator to be
scalar and is therefore impossible.

Normality is relative to C. The projective calculation uses its full
scalar kernel. Identification of Q with the intrinsic two-core remains
the separate parent assembly's responsibility.

Sources: the SU/PSU conventions in GLS3, chapter 2, §2.7
(`refs/KGroup/GLS3/chapter2.tex`); application: Aschbacher–Smith,
condition E and Theorem 0.1.2(4), printed pp.3–4 of `refs/quasithin.pdf`.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
open NormalCentralizer

private theorem lift_normalizes (g : (form 4).specialSubgroup)
    (hg : project 4 g ∈ standardCentralizer) (q : QuaternionGroup 2 × QuaternionGroup 2) :
    ∃ r : QuaternionGroup 2 × QuaternionGroup 2,
      g * quaternionPairSU q = quaternionPairSU r * g := by
  obtain ⟨A, B, he | he⟩ := special_block_shape g hg
  · obtain ⟨a, ha⟩ := unitary_normalizes A q.1
    obtain ⟨b, hb⟩ := unitary_normalizes B q.2
    refine ⟨(a,b), Subtype.ext (Units.ext ?_)⟩
    change g.val.val * (quaternionPairSU q).val.val =
      (quaternionPairSU (a,b)).val.val * g.val.val
    rw [quaternionPairSU_val, quaternionPairSU_val, he, block_mul, block_mul, ha, hb]
  · obtain ⟨a, ha⟩ := unitary_normalizes A q.2
    obtain ⟨b, hb⟩ := unitary_normalizes B q.1
    refine ⟨(a,b), Subtype.ext (Units.ext ?_)⟩
    change g.val.val * (quaternionPairSU q).val.val =
      (quaternionPairSU (a,b)).val.val * g.val.val
    rw [quaternionPairSU_val, quaternionPairSU_val, he, mul_assoc, swap_block,
      ← mul_assoc, block_mul, ha, hb, ← block_mul, mul_assoc]

/-- The quaternion central product is normal inside the full projective
involution centralizer, including elements interchanging the two planes. -/
public theorem quaternionCore_normal : quaternionCore.Normal := by
  constructor
  rintro x ⟨q, rfl⟩ g
  obtain ⟨s, hs⟩ := project_surjective 4 g.val
  have hg : project 4 s ∈ standardCentralizer := by rw [hs]; exact g.property
  obtain ⟨r, hr⟩ := lift_normalizes s hg q
  refine ⟨r, ?_⟩
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Subtype.ext
  change project 4 (quaternionPairSU r) * g.val = g.val * project 4 (quaternionPairSU q)
  rw [← hs, ← map_mul, ← map_mul, hr]

private theorem scalar_commutation (g h : (form 4).specialSubgroup)
    (hc : project 4 g * project 4 h = project 4 h * project 4 g) :
    ∃ u : FiniteField.Nineˣ,
      (g.val.val * h.val.val) * Matrix.scalar (Fin 4) u.val = h.val.val * g.val.val := by
  have he := congrArg Subtype.val hc
  change ProjGenLinGroup.mk g.val * ProjGenLinGroup.mk h.val =
    ProjGenLinGroup.mk h.val * ProjGenLinGroup.mk g.val at he
  rw [← map_mul, ← map_mul] at he
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  exact ⟨u, congrArg Units.val hu⟩

private theorem unitary_cancel_left (A : U₂) {B C : Mat₂} (h : A.val * B = A.val * C) : B = C := by
  have hh := congrArg (fun M : Mat₂ => star A.val * M) h
  simpa only [← mul_assoc, Matrix.mem_unitaryGroup_iff'.mp A.property, one_mul] using hh

private theorem unitary_cancel_right (A : U₂) {B C : Mat₂} (h : B * A.val = C * A.val) : B = C := by
  have hh := congrArg (fun M : Mat₂ => M * star A.val) h
  simpa only [mul_assoc, Matrix.mem_unitaryGroup_iff.mp A.property, mul_one] using hh

private theorem block_commute_left (A B : U₂) (X : Mat₂) (u : FiniteField.Nine)
    (h : (block A.val B.val * block X 1) * Matrix.scalar (Fin 4) u =
      block X 1 * block A.val B.val) : A.val * X = X * A.val := by
  rw [← block_scalar, block_mul, block_mul, block_mul] at h
  simp only [mul_one, one_mul] at h
  obtain ⟨hA, hB⟩ := block_ext h
  have hu : Matrix.scalar (Fin 2) u = 1 :=
    unitary_cancel_left B (hB.trans (mul_one B.val).symm)
  simpa only [hu, mul_one] using hA

private theorem block_commute_right (A B : U₂) (X : Mat₂) (u : FiniteField.Nine)
    (h : (block A.val B.val * block 1 X) * Matrix.scalar (Fin 4) u =
      block 1 X * block A.val B.val) : B.val * X = X * B.val := by
  rw [← block_scalar, block_mul, block_mul, block_mul] at h
  simp only [mul_one, one_mul] at h
  obtain ⟨hA, hB⟩ := block_ext h
  have hu : Matrix.scalar (Fin 2) u = 1 :=
    unitary_cancel_left A (hA.trans (mul_one A.val).symm)
  simpa only [hu, mul_one] using hB

private theorem swap_cannot_commute (A B : U₂) (u : FiniteField.Nine)
    (h : ((block A.val B.val * swap) * block quaternionI 1) * Matrix.scalar (Fin 4) u =
      block quaternionI 1 * (block A.val B.val * swap)) : False := by
  rw [← block_scalar, mul_assoc (block A.val B.val), swap_block,
    ← mul_assoc (block A.val B.val), block_mul] at h
  rw [mul_assoc, swap_block, ← mul_assoc, block_mul] at h
  rw [← mul_assoc, block_mul] at h
  have hh := congrArg (fun M : Mat₄ => M * swap) h
  simp only [mul_assoc, swap_sq, mul_one] at hh
  have hA := (block_ext hh).1
  have hc := (Matrix.scalar_commute u (fun _ => Commute.all _ _) A.val).eq
  rw [← hc] at hA
  have he := unitary_cancel_right A hA
  exact quaternionI_not_scalar u he.symm

private theorem scalar_signs : ∀ a b : FiniteField.Nine,
    star b * b = 1 → a^2 * b^2 = 1 → a = b ∨ a = -b := by decide +kernel

private theorem scalar_blocks_image (a b : FiniteField.Nine)
    (hn : star b * b = 1) (hd : a^2 * b^2 = 1) :
    ∃ (q : QuaternionGroup 2 × QuaternionGroup 2) (u : FiniteField.Nineˣ),
      block (Matrix.scalar (Fin 2) a) (Matrix.scalar (Fin 2) b) =
        block (quaternionMatrix q.1) (quaternionMatrix q.2) * Matrix.scalar (Fin 4) u.val := by
  have hbn : b ≠ 0 := by intro hz; simp [hz] at hn
  let u : FiniteField.Nineˣ := Units.mk0 b hbn
  have hqm1 : quaternionMatrix (1 : QuaternionGroup 2) = 1 := map_one quaternionMatrixHom
  have hqm2 : quaternionMatrix (QuaternionGroup.a 2 : QuaternionGroup 2) = -1 := by decide
  rcases scalar_signs a b hn hd with hab | hab
  · refine ⟨(1,1), u, ?_⟩
    change block (Matrix.scalar (Fin 2) a) (Matrix.scalar (Fin 2) b) =
      block (quaternionMatrix 1) (quaternionMatrix 1) * Matrix.scalar (Fin 4) b
    rw [hqm1, block_one, one_mul, hab, block_scalar]
  · refine ⟨(.a 2,1), u, ?_⟩
    change block (Matrix.scalar (Fin 2) a) (Matrix.scalar (Fin 2) b) =
      block (quaternionMatrix (.a 2)) (quaternionMatrix 1) * Matrix.scalar (Fin 4) b
    rw [hqm1, hqm2, ← block_scalar, block_mul, hab]
    simp [← Matrix.diagonal_neg]

private theorem project_eq_of_scalar (g h : (form 4).specialSubgroup) (u : FiniteField.Nineˣ)
    (he : g.val.val = h.val.val * Matrix.scalar (Fin 4) u.val) : project 4 g = project 4 h := by
  apply Subtype.ext
  change ProjGenLinGroup.mk g.val = ProjGenLinGroup.mk h.val
  exact (ProjGenLinGroup.mk_eq_mk_iff.mpr ⟨u, Units.ext he.symm⟩).symm

private theorem scalar_blocks_mem (g : (form 4).specialSubgroup)
    (A B : U₂) (he : g.val.val = block A.val B.val)
    (hA : A.val = Matrix.scalar (Fin 2) (A.val 0 0))
    (hB : B.val = Matrix.scalar (Fin 2) (B.val 0 0)) :
    ∃ q : QuaternionGroup 2 × QuaternionGroup 2, project 4 g = project 4 (quaternionPairSU q) := by
  have hn : star (B.val 0 0) * B.val 0 0 = 1 := by
    have hu := Matrix.mem_unitaryGroup_iff'.mp B.property
    rw [hB] at hu
    have hh := congrArg (fun M : Mat₂ => M 0 0) hu
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] using hh
  have hdu : GeneralLinearGroup.det g.val = 1 :=
    ((form 4).mem_specialSubgroup_iff g.val).mp g.property |>.2
  have hd := congrArg (fun v : FiniteField.Nineˣ => v.val) hdu
  change g.val.val.det = 1 at hd
  rw [he, hA, hB, block_det] at hd
  have hd' : (A.val 0 0)^2 * (B.val 0 0)^2 = 1 := by
    simpa [Matrix.det_fin_two, pow_two] using hd
  obtain ⟨q, u, hq⟩ := scalar_blocks_image (A.val 0 0) (B.val 0 0) hn hd'
  refine ⟨q, project_eq_of_scalar g (quaternionPairSU q) u ?_⟩
  rw [quaternionPairSU_val, he, hA, hB]
  exact hq

/-- The quaternion core contains its centralizer in the full projective
involution centralizer. The proof descends through the full scalar kernel. -/
public theorem quaternionCore_centralizer_le : Subgroup.centralizer (quaternionCore : Set standardCentralizer) ≤
    quaternionCore := by
  intro g hg
  obtain ⟨s, hs⟩ := project_surjective 4 g.val
  have hsc : project 4 s ∈ standardCentralizer := by rw [hs]; exact g.property
  have hc (q : QuaternionGroup 2 × QuaternionGroup 2) :
      ∃ u : FiniteField.Nineˣ,
        (s.val.val * block (quaternionMatrix q.1) (quaternionMatrix q.2)) *
          Matrix.scalar (Fin 4) u.val =
        block (quaternionMatrix q.1) (quaternionMatrix q.2) * s.val.val := by
    apply scalar_commutation s (quaternionPairSU q)
    rw [hs]
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hg) _
      (quaternionPair_mem q)).symm
  have hqm1 : quaternionMatrix (1 : QuaternionGroup 2) = 1 := map_one quaternionMatrixHom
  have hqmI : quaternionMatrix (QuaternionGroup.a 1 : QuaternionGroup 2) = quaternionI := by decide
  have hqmJ : quaternionMatrix (QuaternionGroup.xa 0 : QuaternionGroup 2) = quaternionJ := by decide
  obtain ⟨A, B, he | he⟩ := special_block_shape s hsc
  · have hAI : A.val * quaternionI = quaternionI * A.val := by
      obtain ⟨u, hu⟩ := hc (.a 1, 1)
      simp only [he, hqmI, hqm1] at hu
      exact block_commute_left A B quaternionI u.val hu
    have hAJ : A.val * quaternionJ = quaternionJ * A.val := by
      obtain ⟨u, hu⟩ := hc (.xa 0, 1)
      simp only [he, hqmJ, hqm1] at hu
      exact block_commute_left A B quaternionJ u.val hu
    have hBI : B.val * quaternionI = quaternionI * B.val := by
      obtain ⟨u, hu⟩ := hc (1, .a 1)
      simp only [he, hqmI, hqm1] at hu
      exact block_commute_right A B quaternionI u.val hu
    have hBJ : B.val * quaternionJ = quaternionJ * B.val := by
      obtain ⟨u, hu⟩ := hc (1, .xa 0)
      simp only [he, hqmJ, hqm1] at hu
      exact block_commute_right A B quaternionJ u.val hu
    obtain ⟨q, hq⟩ := scalar_blocks_mem s A B he
      (commuting_scalar A.val hAI hAJ) (commuting_scalar B.val hBI hBJ)
    refine ⟨q, Subtype.ext ?_⟩
    exact hq.symm.trans hs
  · obtain ⟨u, hu⟩ := hc (.a 1, 1)
    simp only [he, hqmI, hqm1] at hu
    exact (swap_cannot_commute A B u.val hu).elim

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
