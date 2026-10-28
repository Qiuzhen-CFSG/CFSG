module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.Blocks
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.CubicMatrices

/-!
# Two cubic elements detecting the quaternion quotient

Put the explicit cubic matrix on each of the two coordinate planes. For
any element of the projective involution centralizer, its commutator with
either cubic has cube in the quaternion image. If both commutators belong
to that image, the element itself has cube in the image.

A block interchange cannot centralize the first cubic modulo the quaternion
image. In the preserving case the GU₂ calculations give two scalar multiples
of quaternion matrices. The determinant-one condition makes their scalars
agree, so their common scalar disappears under the actual projective map.
Normality of the quaternion image is not needed for these membership facts.

Sources: the unitary conventions of GLS3, chapter 2, §2.7, and the PSU₄(3)
application to Aschbacher–Smith, condition E and Theorem 0.1.2(4), printed
pp.3–4 of `refs/quasithin.pdf`.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore
open Blocks CubicMatrices
open scoped commutatorElement

namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.CubicDetection

theorem unitary_mul_adj (A : U 2) : A.val * A.val.conjTranspose = 1 :=
  Matrix.mem_unitaryGroup_iff.mp A.property

def cU : U 2 := ⟨cubic, (Matrix.mem_unitaryGroup_iff').mpr cubic_unitary⟩
theorem cU_cube : cU ^ 3 = 1 := Subtype.ext cubic_cube

theorem conj_cubic_cube (A : U 2) : (A.val * cubic * A.val.conjTranspose) ^ 3 = 1 := by
  have he : (MulAut.conj A cU) ^ 3 = 1 := by rw [← map_pow, cU_cube, map_one]
  exact congrArg (fun x : U 2 => x.val) he

theorem adj_cubic_cube : cubic.conjTranspose ^ 3 = 1 := by decide

def makeSU (A : Mat₄) (hu : A.conjTranspose * A = 1) (hd : A.det = 1) : SU :=
  ⟨⟨A, A.conjTranspose, mul_eq_one_comm.mp hu, hu⟩, by
    rw [HermitianForm.mem_specialSubgroup_iff]
    constructor
    · change A.conjTranspose * 1 * A = 1
      rwa [mul_one]
    · apply Units.ext
      exact hd⟩

def leftSU : SU := makeSU (block cubic 1) (by
  rw [block_adj, block_mul, cubic_unitary, Matrix.conjTranspose_one, one_mul, block_one])
  (by rw [block_det, cubic_det, Matrix.det_one, mul_one])
def rightSU : SU := makeSU (block 1 cubic) (by
  rw [block_adj, block_mul, cubic_unitary, Matrix.conjTranspose_one, one_mul, block_one])
  (by rw [block_det, cubic_det, Matrix.det_one, one_mul])

theorem left_mem : project 4 leftSU ∈ standardCentralizer :=
  (project_mem_standardCentralizer_iff _).mpr (Or.inl (block_commutes_standard _ _))
theorem right_mem : project 4 rightSU ∈ standardCentralizer :=
  (project_mem_standardCentralizer_iff _).mpr (Or.inl (block_commutes_standard _ _))

public def leftCubic : standardCentralizer := ⟨project 4 leftSU, left_mem⟩
public def rightCubic : standardCentralizer := ⟨project 4 rightSU, right_mem⟩

theorem comm_matrix (g h : SU) :
    (⁅g,h⁆).val.val = g.val.val * h.val.val * g.val.val.conjTranspose * h.val.val.conjTranspose := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Units.val_mul, su_inv]

theorem comm_block (A B X Y : Mat₂) :
    block A B * block X Y * (block A B).conjTranspose * (block X Y).conjTranspose =
      block (A * X * A.conjTranspose * X.conjTranspose)
        (B * Y * B.conjTranspose * Y.conjTranspose) := by
  rw [block_adj, block_adj, block_mul, block_mul, block_mul]

theorem comm_swap (A B X Y : Mat₂) :
    (block A B * swap) * block X Y * (block A B * swap).conjTranspose *
        (block X Y).conjTranspose =
      block (A * Y * A.conjTranspose * X.conjTranspose)
        (B * X * B.conjTranspose * Y.conjTranspose) := by
  have hs : swap * block X Y * swap = block Y X := by
    rw [swap_block, mul_assoc, swap_sq, mul_one]
  rw [Matrix.conjTranspose_mul, show swap.conjTranspose = swap by decide, block_adj, block_adj]
  calc
    _ = (block A B * (swap * block X Y * swap) * block A.conjTranspose B.conjTranspose) *
      block X.conjTranspose Y.conjTranspose := by simp only [mul_assoc]
    _ = _ := by rw [hs, block_mul, block_mul, block_mul]

theorem comm_left_diag (g : SU) (A B : U 2) (h : g.val.val = block A.val B.val) :
    (⁅g,leftSU⁆).val.val = block (ccomm A.val) 1 := by
  rw [comm_matrix]
  change g.val.val * block cubic 1 * g.val.val.conjTranspose * (block cubic 1).conjTranspose = _
  rw [h, comm_block]
  simp only [Matrix.conjTranspose_one, mul_one, unitary_mul_adj]
  rfl

theorem comm_right_diag (g : SU) (A B : U 2) (h : g.val.val = block A.val B.val) :
    (⁅g,rightSU⁆).val.val = block 1 (ccomm B.val) := by
  rw [comm_matrix]
  change g.val.val * block 1 cubic * g.val.val.conjTranspose * (block 1 cubic).conjTranspose = _
  rw [h, comm_block]
  simp only [Matrix.conjTranspose_one, mul_one, unitary_mul_adj]
  rfl

theorem comm_left_swap (g : SU) (A B : U 2) (h : g.val.val = block A.val B.val * swap) :
    (⁅g,leftSU⁆).val.val = block cubic.conjTranspose (B.val * cubic * B.val.conjTranspose) := by
  rw [comm_matrix]
  change g.val.val * block cubic 1 * g.val.val.conjTranspose * (block cubic 1).conjTranspose = _
  rw [h, comm_swap, Matrix.conjTranspose_one, mul_one, unitary_mul_adj, one_mul, mul_one]

theorem comm_right_swap (g : SU) (A B : U 2) (h : g.val.val = block A.val B.val * swap) :
    (⁅g,rightSU⁆).val.val = block (A.val * cubic * A.val.conjTranspose) cubic.conjTranspose := by
  rw [comm_matrix]
  change g.val.val * block 1 cubic * g.val.val.conjTranspose * (block 1 cubic).conjTranspose = _
  rw [h, comm_swap, Matrix.conjTranspose_one, mul_one, mul_one, unitary_mul_adj, one_mul]

theorem comm_mem (g h : SU) (hg : project 4 g ∈ standardCentralizer)
    (hh : project 4 h ∈ standardCentralizer) : project 4 ⁅g,h⁆ ∈ standardCentralizer := by
  rw [map_commutatorElement]
  exact standardCentralizer.mul_mem
    (standardCentralizer.mul_mem (standardCentralizer.mul_mem hg hh) (standardCentralizer.inv_mem hg))
    (standardCentralizer.inv_mem hh)

theorem cube_mem (g : SU) (hg : project 4 g ∈ standardCentralizer)
    (q : QuaternionGroup 2 × QuaternionGroup 2) (u : FiniteField.Nineˣ)
    (hm : g.val.val ^ 3 = u.val • block (quaternionMatrix q.1) (quaternionMatrix q.2)) :
    (⟨project 4 g, hg⟩ : standardCentralizer) ^ 3 ∈ quaternionCore := by
  have hp : project 4 (g ^ 3) ∈ standardCentralizer := by
    rw [map_pow]
    exact standardCentralizer.pow_mem hg 3
  have he : (⟨project 4 g, hg⟩ : standardCentralizer) ^ 3 = ⟨project 4 (g ^ 3), hp⟩ :=
    Subtype.ext (map_pow (project 4) g 3).symm
  rw [he, mem_core_iff]
  refine ⟨q,u,?_⟩
  change matrixHom (g ^ 3) = _
  rw [map_pow]
  exact hm

theorem core_block_one (g : SU) (hg : project 4 g ∈ standardCentralizer)
    (A : Mat₂) (hm : g.val.val = block A 1)
    (hc : (⟨project 4 g, hg⟩ : standardCentralizer) ∈ quaternionCore) : qmem A := by
  obtain ⟨q,u,he⟩ := (mem_core_iff g hg).mp hc
  rw [hm, ← block_smul] at he
  have h₁ := congrArg top he
  have h₂ := congrArg bot he
  simp only [top_block] at h₁
  simp only [bot_block] at h₂
  rw [h₁]
  exact scalar_quaternion_of_one q.1 q.2 u.val h₂

theorem core_one_block (g : SU) (hg : project 4 g ∈ standardCentralizer)
    (B : Mat₂) (hm : g.val.val = block 1 B)
    (hc : (⟨project 4 g, hg⟩ : standardCentralizer) ∈ quaternionCore) : qmem B := by
  obtain ⟨q,u,he⟩ := (mem_core_iff g hg).mp hc
  rw [hm, ← block_smul] at he
  have h₁ := congrArg top he
  have h₂ := congrArg bot he
  simp only [top_block] at h₁
  simp only [bot_block] at h₂
  rw [h₂]
  exact scalar_quaternion_of_one q.2 q.1 u.val h₁

theorem left_cube_mem (g : SU) (hg : project 4 g ∈ standardCentralizer) :
    (⟨project 4 ⁅g,leftSU⁆, comm_mem g leftSU hg left_mem⟩ : standardCentralizer) ^ 3 ∈
      quaternionCore := by
  obtain ⟨A,B,_,h | h⟩ := signed_exists g hg
  · obtain ⟨q,hq⟩ := comm_cube A
    apply cube_mem _ _ (q,1) 1
    rw [comm_left_diag g A B h, block_pow, hq, one_pow]
    simpa only [Units.val_one, one_smul] using
      (show block (quaternionMatrix q) 1 = block (quaternionMatrix q) (quaternionMatrix 1) from rfl)
  · apply cube_mem _ _ (1,1) 1
    rw [comm_left_swap g A B h, block_pow, adj_cubic_cube, conj_cubic_cube]
    simp only [Units.val_one, one_smul]
    rfl

theorem right_cube_mem (g : SU) (hg : project 4 g ∈ standardCentralizer) :
    (⟨project 4 ⁅g,rightSU⁆, comm_mem g rightSU hg right_mem⟩ : standardCentralizer) ^ 3 ∈
      quaternionCore := by
  obtain ⟨A,B,_,h | h⟩ := signed_exists g hg
  · obtain ⟨q,hq⟩ := comm_cube B
    apply cube_mem _ _ (1,q) 1
    rw [comm_right_diag g A B h, block_pow, hq, one_pow]
    simp only [Units.val_one, one_smul]
    rfl
  · apply cube_mem _ _ (1,1) 1
    rw [comm_right_swap g A B h, block_pow, adj_cubic_cube, conj_cubic_cube]
    simp only [Units.val_one, one_smul]
    rfl

theorem central_cube_mem (g : SU) (hg : project 4 g ∈ standardCentralizer)
    (hl : (⟨project 4 ⁅g,leftSU⁆, comm_mem g leftSU hg left_mem⟩ : standardCentralizer) ∈ quaternionCore)
    (hr : (⟨project 4 ⁅g,rightSU⁆, comm_mem g rightSU hg right_mem⟩ : standardCentralizer) ∈ quaternionCore) :
    (⟨project 4 g, hg⟩ : standardCentralizer) ^ 3 ∈ quaternionCore := by
  obtain ⟨A,B,hd,h | h⟩ := signed_exists g hg
  · have hA := core_block_one _ _ _ (comm_left_diag g A B h) hl
    have hB := core_one_block _ _ _ (comm_right_diag g A B h) hr
    obtain ⟨hda,q,hq⟩ := central_cube A hA
    obtain ⟨_,r,hr'⟩ := central_cube B hB
    have he : A.val.det = B.val.det :=
      (by decide +kernel : ∀ a b : FiniteField.Nine,
        (a = 1 ∨ a = -1) → a * b = 1 → a = b) _ _ hda hd
    obtain ⟨u,hu⟩ := scalar_unit A.val.det
    apply cube_mem g hg (q,r) u
    rw [h, block_pow, hq, hr', ← he, ← hu, block_smul]
  · obtain ⟨q,u,he⟩ := (mem_core_iff _ _).mp hl
    rw [comm_left_swap g A B h, ← block_smul] at he
    have ht := congrArg top he
    simp only [top_block] at ht
    exact (cubic_inv_not_scalar q.1 u.val ht).elim



theorem exists_lift (g : standardCentralizer) :
    ∃ (u : SU) (hu : project 4 u ∈ standardCentralizer),
      g = (⟨project 4 u, hu⟩ : standardCentralizer) := by
  obtain ⟨u, he⟩ := project_surjective 4 g.val
  exact ⟨u, he.symm ▸ g.property, Subtype.ext he.symm⟩

theorem lift_comm (g h : SU) (hg : project 4 g ∈ standardCentralizer)
    (hh : project 4 h ∈ standardCentralizer) :
    ⁅(⟨project 4 g, hg⟩ : standardCentralizer), (⟨project 4 h, hh⟩ : standardCentralizer)⁆ =
      ⟨project 4 ⁅g,h⁆, comm_mem g h hg hh⟩ := by
  exact Subtype.ext (map_commutatorElement (project 4) g h).symm

public theorem left_commutator_cube_mem (g : standardCentralizer) : ⁅g,leftCubic⁆ ^ 3 ∈ quaternionCore := by
  obtain ⟨u,hu,rfl⟩ := exists_lift g
  rw [show leftCubic = (⟨project 4 leftSU, left_mem⟩ : standardCentralizer) from rfl,
    lift_comm]
  exact left_cube_mem u hu

public theorem right_commutator_cube_mem (g : standardCentralizer) : ⁅g,rightCubic⁆ ^ 3 ∈ quaternionCore := by
  obtain ⟨u,hu,rfl⟩ := exists_lift g
  rw [show rightCubic = (⟨project 4 rightSU, right_mem⟩ : standardCentralizer) from rfl,
    lift_comm]
  exact right_cube_mem u hu

public theorem cube_mem_of_centralizes_cubics (g : standardCentralizer)
    (hl : ⁅g,leftCubic⁆ ∈ quaternionCore) (hr : ⁅g,rightCubic⁆ ∈ quaternionCore) :
    g ^ 3 ∈ quaternionCore := by
  obtain ⟨u,hu,rfl⟩ := exists_lift g
  rw [show leftCubic = (⟨project 4 leftSU, left_mem⟩ : standardCentralizer) from rfl,
    lift_comm] at hl
  rw [show rightCubic = (⟨project 4 rightSU, right_mem⟩ : standardCentralizer) from rfl,
    lift_comm] at hr
  exact central_cube_mem u hu hl hr

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.CubicDetection
