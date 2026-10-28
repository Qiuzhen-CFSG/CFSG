module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration
import Mathlib.Tactic

/-!
# Normal generation by a nonidentity Spin root element

The checked D4 reflection table gives words taking the first simple root to
all twenty-four roots. Normality preserves membership under their pinned
conjugations. Coroot conjugation and algebraic closedness then rescale one
nonzero parameter to every parameter. Since the actual root groups generate
Spin, any normal subgroup containing a nonidentity root element is the whole
group.

This leaves root extraction from a positive-dimensional closed normal
subgroup as the geometric step in the simplicity proof. It does not assume
or prove that extraction here.
Source: GLS3, 1.10.1(b) and 1.12.1(g,h),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Pinning Pinning.PointGeneration

private def rootOrbitWord : Fin 24 → List (Fin 4) :=
  ![[0, 1, 2, 3, 1],
    [0],
    [],
    [1, 2, 3, 1],
    [0, 1, 2, 3],
    [0, 1],
    [1],
    [1, 2, 3],
    [0, 1, 3],
    [0, 1, 2],
    [1, 2],
    [1, 3],
    [0, 1, 0, 2, 3],
    [0, 1, 0],
    [1, 0],
    [1, 0, 2, 3],
    [0, 1, 0, 3],
    [0, 1, 0, 2],
    [1, 0, 2],
    [1, 0, 3],
    [0, 1, 0, 3, 1],
    [0, 1, 0, 2, 1],
    [1, 0, 2, 1],
    [1, 0, 3, 1]]

private theorem rootOrbitWord_spec (r : Fin 24) :
    (rootOrbitWord r).foldl (fun s i => reflectionIndex i s) 2 = r := by
  revert r
  decide

universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

omit [CharP k 2] in
private theorem normal_conjugate_mem_iff (N : Subgroup (Points k))
    (hN : N.Normal) (x g : Points k) : g⁻¹ * x * g ∈ N ↔ x ∈ N := by
  constructor
  · intro hx
    have h := hN.conj_mem _ hx g
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using h
  · intro hx
    simpa only [inv_inv] using hN.conj_mem x hx g⁻¹

private theorem normal_reflection_mem_iff (N : Subgroup (Points k))
    (hN : N.Normal) (r : Fin 24) (i : Fin 4) (a : k) :
    rootPoint k (rootAt (reflectionIndex i r)) a ∈ N ↔ rootPoint k (rootAt r) a ∈ N := by
  rw [← reflection_rootAt, ← simpleNormalizer_rootPoint_conjugation]
  exact normal_conjugate_mem_iff k N hN _ _

private theorem normal_reflectionWord_mem_iff (N : Subgroup (Points k))
    (hN : N.Normal) (word : List (Fin 4)) (r : Fin 24) (a : k) :
    rootPoint k (rootAt (word.foldl (fun s i => reflectionIndex i s) r)) a ∈ N ↔
      rootPoint k (rootAt r) a ∈ N := by
  induction word generalizing r with
  | nil => rfl
  | cons i word ih =>
    rw [List.foldl_cons, ih]
    exact normal_reflection_mem_iff k N hN r i a

/-- A normal subgroup contains the same parameter in every D4 root group. -/
theorem normal_rootPoint_mem_iff (N : Subgroup (Points k)) (hN : N.Normal)
    (r s : RootIndex) (a : k) : rootPoint k r a ∈ N ↔ rootPoint k s a ∈ N := by
  obtain ⟨r, rfl⟩ := rootAt_surjective r
  obtain ⟨s, rfl⟩ := rootAt_surjective s
  have h (t : Fin 24) : rootPoint k (rootAt t) a ∈ N ↔ rootPoint k (rootAt 2) a ∈ N := by
    simpa only [rootOrbitWord_spec] using
      normal_reflectionWord_mem_iff k N hN (rootOrbitWord t) 2 a
  exact (h r).trans (h s).symm

/-- A single nonidentity root element normally generates all concrete Spin points. -/
theorem normal_eq_top_of_rootPoint_mem (N : Subgroup (Points k)) (hN : N.Normal)
    (r : RootIndex) (a : k) (ha : a ≠ 0) (hx : rootPoint k r a ∈ N) : N = ⊤ := by
  have hsimple : positiveSimplePoint k 0 a ∈ N :=
    (normal_rootPoint_mem_iff k N hN r (simpleRoot 0) a).mp hx
  have hall (s : RootIndex) (b : k) : rootPoint k s b ∈ N := by
    apply (normal_rootPoint_mem_iff k N hN (simpleRoot 0) s b).mp
    by_cases hb : b = 0
    · subst b
      simpa only [rootPoint_zero] using N.one_mem
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (b / a) (n := 2) (by decide)
    have hz0 : z ≠ 0 := by
      intro he
      have hba : b / a = 0 := by simpa [he] using hz.symm
      exact (div_ne_zero hb ha) hba
    let t : kˣ := Units.mk0 z hz0
    have hconj := (normal_conjugate_mem_iff k N hN
      (positiveSimplePoint k 0 a) (simpleCoroot k 0 t)).mpr hsimple
    rw [simpleCoroot_positiveSimplePoint_conjugation] at hconj
    have hscale : (t : k) ^ typeDCartanMatrix 2 0 0 * a = b := by
      change z ^ (2 : ℤ) * a = b
      rw [zpow_ofNat, hz, div_mul_cancel₀ _ ha]
    rw [hscale] at hconj
    exact hconj
  apply top_unique
  rw [← allRootPointSubgroup_eq_top k]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨s, b⟩, rfl⟩
  exact hall s b

end Triality.SimplyConnected
