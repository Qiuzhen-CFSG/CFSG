module

public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Reduced

/-!
# Triangular Borels and Sylow two-normalizers in linear groups

In SLₙ over a finite field of characteristic two, the diagonal character
makes the upper triangular group B an extension of the unitriangular group U
by an abelian group. Cayley–Hamilton and Frobenius show that U is a two-group.
Conjugation of upper transvections, read one column at a time, proves N(U) = B.
Any two-element of B has trivial diagonal. Thus U is self-normalizing in any
two-group containing it; the nilpotent normalizer condition makes U Sylow.
Sylow conjugacy now proves solvability of every Sylow two-normalizer.

The projective construction uses the literal map SLₙ → SLₙ/Z(SLₙ).
Surjective transport of Sylow normalizers identifies the image of B as the
projective Borel, and proves its solvability without a simplicity assumption.

These are the linear Borel calculations used in Aschbacher–Smith,
`refs/quasithin.pdf`, combined manuscript of 1 March 2004, printed p.1144,
proof of 15.3.49(k). The carriers are those listed in B.4.2, p.86, and
B.5.5(1)(iv)–B.5.6, pp.104–105. No representation classification is asserted here.
-/

public section

open Matrix Subgroup
namespace Theory.SpecificGroups.LinearSylowNormalizers
variable (n : ℕ) (F : Type*) [Field F] [Finite F]
local notation "SL" => SpecialLinearGroup (Fin n) F

private def finiteSubgroup {G : Type*} [Group G] [Finite G]
    (s : Set G) (h1 : 1 ∈ s) (hm : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) : Subgroup G where
  carrier := s
  one_mem' := h1
  mul_mem' := fun ha hb => hm _ ha _ hb
  inv_mem' := by
    intro g hg
    let f : s → s := fun x => ⟨g * x, hm g hg x x.property⟩
    have hf : Function.Injective f := fun x y h => Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
    obtain ⟨x, hx⟩ := Finite.surjective_of_injective hf ⟨1,h1⟩
    have he : g * x = 1 := congrArg Subtype.val hx
    have he' : (x : G) = g⁻¹ := eq_inv_of_mul_eq_one_right he
    exact he' ▸ x.property

/-- The determinant-one upper triangular matrices. -/
def borel : Subgroup SL :=
  finiteSubgroup {g | g.val.IsUpperTriangular}
    (Matrix.blockTriangular_one) (fun _ ha _ hb => ha.mul hb)

theorem mem_borel (g : SL) : g ∈ borel n F ↔ g.val.IsUpperTriangular := Iff.rfl

private theorem triangular_mul_diag {a b : SL}
    (ha : a ∈ borel n F) (hb : b ∈ borel n F) (i : Fin n) :
    (a*b).val i i = a.val i i * b.val i i := by
  change ∑ j, a.val i j * b.val j i = _
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [ha h, zero_mul]
    · rw [hb h, mul_zero]
  · simp

private theorem diagonal_ne_zero (g : borel n F) (i : Fin n) : g.val.val i i ≠ 0 := by
  have hd := g.val.property
  rw [Matrix.det_of_isUpperTriangular g.property] at hd
  have hp : (∏ j, g.val.val j j) ≠ 0 := by rw [hd]; exact one_ne_zero
  exact (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)

private def diagonal : borel n F →* (Fin n → Fˣ) where
  toFun g i := Units.mk0 (g.val.val i i) (diagonal_ne_zero n F g i)
  map_one' := by ext i; simp
  map_mul' g h := by
    ext i
    exact triangular_mul_diag n F g.property h.property i

/-- The upper unitriangular matrices, realized as the diagonal character kernel. -/
def unipotent : Subgroup SL := (diagonal n F).ker.map (borel n F).subtype

theorem mem_unipotent (g : SL) : g ∈ unipotent n F ↔
    g ∈ borel n F ∧ ∀ i, g.val i i = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, fun i => ?_⟩
    exact congrArg (fun f : Fin n → Fˣ => (f i : F)) hx
  · rintro ⟨hg, hd⟩
    refine ⟨⟨g,hg⟩, ?_, rfl⟩
    change diagonal n F ⟨g,hg⟩ = 1
    ext i
    exact hd i

theorem unipotent_le_borel : unipotent n F ≤ borel n F := by
  intro g hg
  exact ((mem_unipotent n F g).mp hg).1

private theorem kernel_subgroupOf : (unipotent n F).subgroupOf (borel n F) = (diagonal n F).ker := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_unipotent]
  change (g.val ∈ borel n F ∧ ∀ i, g.val.val i i = 1) ↔ diagonal n F g = 1
  constructor
  · intro h
    ext i
    exact h.2 i
  · intro h
    exact ⟨g.property, fun i => congrArg (fun f : Fin n → Fˣ => (f i : F)) h⟩

theorem borel_le_normalizer_unipotent : borel n F ≤ normalizer (unipotent n F : Set SL) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (unipotent_le_borel n F)).mp
  rw [kernel_subgroupOf]
  infer_instance

private theorem upper_transvection_mem (i j : Fin n) (hij : i < j) :
    SpecialLinearGroup.transvection (ne_of_lt hij) (1 : F) ∈ unipotent n F := by
  rw [mem_unipotent]
  constructor
  · exact Matrix.blockTriangular_transvection hij.le 1
  · intro k
    simp [SpecialLinearGroup.transvection_coe, Matrix.single_apply]
    aesop

/-- Upper transvections recover the coordinate flag from its unitriangular group. -/
theorem normalizer_unipotent_le_borel : normalizer (unipotent n F : Set SL) ≤ borel n F := by
  intro g hg
  change g.val.IsUpperTriangular
  suffices h : ∀ k : ℕ, ∀ j : Fin n, j.val = k → ∀ i : Fin n, j < i → g.val i j = 0 by
    intro i j hji
    exact h j.val j rfl i hji
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro j hj i hji
    let t : SL := SpecialLinearGroup.transvection (ne_of_lt hji) 1
    let v : SL := g⁻¹ * t * g
    have hv : v ∈ unipotent n F :=
      (Subgroup.mem_normalizer_iff''.mp hg t).mp (upper_transvection_mem n F j i hji)
    obtain ⟨hvb,hvd⟩ := (mem_unipotent n F v).mp hv
    have he : t*g = g*v := by dsimp [v]; group
    have hright : (g*v).val j j = g.val j j := by
      change ∑ l, g.val j l * v.val l j = _
      rw [Finset.sum_eq_single j]
      · rw [hvd j, mul_one]
      · intro l _ hlj
        rcases lt_or_gt_of_ne hlj with h | h
        · rw [ih l.val (by omega) l rfl j h, zero_mul]
        · rw [hvb h, mul_zero]
      · simp
    have he' := congrArg (fun a : SL => a.val j j) he
    rw [hright] at he'
    have hleft : (t*g).val j j = g.val j j + g.val i j := by
      change (Matrix.transvection j i (1 : F) * g.val) j j = _
      simp [Matrix.transvection_mul_apply_same]
    rw [hleft] at he'
    exact add_eq_left.mp he'

/-- The normalizer of the concrete unitriangular subgroup is the Borel. -/
theorem normalizer_unipotent : normalizer (unipotent n F : Set SL) = borel n F :=
  le_antisymm (normalizer_unipotent_le_borel n F) (borel_le_normalizer_unipotent n F)

/-- Cayley–Hamilton and Frobenius give two-power order for every unitriangular matrix. -/
theorem unipotent_isPGroup [CharP F 2] (hn : 0 < n) : IsPGroup 2 (unipotent n F) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  intro g
  refine ⟨n, ?_⟩
  let A : Matrix (Fin n) (Fin n) F := g.val.val
  obtain ⟨hupper, hdiag⟩ := (mem_unipotent n F g.val).mp g.property
  have hc : A.charpoly = (Polynomial.X - Polynomial.C 1) ^ n := by
    rw [Matrix.charpoly_of_isUpperTriangular A hupper]
    simp_rw [show ∀ i, A i i = 1 from hdiag]
    simp
  have hz : (A - 1) ^ n = 0 := by
    have h := Matrix.aeval_self_charpoly A
    rw [hc] at h
    simpa using h
  have hz' : (A - 1) ^ (2 ^ n) = 0 :=
    pow_eq_zero_of_le (Nat.lt_two_pow_self.le) hz
  let : ExpChar (Matrix (Fin n) (Fin n) F) 2 :=
    expChar_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective F (Matrix (Fin n) (Fin n) F)) 2
  have h := add_pow_expChar_pow_of_commute 2 n (Commute.one_left (A - 1))
  have hsum : (1 : Matrix (Fin n) (Fin n) F) + (A - 1) = A := by
    rw [add_comm, sub_add_cancel]
  rw [hsum, one_pow, hz', add_zero] at h
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- The Borel is an extension of a finite two-group by a diagonal abelian group. -/
theorem borel_isSolvable [CharP F 2] (hn : 0 < n) : Group.IsSolvable (borel n F) := by
  let := (unipotent_isPGroup n F hn).isNilpotent
  let f : unipotent n F →* borel n F := Subgroup.inclusion (unipotent_le_borel n F)
  apply Group.isSolvable_of_ker_le_range f (diagonal n F)
  intro g hg
  refine ⟨⟨g, ?_⟩, rfl⟩
  exact Subgroup.mem_map_of_mem (borel n F).subtype hg

private theorem pElement_borel_mem_unipotent [CharP F 2]
    (g : SL) (hg : g ∈ borel n F) (k : ℕ) (hk : g ^ (2^k) = 1) :
    g ∈ unipotent n F := by
  rw [mem_unipotent]
  refine ⟨hg, fun i => ?_⟩
  have hb : (⟨g,hg⟩ : borel n F) ^ (2^k) = 1 := Subtype.ext hk
  have hd := congrArg (diagonal n F) hb
  rw [map_pow, map_one] at hd
  have he : (g.val i i) ^ (2^k) = 1 :=
    congrArg (fun f : Fin n → Fˣ => (f i : F)) hd
  exact (iterateFrobenius_inj F 2 k) (by simpa [iterateFrobenius_def] using he)

private theorem pGroup_le_unipotent [CharP F 2] (P : Subgroup SL)
    (hP : IsPGroup 2 P) (hUP : unipotent n F ≤ P) : P ≤ unipotent n F := by
  let := hP.isNilpotent
  have hn : normalizer ((unipotent n F).subgroupOf P : Set P) =
      (unipotent n F).subgroupOf P := by
    apply le_antisymm _ Subgroup.le_normalizer
    intro g hg
    have hgb : (g : SL) ∈ borel n F := by
      rw [← Subgroup.subgroupOf_normalizer_eq hUP, normalizer_unipotent n F] at hg
      exact hg
    obtain ⟨k,hk⟩ := hP g
    exact pElement_borel_mem_unipotent n F g hgb k (congrArg Subtype.val hk)
  have ht := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := P)) _ hn
  exact Subgroup.subgroupOf_eq_top.mp ht

/-- The unitriangular subgroup is Sylow by the normalizer condition in finite two-groups. -/
noncomputable def standardSylow [CharP F 2] (hn : 0 < n) : Sylow 2 SL :=
  { unipotent n F with
    isPGroup' := unipotent_isPGroup n F hn
    is_maximal' := by
      intro P hP hUP
      exact le_antisymm (pGroup_le_unipotent n F P hP hUP) hUP }

@[simp] theorem coe_standardSylow [CharP F 2] (hn : 0 < n) :
    (standardSylow n F hn : Subgroup SL) = unipotent n F := by rfl

theorem normalizer_standardSylow [CharP F 2] (hn : 0 < n) :
    normalizer (standardSylow n F hn : Set SL) = borel n F :=
  normalizer_unipotent n F

/-- Sylow conjugacy transports the solvable Borel to every Sylow two-normalizer in SL. -/
theorem isSolvable_sylow_normalizer [CharP F 2] (hn : 0 < n)
    (S : Sylow 2 SL) : Group.IsSolvable (normalizer (S : Set SL)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL (standardSylow n F hn) S
  have he : (unipotent n F).map (MulAut.conj g).toMonoidHom = (S : Subgroup SL) :=
    congrArg (fun T : Sylow 2 SL => (T : Subgroup SL)) hg
  have hN : (borel n F).map (MulAut.conj g).toMonoidHom = normalizer (S : Set SL) := by
    rw [← normalizer_unipotent n F, Subgroup.map_equiv_normalizer_eq, he, Sylow.coe_coe]
  let _ := borel_isSolvable n F hn
  rw [← hN]
  exact Group.isSolvable_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _)

local notation "PSL" => ProjectiveSpecialLinearGroup (Fin n) F

/-- The image of the triangular Borel in the actual central quotient SL/Z(SL). -/
def projectiveBorel : Subgroup PSL :=
  (borel n F).map (QuotientGroup.mk' (Subgroup.center SL))

/-- The image of the unitriangular Sylow under the actual projective quotient map. -/
noncomputable def projectiveSylow [CharP F 2] (hn : 0 < n) : Sylow 2 PSL :=
  (standardSylow n F hn).mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center SL))

@[simp] theorem coe_projectiveSylow [CharP F 2] (hn : 0 < n) :
    (projectiveSylow n F hn : Subgroup PSL) =
      (unipotent n F).map (QuotientGroup.mk' (Subgroup.center SL)) := by rfl

/-- Surjective Sylow-normalizer transport identifies the projective Borel. -/
theorem normalizer_projectiveSylow [CharP F 2] (hn : 0 < n) :
    normalizer (projectiveSylow n F hn : Set PSL) = projectiveBorel n F := by
  have h := (standardSylow n F hn).normalizer_map_surjective
    (QuotientGroup.mk' (Subgroup.center SL)) (QuotientGroup.mk'_surjective _)
  rw [normalizer_standardSylow] at h
  exact h.symm

/-- The projective Borel is a homomorphic image of the solvable triangular Borel. -/
theorem projectiveBorel_isSolvable [CharP F 2] (hn : 0 < n) :
    Group.IsSolvable (projectiveBorel n F) := by
  let _ := borel_isSolvable n F hn
  exact Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (Subgroup.center SL)).subgroupMap_surjective (borel n F))

/-- Every Sylow two-normalizer in the actual projective special linear group is solvable. -/
theorem isSolvable_projective_sylow_normalizer [CharP F 2] (hn : 0 < n)
    (S : Sylow 2 (ProjectiveSpecialLinearGroup (Fin n) F)) :
    Group.IsSolvable (normalizer (S : Set (ProjectiveSpecialLinearGroup (Fin n) F))) := by
  exact Sylow.isSolvable_normalizer_of_surjective
    (QuotientGroup.mk' (Subgroup.center SL)) (QuotientGroup.mk'_surjective _)
    (isSolvable_sylow_normalizer n F hn) S

end Theory.SpecificGroups.LinearSylowNormalizers
