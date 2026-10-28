module
public import Theory.SpecificGroups.Symplectic.A02ParabolicSections
public import Theory.SpecificGroups.Symplectic.CentralCovers.HigherNonbinary.MatrixSystem
public import Theory.SpecificGroups.PSp4Three.Simplicity

/-!
# The symplectic parabolic containing the actual six-space numerator

The explicit long-root subgroup consists of transvections in the first
isotropic direction. In characteristic two the symplectic center is trivial.
A nonidentity transvection recovers its direction from its moved vectors, so
the root normalizer is exactly the projective stabilizer of that direction.
This stabilizer is proper. The iterated complementary-plane embedding fixes
the direction pointwise, placing its genuine Sp₆ numerator in this parabolic.

The resulting properness and placement discharge the two remaining geometric
premises in the symplectic branch of A.2.18. All groups and quotient maps are
the existing matrix carriers, with no classification hypothesis.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004, A.2.18,
printed p.40; the geometric description of parabolics in GLS3 §2.6.
-/

@[expose] public noncomputable section
open Matrix Matrix.PSp4Three Subgroup
open scoped Pointwise LinearAlgebra.Projectivization
namespace Theory.SpecificGroups.Symplectic
open FundamentalPlane
variable {F : Type*} [Field F] [CharP F 2] {r : ℕ}

private theorem root_eq_transvection (i : Fin r) (t : F) :
    SymplecticRoot.root i t = transvection (Matrix.PSp4Three.e i) t := by
  apply ext_action
  intro x
  rw [transvection_apply,form_e_right,CharTwo.neg_eq]
  change (fromBlocks 1 (diagonal (Pi.single i t)) 0 1) *ᵥ x = _
  rw [fromBlocks_mulVec]
  funext j
  cases j with
  | inl j =>
    by_cases hj : j=i
    · subst j
      simp [Matrix.PSp4Three.e,Pi.smul_apply,smul_eq_mul,mulVec_diagonal]
    · simp [Matrix.PSp4Three.e,Pi.smul_apply,smul_eq_mul,mulVec_diagonal,hj]
  | inr j => simp [Matrix.PSp4Three.e,Pi.smul_apply,smul_eq_mul]

private theorem rootSubgroup_eq_direction (i : Fin r) :
    SymplecticRoot.rootSubgroup (F := F) i = directionGroup (Matrix.PSp4Three.e i) := by
  ext g
  constructor
  · rintro ⟨t,rfl⟩
    refine ⟨t,?_⟩
    change projection (transvection (Matrix.PSp4Three.e i) t.toAdd) = projection (SymplecticRoot.root i t.toAdd)
    rw [root_eq_transvection]
  · rintro ⟨t,rfl⟩
    refine ⟨t,?_⟩
    change projection (SymplecticRoot.root i t.toAdd) = projection (transvection (Matrix.PSp4Three.e i) t.toAdd)
    rw [root_eq_transvection]

/-- The literal long-root normalizer is the stabilizer of its isotropic direction. -/
theorem rootNormalizer_eq_lineStabilizer (i : Fin r) :
    normalizer (SymplecticRoot.rootSubgroup (F := F) i : Set (PSp r F)) =
      MulAction.stabilizer (PSp r F) (ePoint (F := F) i) := by
  ext q
  obtain ⟨g,rfl⟩ := projection_surjective q
  have hproj : Function.Injective (projection (n := r) (F := F)) :=
    (CentralCovers.HigherNonbinary.projectiveEquiv (F := F)
      (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)).injective
  constructor
  · intro hg
    have hroot : projection (transvection (Matrix.PSp4Three.e i) (1 : F)) ∈ SymplecticRoot.rootSubgroup i := by
      rw [rootSubgroup_eq_direction]
      exact ⟨Multiplicative.ofAdd 1,rfl⟩
    have hc := (mem_normalizer_iff.mp hg (projection (transvection (Matrix.PSp4Three.e i) (1 : F)))).mp hroot
    rw [rootSubgroup_eq_direction] at hc
    obtain ⟨t,ht⟩ := hc
    have he : transvection (g • Matrix.PSp4Three.e i) 1 = transvection (Matrix.PSp4Three.e i) t.toAdd := by
      apply hproj
      rw [←transvection_conjugate,map_mul,map_mul,map_inv]
      exact ht.symm
    have hge : g • Matrix.PSp4Three.e (F := F) i ≠ 0 :=
      (map_ne_zero_iff (toLinear g) (toLinear g).injective).mpr (e_nonzero i)
    obtain ⟨x,hx⟩ := exists_form_left hge (1 : F)
    have heq := congrArg (fun a : Sp r F => a • x) he
    simp only [transvection_apply,hx,mul_one,one_smul] at heq
    have hdir : g • Matrix.PSp4Three.e i = (t.toAdd * form x (Matrix.PSp4Three.e i)) • Matrix.PSp4Three.e i := add_left_cancel heq
    apply MulAction.mem_stabilizer_iff.mpr
    rw [projection_smul,ePoint,Projectivization.smul_mk,Projectivization.mk_eq_mk_iff']
    exact ⟨_,hdir.symm⟩
  · intro hg
    have hfix : projection g • ePoint (F := F) i = ePoint (F := F) i := MulAction.mem_stabilizer_iff.mp hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [rootSubgroup_eq_direction,←lineTransvections_mk (e_nonzero i)]
    change (MulAut.conj (projection g)) • lineTransvections (ePoint (F := F) i) = lineTransvections (ePoint (F := F) i)
    rw [←lineTransvections_conj,hfix]

/-- An isotropic-line stabilizer is a proper subgroup of the literal central quotient. -/
theorem rootNormalizer_ne_top (i : Fin r) :
    normalizer (SymplecticRoot.rootSubgroup (F := F) i : Set (PSp r F)) ≠ ⊤ := by
  have hne : ePoint (F := F) i ≠ fPoint i := by
    intro h
    rw [ePoint,fPoint,Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨a,ha⟩ := h
    have hh := congrFun ha (.inl i)
    simp [Matrix.PSp4Three.e,f,Pi.smul_apply,smul_eq_mul] at hh
  obtain ⟨g,hg⟩ := exists_projective_send (ePoint (F := F) i) (fPoint i)
  intro htop
  have hm : g ∈ MulAction.stabilizer (PSp r F) (ePoint (F := F) i) := by
    rw [←rootNormalizer_eq_lineStabilizer,htop]
    exact mem_top g
  exact hne ((MulAction.mem_stabilizer_iff.mp hm).symm.trans hg)

omit [CharP F 2] in
private theorem tailHom_fixes_first_point (k : ℕ) (g : Sp k F) :
    projection (tailHom k g) • ePoint (n := k+1) (F := F) 0 = ePoint (n := k+1) (F := F) 0 := by
  have he : tailHom k g • Matrix.PSp4Three.e (n := k+1) (F := F) 0 = Matrix.PSp4Three.e 0 := by
    apply (headTail k).injective
    simp only [tailHom_headTail,headTail_e,smul_zero]
  simp only [projection_smul,ePoint,Projectivization.smul_mk,he]

/-- The chosen root parabolic in every higher symplectic rank is proper. -/
theorem symplecticParabolic_zero_ne_top (n : ℕ) :
    symplecticParabolic (F := F) n 0 ≠ ⊤ := rootNormalizer_ne_top 0

/-- The iterated complementary Sp₆ factor lies in the original first-line parabolic. -/
theorem symplecticSixRange_le_parabolic (n : ℕ) :
    symplecticSixRange (F := F) n ≤ symplecticParabolic n 0 := by
  rintro _ ⟨g,rfl⟩
  change symplecticSixHom n g ∈ normalizer (SymplecticRoot.rootSubgroup (F := F) (r := 4+n) 0 : Set (PSp (4+n) F))
  rw [rootNormalizer_eq_lineStabilizer]
  apply MulAction.mem_stabilizer_iff.mpr
  cases n with
  | zero => exact tailHom_fixes_first_point 3 g
  | succ n => exact tailHom_fixes_first_point (4+n) (tailIterSp n g)

end Theory.SpecificGroups.Symplectic
