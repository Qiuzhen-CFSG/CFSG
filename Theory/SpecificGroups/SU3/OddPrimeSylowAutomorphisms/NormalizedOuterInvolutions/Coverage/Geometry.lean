module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootSylow

/-!
# Generation and simultaneous normalization of opposite PSU₃ roots

Huppert II.10.12 gives the doubly transitive action on isotropic points, a root
subgroup regular away from its fixed point, and coordinate witnesses. We first
identify that subgroup with the actual upper matrix root group. Since the point
stabilizer normalizes the root group, conjugate roots with the same fixed point
are equal.

Two distinct opposite roots generate a transitive subgroup: a nonidentity upper
root element moves the opposite point, and an opposite root element carries the
upper point to its image. Transitivity then puts every conjugate of the upper
root inside their join. Simplicity makes its nontrivial normal closure the whole
group. For automorphisms, Sylow conjugacy locates the two image roots, and double
transitivity supplies a single inner automorphism normalizing both.

This proves the geometric normalization step in Steinberg, Theorem 36
(`refs/KGroup/GLS3/Chapter2St1.tex`), underlying GLS3, Theorem 2.5.12 and §2.7.
The concrete action and coordinates come from
`BenderSuzuki/External/Huppert/II/theorem_10_12.lean`. The argument includes
fixed-field order three; it needs neither the congruence modulo eight nor a
perfectness assumption.
-/

open Matrix BenderSuzuki.External
open scoped LinearAlgebra.Projectivization
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage

private abbrev isotropicPoints {E : Type*} [Field E] (J : HermitianForm 3 E) :=
  {x : ℙ E (Fin 3 → E) // ∃ (v : Fin 3 → E) (hv : v ≠ 0),
    x = Projectivization.mk E v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}

private theorem root_action {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    ∃ (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (isotropicPoints J))
      (alpha : isotropicPoints J),
      (∀ u ∈ rootGroup J hJ, rho u alpha = alpha) ∧
      (∀ g, rho g alpha = alpha →
        (rootGroup J hJ).map (MulAut.conj g).toMonoidHom = rootGroup J hJ) ∧
      (∀ x y, x ≠ alpha → y ≠ alpha →
        ∃! u : rootGroup J hJ, rho u.val x = y) ∧
      (∀ x y z t, x ≠ y → z ≠ t →
        ∃ g, rho g x = z ∧ rho g y = t) := by
  obtain ⟨_, rho, alpha, _, _, _, hroot, htwo, _⟩ :=
    huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R, _, hRfix, _, hRnorm, _, _, _, _, _, _, _, hregular,
    ⟨coord, hcoord⟩, _⟩ := hroot
  have hcoord_eq (z : hermitianUnipotentCoord J) :
      (coord z).val = root J hJ z := by
    obtain ⟨M, hM, heq⟩ := hcoord z
    have hM' : M = hermitianUnipotentGL J z := Units.ext hM
    apply Subtype.ext
    simpa only [hM', hermitianUnipotentPSU_val] using heq
  have hR : R = rootGroup J hJ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨z, hz⟩ := coord.surjective ⟨r, hr⟩
      exact ⟨z, (hcoord_eq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro r ⟨z, rfl⟩
      rw [← hcoord_eq z]
      exact (coord z).property
  subst R
  refine ⟨rho, alpha, ?_, ?_, hregular, htwo⟩
  · exact fun u hu => hRfix hu
  · intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRnorm hg)

private theorem map_conj_mul {G : Type*} [Group G] (U : Subgroup G) (g h : G) :
    (U.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      U.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_aut_mul {G : Type*} [Group G] (U : Subgroup G) (a b : MulAut G) :
    (U.map b.toMonoidHom).map a.toMonoidHom = U.map (a * b).toMonoidHom :=
  Subgroup.map_map U _ _

private theorem conjugate_eq_of_point_eq {G X : Type*} [Group G]
    (rho : G →* Equiv.Perm X) (U : Subgroup G) (alpha : X)
    (hnorm : ∀ g, rho g alpha = alpha → U.map (MulAut.conj g).toMonoidHom = U)
    (g h : G) (hpoint : rho g alpha = rho h alpha) :
    U.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj h).toMonoidHom := by
  have hn : U.map (MulAut.conj (h⁻¹ * g)).toMonoidHom = U := by
    apply hnorm
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [hpoint]
    exact (rho h).symm_apply_apply alpha
  calc
    U.map (MulAut.conj g).toMonoidHom =
        (U.map (MulAut.conj (h⁻¹ * g)).toMonoidHom).map
          (MulAut.conj h).toMonoidHom := by rw [map_conj_mul]; simp
    _ = U.map (MulAut.conj h).toMonoidHom := by rw [hn]

private theorem exists_root_conjugate {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ g, (rootGroup J hJ).map (MulAut.conj g).toMonoidHom =
      (rootGroup J hJ).map a.toMonoidHom := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let P := rootSylow J hJ hp hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J)
    P (P.mapSurjective (f := a.toMonoidHom) a.surjective)
  have heq : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
      (MulAut.conj g).toMonoidHom =
        (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map a.toMonoidHom :=
    congrArg Sylow.toSubgroup hg
  exact ⟨g, by simpa only [P, rootSylow_coe] using heq⟩

private theorem conjugate_transitive {G X : Type*} [Group G]
    (rho : G →* Equiv.Perm X) (U : Subgroup G) (alpha : X)
    (hregular : ∀ x y, x ≠ alpha → y ≠ alpha →
      ∃! u : U, rho u.val x = y)
    (w : G) (x y : X) (hx : x ≠ rho w alpha) (hy : y ≠ rho w alpha) :
    ∃ v ∈ U.map (MulAut.conj w).toMonoidHom, rho v x = y := by
  have hx' : (rho w).symm x ≠ alpha := by
    intro heq
    apply hx
    rw [← heq, Equiv.apply_symm_apply]
  have hy' : (rho w).symm y ≠ alpha := by
    intro heq
    apply hy
    rw [← heq, Equiv.apply_symm_apply]
  obtain ⟨u, hu, _⟩ := hregular _ _ hx' hy'
  refine ⟨w * u.val * w⁻¹, ⟨u.val, u.property, rfl⟩, ?_⟩
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
  change rho w (rho u.val ((rho w).symm x)) = y
  rw [hu, Equiv.apply_symm_apply]

private theorem sup_conjugate_eq_top {G X : Type*} [Group G] [IsSimpleGroup G]
    (rho : G →* Equiv.Perm X) (U : Subgroup G) (alpha : X)
    (hnorm : ∀ g, rho g alpha = alpha → U.map (MulAut.conj g).toMonoidHom = U)
    (hregular : ∀ x y, x ≠ alpha → y ≠ alpha →
      ∃! u : U, rho u.val x = y)
    (hU : U ≠ ⊥) (w : G) (hw : rho w alpha ≠ alpha) :
    U ⊔ U.map (MulAut.conj w).toMonoidHom = ⊤ := by
  let V := U.map (MulAut.conj w).toMonoidHom
  let H := U ⊔ V
  let beta := rho w alpha
  have hUle : U ≤ H := le_sup_left
  have hVle : V ≤ H := le_sup_right
  obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hmove : rho u.val beta ≠ beta := by
    intro hbad
    obtain ⟨r, _, hr⟩ := hregular beta beta hw hw
    apply hu
    exact (hr u hbad).trans (hr 1 (by simp)).symm
  obtain ⟨v, hv, hvpoint⟩ := conjugate_transitive rho U alpha hregular w
    alpha (rho u.val beta) hw.symm hmove
  let t := u.val⁻¹ * v
  have ht : t ∈ H := H.mul_mem
    (H.inv_mem (hUle u.property)) (hVle hv)
  have htpoint : rho t alpha = beta := by
    simp only [t, map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [hvpoint]
    exact (rho u.val).symm_apply_apply beta
  have htrans (x : X) : ∃ h ∈ H, rho h alpha = x := by
    by_cases hx : x = alpha
    · exact ⟨1, H.one_mem, by simp [hx]⟩
    · obtain ⟨r, hr, _⟩ := hregular beta x hw hx
      refine ⟨r.val * t, H.mul_mem (hUle r.property) ht, ?_⟩
      simpa only [map_mul, Equiv.Perm.mul_apply, htpoint] using hr
  have hconjugates (g : G) : U.map (MulAut.conj g).toMonoidHom ≤ H := by
    obtain ⟨h, hh, hpoint⟩ := htrans (rho g alpha)
    rw [conjugate_eq_of_point_eq rho U alpha hnorm g h hpoint.symm]
    rintro x ⟨u, hu, rfl⟩
    exact H.mul_mem (H.mul_mem hh (hUle hu)) (H.inv_mem hh)
  have hclosure : Subgroup.normalClosure (U : Set G) ≤ H := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨u, hu, hg⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hg
    exact hconjugates g ⟨u, hu, rfl⟩
  have htop : Subgroup.normalClosure (U : Set G) = ⊤ := by
    apply Subgroup.normalClosure_normal.eq_bot_or_eq_top.resolve_left
    intro hbot
    exact hU (le_bot_iff.mp (hbot ▸ Subgroup.le_normalClosure))
  exact top_le_iff.mp (htop ▸ hclosure)

/-- The actual upper and opposite matrix root groups generate the projective
special unitary group whenever that group is simple and the fixed field has
more than one element. -/
public theorem rootGroup_sup_oppositeRootGroup {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {q : ℕ} (hq : 1 < q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    rootGroup J hJ ⊔ oppositeRootGroup J hJ = ⊤ := by
  obtain ⟨rho, alpha, _, hnorm, hregular, _⟩ := root_action J hJ q hcard hfixed
  have hU : rootGroup J hJ ≠ ⊥ := by
    intro hbot
    have hc := rootGroup_card J hJ q hcard hfixed
    rw [hbot, Subgroup.card_bot] at hc
    have hq3 : 1 < q ^ 3 := one_lt_pow₀ hq (by decide)
    omega
  have hw : rho (weyl J hJ) alpha ≠ alpha := by
    intro heq
    apply rootGroup_ne_oppositeRootGroup J hJ hq hcard hfixed
    rw [oppositeRootGroup_eq_map, hnorm _ heq]
  rw [oppositeRootGroup_eq_map]
  exact sup_conjugate_eq_top rho (rootGroup J hJ) alpha hnorm hregular hU
    (weyl J hJ) hw

/-- Every automorphism of the actual projective SU₃ image is an inner
automorphism followed by an automorphism preserving each of the two opposite
matrix root groups. Prime fixed-field order suffices, including three. -/
public theorem exists_root_pair_normalization {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ (k : ProjectiveSpecialUnitaryMatrixGroup J)
      (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)),
      a = MulAut.conj k * b ∧
      (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ ∧
      (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ := by
  obtain ⟨rho, alpha, _, hnorm, _, htwo⟩ := root_action J hJ p hcard hfixed
  let U := rootGroup J hJ
  let w := weyl J hJ
  have hUV := rootGroup_ne_oppositeRootGroup J hJ hp.one_lt hcard hfixed
  obtain ⟨g, hg⟩ := exists_root_conjugate J hJ hp hcard hfixed a
  obtain ⟨h, hh⟩ := exists_root_conjugate J hJ hp hcard hfixed (a * MulAut.conj w)
  have hh' : U.map (MulAut.conj h).toMonoidHom =
      (oppositeRootGroup J hJ).map a.toMonoidHom := by
    rw [oppositeRootGroup_eq_map, map_aut_mul]
    exact hh
  have hpoints : rho g alpha ≠ rho h alpha := by
    intro heq
    apply hUV
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    rw [← hg, ← hh']
    exact conjugate_eq_of_point_eq rho U alpha hnorm g h heq
  have hw : alpha ≠ rho w alpha := by
    intro heq
    apply hUV
    rw [oppositeRootGroup_eq_map]
    exact (hnorm w heq.symm).symm
  obtain ⟨k, hkU, hkV⟩ := htwo (rho g alpha) (rho h alpha) alpha (rho w alpha)
    hpoints hw
  let b := MulAut.conj k * a
  refine ⟨k⁻¹, b, ?_, ?_, ?_⟩
  · dsimp [b]
    rw [map_inv]
    group
  · change U.map (MulAut.conj k * a).toMonoidHom = U
    rw [← map_aut_mul, ← hg, map_conj_mul]
    apply hnorm
    simpa only [map_mul, Equiv.Perm.mul_apply] using hkU
  · change (oppositeRootGroup J hJ).map (MulAut.conj k * a).toMonoidHom = _
    rw [← map_aut_mul, ← hh', map_conj_mul, oppositeRootGroup_eq_map]
    apply conjugate_eq_of_point_eq rho U alpha hnorm (k * h) w
    simpa only [map_mul, Equiv.Perm.mul_apply] using hkV

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
