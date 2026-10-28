module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.SemilinearReduction
public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Opposite root groups in the actual projective SU₃ image

The upper root group is the image of the Hermitian Heisenberg coordinates
`(a,b)` satisfying `b + conj b + a * conj a = 0`. The opposite root group is
its conjugate by the explicit Weyl matrix. The coordinate maps are injective,
and the two images intersect trivially, in every characteristic.

These are the concrete root groups used in the normalization step of
Steinberg's twisted automorphism theorem (Theorem 36, proof steps (1)–(7),
`refs/KGroup/GLS3/Chapter2St1.tex`), underlying GLS3, Theorem 2.5.12 and §2.7.
Generation and automorphism normalization are separate assertions; neither is
part of the definitions here.
-/

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- The upper Hermitian root homomorphism into the actual projective image. -/
public abbrev root : hermitianUnipotentCoord J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  hermitianUnipotentPSU J hJ

/-- The Weyl element interchanging the two coordinate isotropic points. -/
public abbrev weyl : ProjectiveSpecialUnitaryMatrixGroup J := hermitianWeylPSU J hJ

/-- The opposite root homomorphism, with the same coordinate convention. -/
@[expose] public def oppositeRoot :
    hermitianUnipotentCoord J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (MulAut.conj (weyl J hJ)).toMonoidHom.comp (root J hJ)

/-- The upper root subgroup, defined by its actual matrix parametrization. -/
@[expose] public def rootGroup : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (root J hJ).range

/-- The lower root subgroup, defined by its actual matrix parametrization. -/
@[expose] public def oppositeRootGroup : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (oppositeRoot J hJ).range

public theorem oppositeRoot_apply (z : hermitianUnipotentCoord J) :
    oppositeRoot J hJ z = weyl J hJ * root J hJ z * (weyl J hJ)⁻¹ := rfl

public theorem oppositeRootGroup_eq_map :
    oppositeRootGroup J hJ = (rootGroup J hJ).map (MulAut.conj (weyl J hJ)).toMonoidHom := by
  exact MonoidHom.range_comp _ _

public theorem root_injective : Function.Injective (root J hJ) := by
  intro z t h
  have hp : ProjGenLinGroup.mk (hermitianUnipotentGL J z) =
      ProjGenLinGroup.mk (hermitianUnipotentGL J t) := congrArg Subtype.val h
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have hc1 : c = 1 := by
    apply Units.ext
    have he := congrArg (fun M : GL (Fin 3) E => M.val 0 0) hc
    simpa [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal,
      hermitianUnipotentGL, hermitianUnipotentMatrix] using he
  rw [hc1, map_one, mul_one] at hc
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun M : GL (Fin 3) E => M.val 0 1) hc
  · exact congrArg (fun M : GL (Fin 3) E => M.val 0 2) hc

public theorem oppositeRoot_injective : Function.Injective (oppositeRoot J hJ) :=
  (MulAut.conj (weyl J hJ)).injective.comp (root_injective J hJ)

private theorem weylGL_square :
    (hermitianWeylGL : GL (Fin 3) E) * hermitianWeylGL = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem weylGL_inv : (hermitianWeylGL : GL (Fin 3) E)⁻¹ = hermitianWeylGL :=
  inv_eq_of_mul_eq_one_left weylGL_square

private theorem opposite_matrix (z : hermitianUnipotentCoord J) :
    ((hermitianWeylGL : GL (Fin 3) E) * hermitianUnipotentGL J z * hermitianWeylGL).val =
      !![1, 0, 0; J.conj z.val.1, 1, 0; z.val.2, -z.val.1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylGL, hermitianWeylMatrix, hermitianUnipotentGL,
      hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- Upper and lower root groups have trivial intersection, including in
characteristic three; no trace argument is used. -/
public theorem rootGroup_inf_oppositeRootGroup :
    rootGroup J hJ ⊓ oppositeRootGroup J hJ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨z, rfl⟩ := hx.1
  obtain ⟨t, ht⟩ := hx.2
  have hp : ProjGenLinGroup.mk (hermitianUnipotentGL J z) =
      ProjGenLinGroup.mk (hermitianWeylGL * hermitianUnipotentGL J t *
        (hermitianWeylGL : GL (Fin 3) E)) := by
    have he := congrArg Subtype.val ht.symm
    simpa only [oppositeRoot_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      hermitianUnipotentPSU_val, hermitianWeylPSU_val, ← map_inv, ← map_mul,
      weylGL_inv] using he
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have hc1 : c = 1 := by
    apply Units.ext
    have he := congrArg (fun M : GL (Fin 3) E => M.val 0 0) hc
    change (hermitianUnipotentGL J z * GeneralLinearGroup.scalar (Fin 3) c).val 0 0 = _ at he
    rw [opposite_matrix] at he
    simpa [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal,
      hermitianUnipotentGL, hermitianUnipotentMatrix] using he
  rw [hc1, map_one, mul_one] at hc
  have hmat := congrArg (fun M : GL (Fin 3) E => M.val) hc
  rw [opposite_matrix] at hmat
  have hz1 : z.val.1 = 0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) hmat
  have hz2 : z.val.2 = 0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) hmat
  have hz : z = 1 := Subtype.ext (Prod.ext hz1 hz2)
  exact Subgroup.mem_bot.mpr (by rw [hz, map_one])

/-- The explicit upper root image has order `q³`, for fixed-field order `q`. -/
public theorem rootGroup_card [Finite E] (q : ℕ)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Nat.card (rootGroup J hJ) = q ^ 3 := by
  obtain ⟨_, _, _, _, _, _, hroot, _⟩ :=
    huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R, _, _, _, _, _, _, _, hRcard, _, _, _, _, ⟨e, _⟩, _⟩ := hroot
  let er : hermitianUnipotentCoord J ≃* rootGroup J hJ :=
    MulEquiv.ofBijective (root J hJ).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr (root_injective J hJ),
        (root J hJ).rangeRestrict_surjective⟩
  exact (Nat.card_congr er.toEquiv).symm.trans ((Nat.card_congr e).trans hRcard)

/-- In prime fixed-field order, the root image is a group of prime-power order.
Maximality among such subgroups is a separate geometric assertion. -/
public theorem rootGroup_isPGroup [Finite E] {p : ℕ}
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p) :
    IsPGroup p (rootGroup J hJ) :=
  IsPGroup.of_card (rootGroup_card J hJ p hcard hfixed)

/-- The two concrete root groups are distinct for fixed-field order greater
than one. In particular this includes fixed-field order three. -/
public theorem rootGroup_ne_oppositeRootGroup [Finite E] {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    rootGroup J hJ ≠ oppositeRootGroup J hJ := by
  intro heq
  have hbot : rootGroup J hJ = ⊥ := by
    have hi := rootGroup_inf_oppositeRootGroup J hJ
    rwa [← heq, inf_idem] at hi
  have hc := rootGroup_card J hJ q hcard hfixed
  rw [hbot, Subgroup.card_bot] at hc
  have hq3 : 1 < q ^ 3 := one_lt_pow₀ hq (by decide)
  omega

/-- Equality on the two concrete root families determines a homomorphism once
those subgroups are known to generate. -/
public theorem hom_ext_of_rootGroup_sup_eq_top
    (hgen : rootGroup J hJ ⊔ oppositeRootGroup J hJ = ⊤)
    {G : Type*} [Group G]
    (f g : ProjectiveSpecialUnitaryMatrixGroup J →* G)
    (hroot : ∀ z, f (root J hJ z) = g (root J hJ z))
    (hopposite : ∀ z, f (oppositeRoot J hJ z) = g (oppositeRoot J hJ z)) : f = g := by
  have hle : rootGroup J hJ ⊔ oppositeRootGroup J hJ ≤ f.eqLocus g := by
    apply sup_le
    · rintro x ⟨z, rfl⟩
      exact hroot z
    · rintro x ⟨z, rfl⟩
      exact hopposite z
  apply MonoidHom.ext
  intro x
  exact hle (hgen.symm ▸ Subgroup.mem_top x)

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
