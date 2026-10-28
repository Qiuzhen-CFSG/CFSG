module
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers.Reduction
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry

/-!
# Recovering the unitary-five line from its projective radical

The fixed space of the line radical in SU₅ is exactly the marked isotropic
line: a scalar unipotent equates the first two coordinates, and three vector
unipotents kill the remaining coordinates. Thus its normalizer preserves
the line. In the projective group, equal fourth-power-one lifts coincide:
their central ratio has order dividing both four and the scalar kernel's
order five. This lifts radical normalization without identifying SU₅ and PSU₅.

The consumer uses the characteristic two-core of the line residual to prove
the native flag-normalizer bridge required by Aschbacher–Smith 5.3.2 and
F.4.3, printed pp.659 and274 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.FullNormalizerRealization
open LineCore LineCore.Parabolic
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (J : HermitianForm 5 F)

omit [CharP F 2] in
private theorem project_injective_fourth (hconj : ∀ x, J.conj x = x ^ 4)
    (hcard : Nat.card F = 16) (a b : J.specialSubgroup)
    (ha : a ^ 4 = 1) (hb : b ^ 4 = 1) (he : project J a = project J b) : a = b := by
  let z := a * b⁻¹
  have hk : z ∈ (project J).ker := by simp [z, MonoidHom.mem_ker, he]
  have hz : Commute z b := (mem_center_iff.mp (project_kernel_le_center J hk) b).symm
  have h4 : z ^ 4 = 1 := by
    have hh := hz.mul_pow 4
    rw [show z * b = a by simp [z], ha, hb, mul_one] at hh
    exact hh.symm
  let zk : (project J).ker := ⟨z,hk⟩
  have hd4 : orderOf zk ∣ 4 := orderOf_dvd_of_pow_eq_one (Subtype.ext h4)
  have hd5 : orderOf zk ∣ 5 := (orderOf_dvd_natCard zk).trans
    (dvd_of_eq (card_project_kernel J hconj hcard))
  have hone : orderOf zk = 1 := Nat.dvd_one.mp (Nat.dvd_gcd hd4 hd5)
  exact mul_inv_eq_one.mp (congrArg Subtype.val (orderOf_eq_one_iff.mp hone))

omit [Finite F] in
/-- The common fixed space of the actual SU line radical is the marked line. -/
theorem line_radical_fixedSpace (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    IsotropicGeometry.fixedSpace J (toSU J hJ).range = line F := by
  ext v
  constructor
  · intro hv
    have hfix (u : Coord J) : ambientMatrix J u *ᵥ v = v := by
      have hh := hv (toSU J hJ u) ⟨u,rfl⟩
      change (ambientGL J u).val *ᵥ v = v at hh
      rwa [ambientGL_val] at hh
    let u : Coord J := ⟨0,1,by simp [CharTwo.add_self_eq_zero]⟩
    have h01 : v 1 = v 0 := by
      have hh := congrFun (hfix u) 0
      simpa [ambientMatrix, u, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        CharTwo.add_self_eq_zero] using hh
    have htail (i : Fin 3) : v ⟨i.val + 2, by omega⟩ = 0 := by
      have hh := congrFun (hfix (Coord.liftVector c hc (Pi.single i 1))) 0
      fin_cases i <;>
        simp [ambientMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
          Coord.liftVector, h01, add_mul, add_assoc] at hh ⊢ <;>
        simpa only [←add_assoc, CharTwo.add_self_eq_zero, zero_add] using hh
    exact ⟨h01, htail 0, htail 1, htail 2⟩
  · intro hv u hu
    obtain ⟨x,rfl⟩ := hu
    exact toSU_fixes_line J hJ x v hv

/-- The normalizer of the projective line radical lies in its full parabolic.
The lift uses fourth-power uniqueness across the actual kernel of order five. -/
theorem normalizer_line_radical_le_parabolic (hconj : ∀ x, J.conj x = x ^ 4)
    (hcard : Nat.card F = 16) (hJ : J.form = 1) :
    normalizer (((projectiveUnipotent J hJ).map (lineParabolic J).subtype) :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ lineParabolic J := by
  intro g hg
  obtain ⟨A,rfl⟩ := project_surjective J g
  have hnorm : A ∈ normalizer ((toSU J hJ).range : Set J.specialSubgroup) := by
    apply mem_normalizer_iff.mpr
    intro B
    have forward (A : J.specialSubgroup)
        (hA : project J A ∈ normalizer (((projectiveUnipotent J hJ).map (lineParabolic J).subtype) :
          Set (ProjectiveSpecialUnitaryMatrixGroup J)))
        (B : J.specialSubgroup) (hB : B ∈ (toSU J hJ).range) :
        A * B * A⁻¹ ∈ (toSU J hJ).range := by
      obtain ⟨u,rfl⟩ := hB
      have hu : project J (toSU J hJ u) ∈
          (projectiveUnipotent J hJ).map (lineParabolic J).subtype :=
        ⟨toParabolic J hJ u, ⟨u,rfl⟩, rfl⟩
      obtain ⟨v,⟨w,rfl⟩,hw⟩ := (mem_normalizer_iff.mp hA _).mp hu
      have he : toSU J hJ w = A * toSU J hJ u * A⁻¹ :=
        project_injective_fourth J hconj hcard _ _
          (by rw [←map_pow, Coord.fourth_power, map_one])
          (by rw [conj_pow, ←map_pow, Coord.fourth_power, map_one]; simp)
          (by
            change project J (toSU J hJ w) = _ at hw
            simpa only [map_mul,map_inv] using hw)
      exact ⟨w,he⟩
    constructor
    · exact forward A hg B
    · intro hB
      have hh := forward A⁻¹ ((normalizer _).inv_mem hg) (A*B*A⁻¹) hB
      simpa [mul_assoc] using hh
  obtain ⟨c,hc⟩ := RadicalCentralizers.exists_trace_one J hconj hcard
  have hm := IsotropicGeometry.normalizer_le_fixedSpace_stabilizer J (toSU J hJ).range hnorm
  rw [line_radical_fixedSpace J c hc hJ] at hm
  exact ⟨A,hm,rfl⟩

end Theory.SpecificGroups.UnitaryFive.FullNormalizerRealization
