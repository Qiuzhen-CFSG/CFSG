module
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Graph fixed points through the PSU₅(4) scalar quotient

Entrywise Hermitian conjugation defines automorphisms of the actual SU and
PSU carriers. The projective action is descended through the original map
to PGL. It inverts the scalar kernel of order five. Correcting any fixed
projective lift by the cube of its scalar displacement produces an actually
fixed SU lift; the fixed scalar kernel is trivial. Restriction of the same
projection therefore gives an exact equivalence of the fixed subgroups.

This is the projective descent in F.4.37(1), Aschbacher--Smith, printed p.293
of `refs/quasithin.pdf`. It does not identify arbitrary outer involutions
or assert Sylow placement in an ambient centralizer.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {F : Type*} [Field F] (J : HermitianForm 5 F) (hJ : J.form = 1)

/-- Entrywise Hermitian conjugation on the actual special unitary matrices. -/
def matrixHom : J.specialSubgroup →* J.specialSubgroup where
  toFun g := ⟨GeneralLinearGroup.map J.conj.toRingHom g.val, by
    constructor
    · have hg := g.property.1
      change J.conjTranspose g.val.val * J.form * g.val.val = J.form at hg
      rw [hJ,mul_one] at hg
      have he := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A.map J.conj) hg
      rw [Matrix.map_mul] at he
      have hmap : (1 : Matrix (Fin 5) (Fin 5) F).map J.conj = 1 := by simp
      rw [hmap] at he
      change J.conjTranspose (g.val.val.map J.conj) * J.form *
        g.val.val.map J.conj = J.form
      rw [hJ,mul_one]
      exact he
    · change GeneralLinearGroup.det (GeneralLinearGroup.map J.conj.toRingHom g.val) = 1
      rw [GeneralLinearGroup.map_det,g.property.2,map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g k := Subtype.ext (map_mul _ _ _)

theorem matrixHom_involutive : Function.Involutive (matrixHom J hJ) := by
  intro g
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact J.conj_involutive _

/-- The graph automorphism before taking the nontrivial projective quotient. -/
def matrixAut : MulAut J.specialSubgroup :=
  MulEquiv.ofBijective (matrixHom J hJ) (matrixHom_involutive J hJ).bijective

theorem matrixAut_apply (g : J.specialSubgroup) (i j : Fin 5) :
    (matrixAut J hJ g).val.val i j = J.conj (g.val.val i j) := rfl

theorem matrixAut_involutive : Function.Involutive (matrixAut J hJ) :=
  matrixHom_involutive J hJ

private theorem matrixAut_kernel (g : J.specialSubgroup) (hg : g ∈ (project J).ker) :
    matrixAut J hJ g ∈ (project J).ker := by
  have hk : ProjGenLinGroup.mk g.val = 1 := congrArg Subtype.val hg
  rw [ProjGenLinGroup.mk_eq_one,GeneralLinearGroup.center_eq_range_scalar] at hk
  obtain ⟨u,hu⟩ := hk
  apply Subtype.ext
  change ProjGenLinGroup.mk (GeneralLinearGroup.map J.conj.toRingHom g.val) = 1
  rw [←hu]
  have he : GeneralLinearGroup.map J.conj.toRingHom (GeneralLinearGroup.scalar (Fin 5) u) =
      GeneralLinearGroup.scalar (Fin 5) (Units.map J.conj.toMonoidHom u) := by
    apply Units.ext
    ext i j
    by_cases hij : i=j <;> simp [GeneralLinearGroup.coe_scalar,Matrix.scalar,hij]
  rw [he,ProjGenLinGroup.mk_scalar]

/-- The descended action uses the literal SU-to-PGL projection. -/
def projectiveHom : ProjectiveSpecialUnitaryMatrixGroup J →*
    ProjectiveSpecialUnitaryMatrixGroup J :=
  (project J).liftOfSurjective (project_surjective J)
    ⟨(project J).comp (matrixAut J hJ).toMonoidHom,by exact matrixAut_kernel J hJ⟩

theorem projectiveHom_project (g : J.specialSubgroup) :
    projectiveHom J hJ (project J g) = project J (matrixAut J hJ g) :=
  MonoidHom.liftOfRightInverse_comp_apply ..

theorem projectiveHom_involutive : Function.Involutive (projectiveHom J hJ) := by
  intro x
  obtain ⟨g,rfl⟩ := project_surjective J x
  rw [projectiveHom_project,projectiveHom_project,matrixAut_involutive]

/-- Hermitian conjugation on the actual projective special unitary carrier. -/
def projectiveAut : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  MulEquiv.ofBijective (projectiveHom J hJ) (projectiveHom_involutive J hJ).bijective

theorem projectiveAut_project (g : J.specialSubgroup) :
    projectiveAut J hJ (project J g) = project J (matrixAut J hJ g) :=
  projectiveHom_project J hJ g

theorem projectiveAut_involutive : Function.Involutive (projectiveAut J hJ) :=
  projectiveHom_involutive J hJ

variable (hconj : ∀ x, J.conj x = x^4)
include hconj

/-- The graph automorphism inverts, rather than kills, the scalar kernel. -/
theorem matrixAut_on_kernel (g : (project J).ker) :
    matrixAut J hJ g.val = g.val⁻¹ := by
  obtain ⟨u,rfl⟩ := scalarToKernel_bijective J hconj |>.2 g
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hu : (u.val : F)^5=1 := (mem_rootsOfUnity' 5 u.val).mp u.property
  have hi : J.conj (u.val : F) = (u.val : F)⁻¹ := by
    rw [hconj]
    apply (mul_eq_one_iff_eq_inv₀ u.val.ne_zero).mp
    simpa only [←pow_succ] using hu
  by_cases hij : i=j <;>
    simp [matrixAut_apply,scalarToKernel,GeneralLinearGroup.coe_scalar,Matrix.scalar,
      hij,hi,←map_inv]

/-- The projective map is injective on the graph-fixed subgroup, although its
kernel on all of SU₅(4) has order five. -/
theorem fixed_project_injective [Finite F] (hF : Nat.card F=16) :
    Function.Injective ((project J).comp (matrixAut J hJ).fixedSubgroup.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [eq_bot_iff_forall]
  intro x hx
  have hxk : x.val ∈ (project J).ker := hx
  have hxinv : x.val=x.val⁻¹ :=
    ((MulAut.mem_fixedSubgroup _ _).mp x.property).symm.trans
      (matrixAut_on_kernel J hJ hconj ⟨x.val,hxk⟩)
  have hx2 : x.val^2=1 := by
    rw [pow_two]
    exact (congrArg (fun y => x.val*y) hxinv).trans (mul_inv_cancel _)
  have hx5 : x.val^5=1 := by
    have hh := pow_card_eq_one' (x := (⟨x.val,hxk⟩ : (project J).ker))
    rw [card_project_kernel J hconj hF] at hh
    exact congrArg (fun k : (project J).ker => k.val) hh
  have hx1 : x.val=1 := by
    have hh : x.val^5=x.val := by
      calc
        x.val^5 = (x.val^2)^2*x.val := by group
        _ = x.val := by rw [hx2,one_pow,one_mul]
    exact hh.symm.trans hx5
  exact Subtype.ext hx1

/-- Each fixed projective element has an actually fixed special-unitary lift.
The correction uses the fifth-order scalar kernel, not an injective projection. -/
theorem fixed_project_surjective [Finite F] (hF : Nat.card F=16)
    (x : (projectiveAut J hJ).fixedSubgroup) :
    ∃ g : (matrixAut J hJ).fixedSubgroup, project J g.val=x.val := by
  obtain ⟨g,hg⟩ := project_surjective J x.val
  let c := matrixAut J hJ g * g⁻¹
  have hck : c ∈ (project J).ker := by
    change project J (matrixAut J hJ g * g⁻¹) = 1
    rw [map_mul,map_inv,←projectiveAut_project,hg,
      (MulAut.mem_fixedSubgroup _ _).mp x.property,mul_inv_cancel]
  have hc5 : c^5=1 := by
    have hh := pow_card_eq_one' (x := (⟨c,hck⟩ : (project J).ker))
    rw [card_project_kernel J hconj hF] at hh
    exact congrArg (fun k : (project J).ker => k.val) hh
  have hcg : matrixAut J hJ g=c*g := by simp [c,mul_assoc]
  refine ⟨⟨c^3*g,?_⟩,?_⟩
  · apply (MulAut.mem_fixedSubgroup _ _).mpr
    change matrixAut J hJ (c^3*g)=c^3*g
    rw [map_mul,map_pow,matrixAut_on_kernel J hJ hconj ⟨c,hck⟩,hcg]
    have he : (c⁻¹)^3*c=c^3 := by
      apply mul_right_cancel (b := c^3)
      calc
        ((c⁻¹)^3*c)*c^3 = c := by group
        _ = c^5*c := by rw [hc5,one_mul]
        _ = c^3*c^3 := by group
    rw [←mul_assoc,he]
  · rw [map_mul,map_pow,MonoidHom.mem_ker.mp hck,one_pow,one_mul,hg]

/-- Exact graph-fixed-group transport through the original projective map. -/
def fixedProjectEquiv [Finite F] (hF : Nat.card F=16) :
    (matrixAut J hJ).fixedSubgroup ≃* (projectiveAut J hJ).fixedSubgroup :=
  MulEquiv.ofBijective
    (((project J).comp (matrixAut J hJ).fixedSubgroup.subtype).codRestrict _ (fun g => by
      rw [MulAut.mem_fixedSubgroup,MonoidHom.comp_apply,subtype_apply,
        projectiveAut_project,(MulAut.mem_fixedSubgroup _ _).mp g.property]))
    ⟨fun x y h => fixed_project_injective J hJ hconj hF (congrArg Subtype.val h),
      fun x => by
        obtain ⟨g,hg⟩ := fixed_project_surjective J hJ hconj hF x
        exact ⟨g,Subtype.ext hg⟩⟩

theorem fixedProjectEquiv_apply [Finite F] (hF : Nat.card F=16)
    (g : (matrixAut J hJ).fixedSubgroup) :
    (fixedProjectEquiv J hJ hconj hF g).val=project J g.val := rfl
end Theory.SpecificGroups.UnitaryFive.GraphFixed
