module

public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeTensor
public import Theory.GroupTheory.PResidual.NormalSubgroup
import all CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeTensor

/-!
# A cubic residual actor on the original M22 pair

The cubic actor is lifted inside the actual
two-residual of I.  Its order in I is not assumed to be three: only its image
in I/O₂(I) has order three.  The existing multiplicity action proves that
this particular residual representative has no nonidentity fixed point on
the original P/U.  Thus it moves every nontrivial subgroup of P/U, including
the moved four-space used to generate the mixed normal closure.

The direct commutator application uses the original inclusion and quotient
representatives. Source: Aschbacher--Smith 8.2.8(5) and 8.2.9, printed
pp.718--721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction
  Normalizer.SmallOvergroups Normalizer.TensorRecognition

set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]

/-- The original pair residual contains an actor with fixed-point-free
action on the literal P/U.  Both the residual membership and the action
are proved from the native multiplicity coordinates. -/
theorem m22_residual_cubic_fixed_free
    {R I V U : Subgroup G} {i : I}
    {fq : R →* MathieuCode.M22Quintet.Q}
    (hm : M22CodePairMultiplicityAction R I V U i fq)
    (hc : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2))) :
    ∃ hYP : R ⊔ I ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : R ⊔ I ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          ∃ a : pResidual 2 I,
            ∀ x : I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2),
              sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU
                (inclusion le_sup_right a.val) x = x → x = 1 := by
  obtain ⟨hYP,hYU,hUP,hBU,eB,rA,eP,μ,hrsur,hrker,hrval,hμ,heP,hR,hact⟩ := hm
  let := hUP
  let := hBU
  obtain ⟨e⟩ := hc
  let eI := (e.trans Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm).trans
    nonempty_dihedralThreeEquivPerm.some
  let q := eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hq : Function.Surjective q := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  have horder : orderOf InvertedCubicTensor.cubic = 3 :=
    orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hcR : InvertedCubicTensor.cubic ∈ pResidual 2 InvertedCubicTensor.S₃ :=
    mem_pResidual_of_orderOf_coprime (by rw [horder]; decide)
  have hcMap : InvertedCubicTensor.cubic ∈ (pResidual 2 I).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact hcR
  obtain ⟨a,ha,hac⟩ := hcMap
  have hpow : (QuotientGroup.mk' (pCore 2 I) a)^3 = 1 := by
    apply eI.injective
    rw [map_pow,show eI (QuotientGroup.mk' (pCore 2 I) a) =
      InvertedCubicTensor.cubic from hac,map_one]
    decide +kernel
  have hne : QuotientGroup.mk' (pCore 2 I) a ≠ 1 := by
    intro hz
    have he : InvertedCubicTensor.cubic = 1 := by
      rw [←hac]
      change eI (QuotientGroup.mk' (pCore 2 I) a) = 1
      rw [hz,map_one]
    have hn : InvertedCubicTensor.cubic ≠ 1 := by decide +kernel
    exact hn he
  have hfree (c : Fin 2 → ZMod 2)
      (hfix : μ (QuotientGroup.mk' (pCore 2 I) a) c = c) : c = 0 :=
    ScalarMultiplicity.binary_plane_odd_fixed_eq_zero μ hμ
      (QuotientGroup.mk' (pCore 2 I) a) 3 (by decide) hpow hne c hfix
  refine ⟨hYP,hYU,hUP,⟨a,ha⟩,?_⟩
  intro x hx
  apply multiplicity_pair_fixed_eq_one
    ((MulEquiv.toMultiplicative_toAdditive.prodCongr
      MulEquiv.toMultiplicative_toAdditive).trans eP)
    (sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU (inclusion le_sup_right a))
    (μ (QuotientGroup.mk' (pCore 2 I) a)) (hact a) hfree x hx

/-- The same original residual element fixes no nonidentity element of
P modulo U, stated directly in the ambient group's commutator convention. -/
theorem m22_residual_cubic_centralizer_modulo
    {R I V U : Subgroup G} {i : I}
    {fq : R →* MathieuCode.M22Quintet.Q}
    (hm : M22CodePairMultiplicityAction R I V U i fq)
    (hc : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2))) :
    ∃ a : pResidual 2 I, ∀ p : G, p ∈ I.pCoreIn 2 →
      ⁅(a.val : G),p⁆ ∈ U → p ∈ U := by
  obtain ⟨hYP,hYU,hUP,a,hfree⟩ := m22_residual_cubic_fixed_free hm hc
  let := hUP
  refine ⟨a,?_⟩
  intro p hp hcomm
  let x : I.pCoreIn 2 := ⟨p,hp⟩
  have hfix : sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU
      (inclusion le_sup_right a.val)
      (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) x) =
        QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) x := by
    rw [sectionAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (a.val : G) * p * (a.val : G)⁻¹ / p ∈ U
    simpa only [commutatorElement_def,div_eq_mul_inv] using hcomm
  exact (QuotientGroup.eq_one_iff x).mp (hfree _ hfix)

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
