module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeComponentSieve
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeComplementAutomizer

/-!
# Centerless containing component in the original M22-code branch

The literal H/O₂(H) wreath marking makes the original complement automizer
noncyclic. This excludes the symplectic row in the same component already
containing both the original A₆ residual and O²(H). The remaining models
are M11, PSL4(2), PSL5(2), and Held, so this component's full two-core
quotient has trivial center.

The original A₆ residual may still have a covering center. Its full source
embedding comparison, the remaining model exclusions and the terminal M11
extension contradiction remain needed to remove hcore. No unconditional
M22-code exclusion or M24-cocode selection is asserted here.
Source: Aschbacher--Smith 8.2.2(1), printed p.715, refs/quasithin.pdf.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterE Chapter7.NormalizedSource MathieuCode Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.MathieuShadowRows Chapter1 Chapter1.XiEmbedding
open Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The automizer of every original Xi complement is noncyclic in the temporary inside-core branch. -/
theorem sourceOrbit_m22_code_inside_core_automizer_not_cyclic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    {P C : Subgroup G}
    (hin : LocalInput 3 (T : Subgroup G) ((pResidual 2 H).map H.subtype) P C) :
    ¬ IsCyclic (automizer (T : Subgroup G) P) := by
  obtain ⟨_,_,⟨e⟩⟩ := D.sourceOrbit_m22_code_inside_core_wreath h hmany hV hnon d hH hcore
  let w := RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  let f := (e.trans w.symm).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := (e.trans w.symm).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (e.trans w.symm).injective,QuotientGroup.ker_mk']
  exact wreath_local_automizer_not_cyclic T hH.1.1.2 hin
    (D.sourceOrbit_m22_code_inside_core_solvable h hmany hV hnon d hH hcore) f hf hk

/-- The same original component has centerless full two-core quotient; the symplectic alternative is excluded by its original automizer. -/
theorem sourceOrbit_m22_code_inside_core_centerless_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let X := (pResidual 2 H).map H.subtype
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
      H ≤ centralizer ({(z : G)} : Set G) ∧
      ∃ P K : Subgroup G,
        LocalInput 3 (T : Subgroup G) X P (centralizer ({(z : G)} : Set G)) ∧
        K ∈ cComponentsIn (centralizer ({(z : G)} : Set G)) ∧
        localResidual L z ≤ K ∧
        centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (XiQuotient K) ∧ center (XiQuotient K) = ⊥ ∧
        X ≤ K ∧ Nonempty (P ≃* Plane 3) ∧
        (ExceptionalModel (XiQuotient K) ∨ Nonempty (XiQuotient K ≃* Held.He)) := by
  obtain ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,_,hXK,hP,hm⟩ :=
    D.sourceOrbit_m22_code_inside_core_same_component h hmany hV hnon d hH hcore
  have hm' := hm.resolve_left (fun hh =>
    D.sourceOrbit_m22_code_inside_core_automizer_not_cyclic h hmany hV hnon d hH hcore hin hh.2)
  exact ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,
    exceptional_or_held_center_eq_bot hm',hXK,hP,hm'⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
