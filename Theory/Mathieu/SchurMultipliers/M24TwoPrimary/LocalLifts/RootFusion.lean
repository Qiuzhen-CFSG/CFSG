module

public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.Reduction
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage
import all Theory.Mathieu.M24.LocalGeometry.LinearFourCore

/-!
# Fusion of an octad root with a translation in native M₂₄

The native heptad alternating section lifts a double transposition of A₇ to
an involution in the chosen octad stabilizer. The labelled point action proves
that its octad permutation is exactly a product of two disjoint swaps. Both
this element and every pointwise translation fix the distinguished ambient
point. The checked two-class coverage of M₂₄ involutions and the absence of
fixed points for class 2B put both nonidentity involutions in class 2A.

This supplies the literal ambient fusion witness used to transport an
involutory translation lift through the original covering map. The private
`import all` is used only to prove the evaluation equation for the existing
non-exposed octad action; its public boundary is unchanged.

Source context: Aschbacher–Smith, I.1.3, printed p.407; GLS3 §6.1 and
Table 5.3e. The native heptad section and the involution coverage are proved
in the imported Mathieu geometry and permutation-certificate modules.
-/

open Subgroup PerfectCentralCovering
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
open Sporadic.Mathieu.M23Geometry
open Sporadic.Mathieu.M24InvolutionCentralizers
namespace Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary

@[expose] public section
noncomputable section

private theorem literal_action_apply (g : OctadGroup) (i : seedOctad.val) :
    (action seedOctad g i).val = g.val.val i.val := rfl

private theorem isConj_twoA_of_fixed (x : M24) (hx : orderOf x = 2)
    (i : Fin 24) (hi : x.val i = i) : IsConj involution2A x := by
  rcases involution_classes x hx with h | h
  · exact h
  · obtain ⟨g, hg⟩ := isConj_iff.mp h
    have hc : x.val.support.card = 24 := by
      rw [← hg]
      change (g.val * involution2B.val * g.val⁻¹).support.card = 24
      rw [Equiv.Perm.card_support_conj]
      exact m24Involution2B_fixed_card
    have ht : x.val.support = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hc)
    have hm : i ∈ x.val.support := ht ▸ Finset.mem_univ i
    exact ((Equiv.Perm.mem_support.mp hm) hi).elim

private def doubleSwap : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩

private def rootElement : OctadGroup := heptadLift (AlternatingSection.s doubleSwap)

private theorem rootElement_sq : rootElement ^ 2 = 1 := by
  have hd : doubleSwap^2 = 1 := by
    apply Subtype.ext
    change (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3)^2 = 1
    decide
  change (heptadLift (AlternatingSection.s doubleSwap))^2 = 1
  rw [← map_pow, ← map_pow, hd, map_one, map_one]

private def octadLabel (i : Fin 7) : seedOctad.val :=
  ⟨m23PointEmbedding (label i), (mem_seedOctad _).mpr
    (Or.inr ⟨label i, (labelEquiv i).property, rfl⟩)⟩

private theorem octadLabel_injective : Function.Injective octadLabel := by
  intro i j h
  apply label.injective
  apply m23PointEmbedding.injective
  exact congrArg (fun x : seedOctad.val => (x : Fin 24)) h

private theorem rootElement_label (i : Fin 7) :
    action seedOctad rootElement (octadLabel i) = octadLabel (doubleSwap.val i) := by
  apply Subtype.ext
  rw [literal_action_apply]
  change (rootElement.val.val) (m23PointEmbedding (label i)) = _
  rw [rootElement, heptadLift_coe, m23ExtendHom_apply_embedded]
  exact congrArg m23PointEmbedding (AlternatingSection.s_label doubleSwap i)

private theorem rootElement_action :
    action seedOctad rootElement =
      Equiv.swap (octadLabel 0) (octadLabel 1) * Equiv.swap (octadLabel 2) (octadLabel 3) := by
  classical
  apply Equiv.ext
  intro x
  rcases (mem_seedOctad x.val).mp x.property with h | ⟨j,hj,hj'⟩
  · have hx : x = ⟨(24 : Fin 24), (mem_seedOctad _).mpr (Or.inl rfl)⟩ := Subtype.ext h
    subst x
    have hn (i : Fin 7) :
        (⟨(24 : Fin 24), (mem_seedOctad _).mpr (Or.inl rfl)⟩ : seedOctad.val) ≠ octadLabel i := by
      intro he
      have he' := congrArg Subtype.val he
      change (24 : Fin 24) = m23PointEmbedding (label i) at he'
      have hne : ∀ j : Fin 23, m23PointEmbedding j ≠ (24 : Fin 24) :=
        fun j => (m23PointEquiv j).property
      exact hne (label i) he'.symm
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (hn 2) (hn 3),
      Equiv.swap_apply_of_ne_of_ne (hn 0) (hn 1)]
    apply Subtype.ext
    rw [literal_action_apply]
    change rootElement.val.val (24 : Fin 24) = (24 : Fin 24)
    rw [rootElement, heptadLift_coe]
    exact m23ExtendHom_apply_24 _
  · obtain ⟨i,hi⟩ := labelEquiv.surjective ⟨j,hj⟩
    have he : x = octadLabel i := by
      apply Subtype.ext
      exact hj'.symm.trans (congrArg m23PointEmbedding (congrArg Subtype.val hi)).symm
    rw [he, rootElement_label]
    change octadLabel ((Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 7)) i) = _
    simp only [Equiv.Perm.mul_apply, octadLabel_injective.map_swap]

private theorem rootElement_isRoot : IsOctadRoot rootElement := by
  classical
  change (action seedOctad rootElement).cycleType = {2,2}
  rw [rootElement_action]
  apply Equiv.Perm.cycleType_swap_mul_swap_of_nodup
  exact List.Nodup.map octadLabel_injective (by decide : ([0,1,2,3] : List (Fin 7)).Nodup)

private theorem rootElement_ne_one : rootElement ≠ 1 := by
  intro h
  have ht := rootElement_isRoot
  simp [IsOctadRoot, h] at ht

private theorem rootElement_fixed : rootElement.val.val (24 : Fin 24) = (24 : Fin 24) := by
  rw [rootElement, heptadLift_coe]
  exact m23ExtendHom_apply_24 _

/-- A literal octad double transposition is fused in native M₂₄ to a nonidentity
pointwise translation. The representatives and their actions are constructed above. -/
theorem exists_octad_root_fusion : ∃ (v : octadKernel) (a : OctadGroup),
    IsOctadRoot a ∧ IsConj (v.val : M24) (a : M24) := by
  have hcard : Nat.card octadKernel = 16 := kernel_card
  let : Nontrivial octadKernel := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  obtain ⟨v,hv⟩ := exists_ne (1 : octadKernel)
  have hv2 : (v.val : M24)^2 = 1 :=
    congrArg (fun w : octadKernel => (w.val : M24)) (kernel_sq v)
  have hv1 : (v.val : M24) ≠ 1 := by
    intro h
    exact hv (Subtype.ext (Subtype.ext h))
  have hvo : orderOf (v.val : M24) = 2 := orderOf_eq_prime hv2 hv1
  have hvfix : v.val.val.val (24 : Fin 24) = (24 : Fin 24) :=
    (mem_action_ker seedOctad v.val).mp v.property _ ((mem_seedOctad _).mpr (Or.inl rfl))
  have hva := isConj_twoA_of_fixed (v.val : M24) hvo (24 : Fin 24) hvfix
  have hao : orderOf (rootElement : M24) = 2 := orderOf_eq_prime
    (congrArg Subtype.val rootElement_sq)
    (fun h => rootElement_ne_one (Subtype.ext h))
  have haa := isConj_twoA_of_fixed (rootElement : M24) hao (24 : Fin 24) rootElement_fixed
  exact ⟨v, rootElement, rootElement_isRoot, hva.symm.trans haa⟩

end
end
end Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
