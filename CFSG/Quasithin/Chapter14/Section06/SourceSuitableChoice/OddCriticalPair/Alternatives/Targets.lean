module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalAction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Source
public import CFSG.Quasithin.ChapterF.Section09.CriticalEndpoints
public import Theory.GroupTheory.CommutatorPreimage

/-!+# The two original critical-pair targets

These interfaces retain the actual first support, quotient action and critical
endpoint of 14.6.13. The rank-eight denominator is the literal centralizer
modulo the source point. In particular the two point containments use the
same endpoint representative. All displayed conjugations are left conjugations.

`FourCriticalGeometry` separates the endpoint calculation from recognition
of the orthogonal action. Neither structure asserts its own existence.

Source: Aschbacher--Smith 14.6.13, printed pp.1031--1032.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The rank-four endpoint geometry before choosing orthogonal coordinates. -/
structure FourCriticalGeometry {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (Mc H1 : Subgroup G) where
  dimension : Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4
  g : G
  outside : g ∉ Mc
  normalizes : U.map (MulAut.conj g).toMonoidHom ≤
    H ⊓ normalizer (firstSupport a H1 : Set G)
  reverse : U ≤ H.map (MulAut.conj g).toMonoidHom
  noncentral : ¬ ⁅firstSupport a H1,U.map (MulAut.conj g).toMonoidHom⁆ ≤ Z

/-- The whole second alternative of 14.6.13, with one actual F.9 endpoint. -/
structure RankEightCriticalPlacement {D : ChapterF.Section09.Setup G}
    (h : D.Hypothesis) [IsElementaryAbelian 2 D.UH]
    (a : LocalQuotientAction D.H D.UH D.V₁) (Mc H1 : Subgroup G) where
  dimension : Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 8
  endpoint : h.CriticalEndpoint
  outside : endpoint.representative ∉ Mc
  strict : commutatorPreimage (endpoint.conjugate D.UH) D.UH D.V₁ < endpoint.conjugate D.UH
  first_actor : actorImage D.H (endpoint.conjugate D.UH) ≤ actorImage D.H H1
  point : endpoint.conjugate D.V₁ ≤ firstSupport a H1
  reverse_point : D.V₁ ≤ endpoint.conjugate (firstSupport a H1)

/-- The literal alternatives to be proved from the original rank-two prefix
and the earlier 14.6.12 setup. This predicate is not a source theorem. -/
def SourceCriticalAlternatives {D : ChapterF.Section09.Setup G}
    (h : D.Hypothesis) [IsElementaryAbelian 2 D.UH]
    (a : LocalQuotientAction D.H D.UH D.V₁) (Mc H1 : Subgroup G) (p : ℕ) : Prop :=
  (p = 3 ∧ ∃ o : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH,
    ∃ c : SourceOrthogonalCriticalPair o Mc, o.plane c.first = firstSupport a H1) ∨
  ((p = 3 ∨ p = 5) ∧ Nonempty (RankEightCriticalPlacement h a Mc H1))

/-- F.9.2(3) identifies the literal modulo-point denominator with the core
intersection. This justifies using either convention in the Sylow argument. -/
theorem critical_denominator_eq {D : ChapterF.Section09.Setup G}
    (h : D.Hypothesis) (A : Subgroup G) (hAH : A ≤ D.H) :
    commutatorPreimage A D.UH D.V₁ = A ⊓ D.QH := by
  apply le_antisymm
  · have hn : A ≤ normalizer (D.V₁ : Set G) :=
      hAH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    have hc := commutator_commutatorPreimage_le A D.UH D.V₁ hn
    rw [commutator_comm] at hc
    intro x hx
    have hxA := commutatorPreimage_le A D.UH D.V₁ hx
    refine ⟨hxA,?_⟩
    rw [← h.kernel_UH_eq_QH]
    exact (h.mem_kernel_iff h.UH_le_H).mpr
      ⟨hAH hxA,fun u hu => hc (commutator_mem_commutator hu hx)⟩
  · apply le_commutatorPreimage inf_le_left
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans h.commutator_UH_QH_le_point

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
