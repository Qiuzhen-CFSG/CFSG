module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualGraph
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Representation

/-!
# The original diagram actor on a faithful residual image

An actual equivalence from K/O₂(K) to the image of K transports the
original Sylow diagram actor. The representative equation identifies
its implementing element with the literal projected Sylow element.
Both conjugation identities are retained, including the original field
and its geometric parabolic classes.

The Chapter 12 application constructs this equivalence for the faithful
centralizer-span action and excludes the Hermitian row using the resulting
actor. This is the diagram step in Aschbacher--Smith 5.1.23, printed p.646
of `refs/quasithin.pdf`; it does not select an irreducible constituent.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree.OuterExtensions
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape

variable {G X : Type*} [Group G] [Group X]

/-- Transport the actual residual quotient and its diagram actor into the action image. -/
theorem graph_action_on_quotient_image
    (S K J : Subgroup G) (hKJ : K ≤ J) (hSJ : S ≤ J)
    (hg : HasLinearFourGraphAction S K) (f : J →* X)
    (e : (K ⧸ pCore 2 K) ≃* (K.subgroupOf J).map f)
    (he : ∀ k : K, (e (QuotientGroup.mk' (pCore 2 K) k) : X) =
      f (inclusion hKJ k)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      ∃ j : (K.subgroupOf J).map f ≃* PSL(3,F),
        ∃ t : S, ∃ a : MulAut ((K.subgroupOf J).map f), ∃ b : MulAut PSL(3,F),
          (∀ k, (a k : X) = f (inclusion hSJ t) * k * (f (inclusion hSJ t))⁻¹) ∧
          (∀ k, j (a k) = b (j k)) ∧ b ∉ diagramTrivial F := by
  obtain ⟨F,hF,hfin,hcard,j,t,ht,a,b,ha,hb,hd⟩ := hg
  let aq := quotientAut (pCore 2 K) a
  let a' := MulAut.congr e aq
  refine ⟨F,hF,hfin,hcard,e.symm.trans j,⟨t,ht⟩,a',b,?_,?_,hd⟩
  · intro k
    obtain ⟨x,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K)) k
    change (e (aq (e.symm (e (QuotientGroup.mk' _ x)))) : X) = _
    rw [e.symm_apply_apply]
    rw [show aq (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (a x) from
      quotientAut_apply_mk (pCore 2 K) a x]
    simp only [Function.comp_apply,he]
    have hx : inclusion hKJ (a x) = inclusion hSJ ⟨t,ht⟩ * inclusion hKJ x *
        (inclusion hSJ ⟨t,ht⟩)⁻¹ :=
      Subtype.ext (ha x)
    rw [hx,map_mul,map_mul,map_inv]
  · intro k
    obtain ⟨x,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K)) k
    change j (e.symm (e (aq (e.symm (e (QuotientGroup.mk' _ x)))))) =
      b (j (e.symm (e (QuotientGroup.mk' _ x))))
    simp only [e.symm_apply_apply]
    simpa only [aq, quotientAut_apply_mk] using hb x

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
