module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.UnitaryGraph
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.Covers
public import Theory.GroupTheory.QuasisimpleGraphQuotientLifting
public import Theory.GroupTheory.MarkedPerfectCoverAction

/-!
# The unitary graph involution through the actual central cover

Quotienting by the component centralizer gives a simple generalized Fitting
subgroup. The projective source theorem supplies an outside graph involution
and a new identity-Gram marking there. The odd center lifts the involution
back to the original group, preserving generation. Scalar-cover recognition
with that new marking recovers SU₃ or PSU₃. Uniqueness through a perfect
central cover then identifies the original component action with the exact
inverse-transpose lift, including the nontrivial cubic-center case.

The odd center is proved from the original quotient by O_{3'}, so it is not
an additional source premise. Source: Aschbacher–Smith F.6.18(11), p.310,
and the cover convention I.1.1–I.1.4, pp.407–408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open QuasisimpleGraphQuotientLifting PerfectCentralCovering
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H] [Field F] [Finite F]

/-- Both the special and projective unitary cases retain the newly constructed
quotient graph marking on the original component. -/
theorem exists_unitary_cover_graph_involution
    (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsQuasisimple (generalizedFitting G))
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hproper : generalizedFitting G ≠ ⊤)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (eK : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ t : G, orderOf t = 2 ∧ t ∉ generalizedFitting G ∧
      generalizedFitting G ⊔ zpowers t = ⊤ ∧
      ∃ J' : HermitianForm 3 F, J'.conj = J.conj ∧ J'.form = 1 ∧
        ((∃ (j : generalizedFitting G ≃* ProjectiveSpecialUnitaryMatrixGroup J')
            (gl : MulAut J'.specialSubgroup),
          (∀ x : J'.specialSubgroup, (gl x).val.val = x.val.inv.transpose) ∧
          (∀ x : J'.specialSubgroup,
            j (MulAut.conjNormal t (j.symm (J'.specialToProjective x))) =
              J'.specialToProjective (gl x))) ∨
         (∃ j : generalizedFitting G ≃* J'.specialSubgroup,
           ∀ x : generalizedFitting G,
             (j (MulAut.conjNormal t x)).val.val = (j x).val.inv.transpose)) := by
  let K := generalizedFitting G
  let : IsQuasisimple K := hK
  have hcomp : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal, hK⟩
  have ho := component_center_odd_of_primeToThree_quotient eG hcomp
  have hq : IsPGroup 2 (G ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K (T : Subgroup G) T.isPGroup' hgen
  let B := CentralizerQuotient K
  let : IsSimpleGroup (generalizedFitting B) := quotient_fitting_simple K hq
  let TB := T.mapSurjective (QuotientGroup.mk'_surjective (centralizer (K : Set G)))
  let eB := (fittingEquiv K hq).symm.trans eK
  obtain ⟨b, hb2, hbout, hbgen, J', jb, gl, hconj, hgram, hgl, hjb⟩ :=
    exists_projective_unitary_graph_involution TB
      (quotient_fitting_sup_sylow K hq T hgen)
      (quotient_fitting_proper K hq rfl hproper) J hp hp8 hcard hc eB
  obtain ⟨t, ht, ht2, htout, htgen⟩ :=
    exists_lift_involution K hq rfl ho b hb2 hbout hbgen
  let eNew := (fittingEquiv K hq).trans jb
  let f : K →* ProjectiveSpecialUnitaryMatrixGroup J' :=
    eNew.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J') :=
    MulAut.congr jb (MulAut.conjNormal b)
  have hf (x : K) : f x = jb (fittingMap K hq x) := rfl
  have hα (x : K) : f (MulAut.conjNormal t x) = γ (f x) := by
    rw [hf, hf, fittingMap_conj, ht]
    change jb (MulAut.conjNormal b (fittingMap K hq x)) =
      jb (MulAut.conjNormal b (jb.symm (jb (fittingMap K hq x))))
    rw [jb.symm_apply_apply]
  have hβ (x : J'.specialSubgroup) :
      J'.specialToProjective (gl x) = γ (J'.specialToProjective x) := (hjb x).symm
  have hc' : ∀ x, J'.conj x = x ^ p := by intro x; rw [hconj, hc]
  refine ⟨t, ht2, htout, htgen, J', hconj, hgram, ?_⟩
  rcases component_unitary_three_cover eG hcomp J' hp (by omega) hcard hc' eNew with
    ⟨_, j, hj⟩ | ⟨_, _, a, ha⟩
  · apply Or.inl
    have hmark (x : K) : j x = f x := DFunLike.congr_fun hj x
    have hja (x : K) : j (MulAut.conjNormal t x) = γ (j x) := by
      rw [hmark, hmark]
      exact hα x
    refine ⟨j, gl, hgl, ?_⟩
    intro x
    rw [hja, j.apply_symm_apply]
    exact (hβ x).symm
  · apply Or.inr
    have he := equiv_symm_intertwines_of_marked_cover J'.specialToProjective
      J'.specialToProjective_ker_le_center f a ha (MulAut.conjNormal t) gl γ hα hβ
    refine ⟨a.symm, ?_⟩
    intro x
    rw [he]
    exact hgl (a.symm x)

end CFSG.Quasithin.ChapterF.SourceAssembly
