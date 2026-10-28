module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Normalizer

/-!
# The original Sylow maximum family and Thompson subgroup

Baum(R) contains J(R), hence it has the same maximum elementary family as R.
The proved two-core family spans S, so S=J(R). The argument uses the
literal original subgroups and retains every central covering layer.

Source: Aschbacher–Smith C.5.6(7i) and C.5.7, printed pp.158,160.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

private theorem baumann_maxFamily (R : Subgroup G) :
    elementaryAbelianMaxSubgroups (S R) = elementaryAbelianMaxSubgroups R := by
  have hJR : elementaryAbelianMaxJ R ≤ S R := by
    apply le_inf (sSup_le fun _ hB => hB.1)
    apply le_centralizer_iff.mpr
    intro a ha
    exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp ha).2.2
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty R
  have hAS : A ≤ S R := (le_sSup hA).trans hJR
  ext B
  constructor
  · intro hB
    refine ⟨hB.1.trans inf_le_left, hB.2.1, ?_⟩
    intro C hCR hC
    exact (hA.2.2 C hCR hC).trans (hB.2.2 A hAS hA.2.1)
  · intro hB
    refine ⟨(le_sSup hB).trans hJR, hB.2.1, ?_⟩
    intro C hCS hC
    exact hB.2.2 C (hCS.trans inf_le_left) hC

/-- The complete maximum elementary family of the original R has two members. -/
theorem Setup.sylow_maximum_family (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) :
    elementaryAbelianMaxSubgroups R = {Q R L, (Q R L).map (MulAut.conj x⁻¹).toMonoidHom} := by
  rw [← baumann_maxFamily R]
  exact h.maximum_family hx hnc hphi

/-- The source Baumann group is exactly the original elementary Thompson subgroup. -/
theorem Setup.baumann_eq_thompson (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) : S R = elementaryAbelianMaxJ R := by
  unfold elementaryAbelianMaxJ
  rw [h.sylow_maximum_family hx hnc hphi, sSup_pair]
  exact h.core_span hx hnc
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
