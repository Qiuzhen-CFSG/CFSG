module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.Transport
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Relative block exclusion survives a normalized two-group supplement

A chi-zero block is 2-perfect by C.1.7 and C.1.12. When Q is a two-group
normalizing A, its image in (A Q)/A is therefore trivial: every such block
contained in A Q already lies in A. Subnormality then restricts from A Q to A.
Consequently it suffices to exclude relatively subnormal chi-zero blocks in
the intrinsic triality parabolics; adjoining Q creates no new ones.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7 and
C.1.12, printed pp.123–124, applied to the parabolics in E.6.8, p.247.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry

variable {G : Type*} [Group G] {A Q B : Subgroup G}

/-- Two-perfection forces a chi-zero block through a quotient by a two-group.
The normality used here is only inside the join A ∨ Q. -/
theorem chiZeroBlock_le_of_sup (hQ : IsPGroup 2 Q)
    (hN : Q ≤ normalizer (A : Set G)) (hB : B ≤ A ⊔ Q)
    (hb : ChapterC.IsChiZeroBlock B) : B ≤ A := by
  let D := A ⊔ Q
  let _ : (A.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show A ≤ D from le_sup_left)).mpr
      (sup_le A.le_normalizer hN)
  let e := subgroupOfEquivOfLe hB
  have hp : IsPPerfect 2 (B.subgroupOf D) :=
    hb.chi.short.twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective
  have htop : A.subgroupOf D ⊔ Q.subgroupOf D = ⊤ := by
    rw [← subgroupOf_sup (show A ≤ D from le_sup_left) (show Q ≤ D from le_sup_right)]
    exact subgroupOf_self _
  have hle := le_normal_of_isPPerfect_of_le_sup_pGroup
    (B.subgroupOf D) (A.subgroupOf D) (Q.subgroupOf D) hp hQ.comap_subtype
      (htop.symm ▸ le_top)
  intro x hx
  exact hle (show (⟨x, hB hx⟩ : D) ∈ B.subgroupOf D from hx)

/-- Relative subnormality restricts after the block has been placed in A. -/
theorem noChiZeroBlocks_sup (hQ : IsPGroup 2 Q)
    (hN : Q ≤ normalizer (A : Set G)) (hfree : NoChiZeroBlocks A) :
    NoChiZeroBlocks (A ⊔ Q) := by
  intro B hB hs hb
  have hBA := chiZeroBlock_le_of_sup hQ hN hB hb
  exact hfree B hBA (hs.comap (inclusion (show A ≤ A ⊔ Q from le_sup_left))) hb

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
