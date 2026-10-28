module

public import CFSG.Quasithin.Chapter13.Section05.LocalSteps
public import CFSG.Quasithin.Chapter13.Section05.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreRestriction

/-!
# Nonnormality and normalizer cores in the Section 13.5 counterexample

The failure of the actual matrix-model conclusion, together with the earlier
normal-L₁ recognitions, gives 13.5.18. For 13.5.19, T-invariance of Y and
O₂(H) ≤ T allow the residual normalizer theorem to apply to the actual map
H → H/O₂(H). In the triple-cover branch Y is the literal O²(O₂,Z(L)).

In the ordinary branch, a normalizer outside M lies in H_z: its two-core
contains the nontrivial point V₁. If its V₃-closure were abelian, F.9.4(2)
and the earlier seed-centralizer bound would put V in its two-core. Otherwise
13.5.18 contradicts its relative normality of L₁. This proves 13.5.19(2)
without a further Baer–Suzuki specialization.

These deductions retain explicit earlier inputs: universal 13.5.7 and
13.5.16–17, the normalizer bound of 13.5.5, the seed-centralizer bound from
13.5.4(4) (or the A₅ natural action), and V ≤ O₂(M). Their source construction
belongs to the local-geometry and normal-recognition owners. No component or
module alternative is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.18–19, printed p.922 (PDF p.939).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction
open Section08.Source
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- 13.5.19(1): the normalizer image under the actual star map. -/
theorem normalizer_starImage_eq (H Y : Subgroup G)
    (hYH : Y ≤ H) (hp : IsPPerfect 2 Y)
    (hn : H.pCoreIn 2 ≤ normalizer (Y : Set G)) :
    starImage H (H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage H Y : Set (Hstar H)) := by
  let q : H →* Hstar H := QuotientGroup.mk' (pCore 2 H)
  have hp' : IsPPerfect 2 (Y.subgroupOf H) := hp.of_surjective
    (subgroupOfEquivOfLe hYH).symm.toMonoidHom (subgroupOfEquivOfLe hYH).symm.surjective
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hn' : q.ker ≤ normalizer (Y.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hYH]
    intro x hx
    exact hn (mem_map.mpr ⟨x, (QuotientGroup.ker_mk' (pCore 2 H)) ▸ hx, rfl⟩)
  have he := map_normalizer_of_pPerfect q (QuotientGroup.mk'_surjective _)
    (Y.subgroupOf H) hp' hk hn'
  simpa only [starImage, inf_subgroupOf_left, subgroupOf_normalizer_eq hYH] using he

/-- The point residual is T-invariant; thus the kernel O₂(H) normalizes it. -/
theorem local_residual_normalized
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) :
    (D.T : Subgroup G) ≤ normalizer (D.L₁ : Set G) := by
  have hz : (D.T : Subgroup G) ≤ normalizer (D.Gz : Set G) :=
    h.normalizes_point.trans (normalizer_le_normalizer_centralizer _)
  exact ((le_inf h.normalizes_L hz).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image (D.L ⊓ D.Gz) (pResidual 2 (D.L ⊓ D.Gz : Subgroup G)))

/-- Specialization of 13.5.19(1) to Y = L₁. -/
theorem local_normalizer_image
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) :
    starImage D.H (D.H ⊓ normalizer (D.L₁ : Set G)) =
      normalizer (starImage D.H D.L₁ : Set (Hstar D.H)) :=
  normalizer_starImage_eq D.H D.L₁ (le_sup_left.trans h.local_le)
    (isPPerfect_embedded_pResidual 2 _) (h.QH_le_T.trans (local_residual_normalized D h))

/-- The point V₁ supplies the nontrivial two-core needed for N_H(L₁) ∈ H_z. -/
theorem local_normalizer_mem_Hz
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) (M : Subgroup G)
    (hout : ¬ D.H ⊓ normalizer (D.L₁ : Set G) ≤ M) :
    D.H ⊓ normalizer (D.L₁ : Set G) ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M := by
  let J := D.H ⊓ normalizer (D.L₁ : Set G)
  have hlocal : D.L₁ ⊔ (D.T : Subgroup G) ≤ J :=
    le_inf h.local_le (sup_le D.L₁.le_normalizer (local_residual_normalized D h))
  have hpJ : D.V₁ ≤ J := h.point_lt.le.trans (h.plus_le.trans (h.V_le_T.trans
    (le_sup_right.trans hlocal)))
  have hpCore : D.V₁ ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((show IsPGroup 2 D.V from h.elementary.isPGroup).to_le (h.point_lt.le.trans h.plus_le))
    hpJ ((inf_le_left.trans h.H_centralizes).trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨⟨?_, hlocal⟩, ?_, hout⟩
  · change J.pCoreIn 2 ≠ ⊥
    intro he
    have heq : D.V₁ = ⊥ := bot_unique (hpCore.trans_eq he)
    have hc := h.point_card
    simp [heq] at hc
  · exact (inf_le_left.trans h.H_centralizes).trans (Subgroup.centralizer_le_normalizer _)


/-- 13.5.19(2) in the ordinary branch: F.9.4(2) makes a failure of core
containment contradict the nonnormality conclusion of 13.5.18. -/
theorem local_normalizer_core
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) (M : Subgroup G)
    (hVM : D.V ≤ M.pCoreIn 2)
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hcentral : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (hF : ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ({D with H := J} : ChapterF.Section09.Setup G).Hypothesis)
    (hnormal : ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ¬ IsMulCommutative (UH J D.Vplus) → ¬ (D.L₁.subgroupOf J).Normal) :
    D.V ≤ (D.H ⊓ normalizer (D.L₁ : Set G)).pCoreIn 2 := by
  let J := D.H ⊓ normalizer (D.L₁ : Set G)
  have hVJ : D.V ≤ J := le_inf h.V_le_H
    (h.V_le_T.trans (local_residual_normalized D h))
  by_contra hnot
  have hout : ¬ J ≤ M := fun hJM => hnot
    ((le_inf hVJ hVM).trans (inf_pCoreIn_le_of_le 2 hJM))
  have hJ := local_normalizer_mem_Hz D h M hout
  have h' := hF J hJ
  have hc : ⁅D.V, (J ⊓ centralizer (D.Vplus : Set G)) ⊓
      (J ⊓ normalizer (D.V : Set G))⁆ ≤ D.V₁ := by
    apply (commutator_mono le_rfl ?_).trans hcentral
    intro x hx
    exact ⟨hbound ⟨(Subgroup.centralizer_le_normalizer _)
      (h.H_centralizes hx.1.1.1), (Subgroup.centralizer_le_normalizer _) hx.1.2⟩, hx.1.2⟩
  have hnab : ¬ IsMulCommutative (UH J D.Vplus) := by
    intro hab
    let : IsMulCommutative ({D with H := J} : ChapterF.Section09.Setup G).UH := hab
    exact hnot (h'.V_le_QH_of_UH_abelian hc)
  exact hnormal J hJ hnab (normal_subgroupOf_of_le_normalizer inf_le_right)

omit [Finite G] in
/-- The 13.5.18 deduction from the universal earlier recognitions 13.5.16–17.
The degree-six case uses the actual ordinary A₆ quotient. -/
theorem not_normal_of_source_recognition
    (D : ChapterF.Section09.Setup G) (M : Subgroup G) (n : ℕ)
    (hcase : n = 5 ∨ (n = 6 ∧ Nonempty ((D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))))
    (hnot : ¬ ModelConclusion G n)
    (h16 : Nonempty ((D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) →
      ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
        ¬ IsMulCommutative (UH J D.Vplus) → (D.L₁.subgroupOf J).Normal →
          ClassicalGroup.IsPSU G 4 3)
    (h17 : n = 5 → ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ¬ IsMulCommutative (UH J D.Vplus) → (D.L₁.subgroupOf J).Normal →
        ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3) :
    ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ¬ IsMulCommutative (UH J D.Vplus) → ¬ (D.L₁.subgroupOf J).Normal := by
  intro J hJ hu hn
  apply hnot
  rcases hcase with h5 | ⟨h6, he⟩
  · exact Or.inl ⟨h5, h17 h5 J hJ hu hn⟩
  · exact Or.inr ⟨h6, h16 he J hJ hu hn⟩

open Section08.ComponentSieve.FieldComponents.SmallCovers
/-- Both clauses of 13.5.19 for the literal L₀ = O²(O₂,Z(L)).
The bound N_G(L₀) ≤ M is the earlier 13.2.2(9) input. -/
theorem covered_normalizer
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) (M : Subgroup G)
    (hYH : coverResidualIn D.L ≤ D.H)
    (hVM : D.V ≤ M.pCoreIn 2)
    (hbound : normalizer (coverResidualIn D.L : Set G) ≤ M) :
    starImage D.H (D.H ⊓ normalizer (coverResidualIn D.L : Set G)) =
      normalizer (starImage D.H (coverResidualIn D.L) : Set (Hstar D.H)) ∧
    D.V ≤ (D.H ⊓ normalizer (coverResidualIn D.L : Set G)).pCoreIn 2 := by
  have hTY : (D.T : Subgroup G) ≤ normalizer (coverResidualIn D.L : Set G) :=
    h.normalizes_L.trans (normalizer_le_normalizer_characteristic_image D.L (coverResidual D.L))
  have hp : IsPPerfect 2 (coverResidualIn D.L) := by
    have hi : IsPPerfect 2 (coverResidual D.L) := isPPerfect_embedded_pResidual 2 _
    let e := (coverResidual D.L).equivMapOfInjective D.L.subtype D.L.subtype_injective
    exact hi.of_surjective e.toMonoidHom e.surjective
  exact ⟨normalizer_starImage_eq D.H _ hYH hp (h.QH_le_T.trans hTY),
    (le_inf (le_inf h.V_le_H (h.V_le_T.trans hTY)) hVM).trans
      (inf_pCoreIn_le_of_le 2 (inf_le_right.trans hbound))⟩


/-- Ordinary A₅/A₆ branch of 13.5.18–19. The only recognition inputs are
13.5.16 and 13.5.17, stated on every actual member of H_z. -/
theorem ordinary_counterexample_normalizers
    (D : ChapterF.Section09.Setup G) (M : Subgroup G) (n : ℕ)
    (hH : D.H ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M)
    (hcase : n = 5 ∨ (n = 6 ∧ Nonempty ((D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))))
    (hnot : ¬ ModelConclusion G n)
    (h16 : Nonempty ((D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) →
      ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
        ¬ IsMulCommutative (UH J D.Vplus) → (D.L₁.subgroupOf J).Normal →
          ClassicalGroup.IsPSU G 4 3)
    (h17 : n = 5 → ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ¬ IsMulCommutative (UH J D.Vplus) → (D.L₁.subgroupOf J).Normal →
        ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
    (hF : ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ({D with H := J} : ChapterF.Section09.Setup G).Hypothesis)
    (hVM : D.V ≤ M.pCoreIn 2)
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hcentral : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁) :
    (∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ¬ IsMulCommutative (UH J D.Vplus) → ¬ (D.L₁.subgroupOf J).Normal) ∧
    starImage D.H (D.H ⊓ normalizer (D.L₁ : Set G)) =
      normalizer (starImage D.H D.L₁ : Set (Hstar D.H)) ∧
    D.V ≤ (D.H ⊓ normalizer (D.L₁ : Set G)).pCoreIn 2 := by
  have h : D.Hypothesis := hF D.H hH
  have hn := not_normal_of_source_recognition D M n hcase hnot h16 h17
  exact ⟨hn, local_normalizer_image D h,
    local_normalizer_core D h M hVM hbound hcentral hF hn⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction
end
