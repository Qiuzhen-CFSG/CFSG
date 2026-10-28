module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalQuotient
public import Theory.GroupTheory.SylowKernelQuotient
public import Theory.GroupTheory.PerfectQuotientGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SelectedGroup
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannNormalizer

/-!
# Natural seven-letter cubic generation with the original Baumann normalizer

The kernel Sylow is O₂(G); the remaining odd kernel lies in the normal
quasisimple component and is central there. Relative Frattini lifts the
normalizer of the three-pair eight-group to the actual two-subgroup.
Together with the selected cubic, its permutation image generates S₇.
Perfectness of the component quotient removes the full central kernel,
including its possible central three-part.

Source: Aschbacher–Smith C.1.24(a), printed pp.130–131. The selected
preimage and all quotient maps are the literal source constructions.
-/

public section
open Subgroup Theory.GroupTheory Equiv
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource.Natural
open SymmetricSix
open Theory.SpecificGroups.SymmetricSeven.ThreePairsCubic
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The actual residual action kernel is central in the original component
image modulo the two-core; it need not be a two-group. -/
theorem kernel_image_le_center_component (L T : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 7))
    (hT : IsPGroup 2 T) (hgen : L ⊔ T = ⊤)
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G) :
    q.ker.map (QuotientGroup.mk' (pCore 2 G)) ≤
      (center (L.map (QuotientGroup.mk' (pCore 2 G)))).map
        (L.map (QuotientGroup.mk' (pCore 2 G))).subtype := by
  let π := QuotientGroup.mk' (pCore 2 G)
  let qb := QuotientGroup.lift (pCore 2 G) q hQ
  let B := L.map π
  let eB : (L ⧸ pCore 2 L) ≃* B := (inferInstance : L.Normal).isSubnormal.quotientCoreImageEquiv 2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB
  have hBq : B.map qb = alternatingGroup (Fin 7) := by
    rw [map_map]
    exact hLq
  let f : B →* alternatingGroup (Fin 7) := (qb.comp B.subtype).codRestrict _
    (fun x => hBq ▸ mem_map_of_mem qb x.property)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : Sym) ∈ B.map qb := by rw [hBq]; exact y.property
    obtain ⟨x,hx,he⟩ := hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 7))
  let cover : Covering B (alternatingGroup (Fin 7)) := ⟨f,hf⟩
  have hk : f.ker = center B := cover.ker_eq_center_of_isSimple
  have hker := kernel_le_normal_sup_of_kernel_sylow q (pCore 2 G) L T P hP hT hgen
  have hDB : q.ker.map π ≤ B := by
    have hh := map_mono (f := π) hker
    have hQπ : (pCore 2 G).map π = ⊥ := (Subgroup.map_eq_bot_iff _).mpr
      (by rw [QuotientGroup.ker_mk'])
    rw [Subgroup.map_sup,hQπ,sup_bot_eq] at hh
    exact hh
  intro x hx
  refine ⟨⟨x,hDB hx⟩,?_,rfl⟩
  rw [←hk]
  apply Subtype.ext
  change qb x = 1
  obtain ⟨k,hk,he⟩ := hx
  rw [←he]
  exact hk

/-- A subgroup containing the original two-core and the full S₇ image
already equals G, using the genuine perfect component quotient. -/
theorem eq_top_of_full_symmetric_image (L T : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 7))
    (hT : IsPGroup 2 T) (hgen : L ⊔ T = ⊤)
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G)
    (K : Subgroup G) (hQK : pCore 2 G ≤ K) (hK : K.map q = ⊤) : K = ⊤ := by
  let B := L.map (QuotientGroup.mk' (pCore 2 G))
  let eB : (L ⧸ pCore 2 L) ≃* B := (inferInstance : L.Normal).isSubnormal.quotientCoreImageEquiv 2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB
  exact eq_top_of_perfect_quotient_image (pCore 2 G) q K hQK B
    (kernel_image_le_center_component L T q hQ hLq hT hgen P hP) hK

/-- The literal residual of the selected cubic preimage generates G with
the original Baumann normalizer. No external conjugator is assumed. -/
theorem selected_normalizer_generate (L R T : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym) (hq : Function.Surjective q)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 7))
    (hT : IsPGroup 2 T) (hgen : L ⊔ T = ⊤)
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G)
    (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R) (hRker : R ⊓ q.ker = pCore 2 G)
    (hR : R.map q = pairElementary)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M = 3)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)))
    (hMc : M.map (QuotientGroup.lift (pCore 2 G) q hQ) = zpowers cubic) :
    (pResidual 2 (selectedGroup R M)).map (selectedGroup R M).subtype ⊔
      normalizer (ChapterB.baumann R : Set G) = ⊤ := by
  let Y := (pResidual 2 (selectedGroup R M)).map (selectedGroup R M).subtype
  let K := Y ⊔ normalizer (ChapterB.baumann R : Set G)
  have hRN : normalizer (R : Set G) ≤ normalizer (ChapterB.baumann R : Set G) :=
    Stellmacher.normalizer_le_normalizer_baumann R
  have hQK : pCore 2 G ≤ K := hQR.trans (R.le_normalizer.trans (hRN.trans le_sup_right))
  have hN := normalizer_map_eq_of_kernel_intersection R hpR q hq P (hP.trans hRker.symm)
  rw [hR] at hN
  let π := QuotientGroup.mk' (pCore 2 G)
  let qb := QuotientGroup.lift (pCore 2 G) q hQ
  have he : qb.comp π = q := by ext x; rfl
  have hYq : Y.map q = zpowers cubic := by
    rw [←he,←map_map]
    rw [selected_residual_image R hpR M hM hn]
    exact hMc
  have hKq : K.map q = ⊤ := by
    apply top_unique
    rw [←normalizer_cubic_generate]
    apply sup_le
    · rw [←hN]
      exact map_mono (hRN.trans le_sup_right)
    · rw [←hYq]
      exact map_mono le_sup_left
  exact eq_top_of_full_symmetric_image L T q hQ hLq hT hgen P hP K hQK hKq

/-- Adding Baum(R) to the same residual does not change the generation
conclusion; this is the literal Hseed in C.1.24(a). -/
theorem selected_seed_normalizer_generate (L R T : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym) (hq : Function.Surjective q)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 7))
    (hT : IsPGroup 2 T) (hgen : L ⊔ T = ⊤)
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G)
    (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R) (hRker : R ⊓ q.ker = pCore 2 G)
    (hR : R.map q = pairElementary)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M = 3)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)))
    (hMc : M.map (QuotientGroup.lift (pCore 2 G) q hQ) = zpowers cubic) :
    ((pResidual 2 (selectedGroup R M)).map (selectedGroup R M).subtype ⊔ ChapterB.baumann R) ⊔
      normalizer (ChapterB.baumann R : Set G) = ⊤ := by
  rw [sup_assoc,sup_of_le_right (ChapterB.baumann R).le_normalizer]
  exact selected_normalizer_generate L R T q hq hQ hLq hT hgen P hP hpR hQR hRker
    hR M hM hn hMc

end CFSG.Quasithin.ChapterC.RankOne.SevenSource.Natural
