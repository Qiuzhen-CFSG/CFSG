module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingEnumeration
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# The original maximum elementary family of R

Baum(R) contains the elementary Thompson subgroup, so its maximum elementary
subgroups are exactly those of R. The intrinsic four-family enumeration
therefore transports to the literal subgroups of the original ambient group,
with the two extra transposition images retained in the source marking.

Source: Aschbacher–Smith, C.5.6(5),(7) and C.5.7, printed pp.157–160.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
omit [Finite G] in
private theorem maxFamily_eq_image (S : Subgroup G) :
    elementaryAbelianMaxSubgroups S =
      (fun B : Subgroup S => B.map S.subtype) '' elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by
  ext A
  rw [maxFamily_equiv_iff S (MulEquiv.refl S) A]
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B, hB, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B, hB, rfl⟩

/-- Passing to Baum(R) preserves the complete maximum elementary family. -/
theorem baumann_maxFamily (R : Subgroup G) :
    elementaryAbelianMaxSubgroups (ChapterB.baumann R) = elementaryAbelianMaxSubgroups R := by
  have hJR : elementaryAbelianMaxJ R ≤ ChapterB.baumann R := by
    apply le_inf (sSup_le fun _ hB => hB.1)
    apply le_centralizer_iff.mpr
    intro a ha
    exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp ha).2.2
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty R
  have hAS : A ≤ ChapterB.baumann R := (le_sSup hA).trans hJR
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

open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily

theorem AlternatingPairSetup.family_eq_four
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥) :
    let S := ChapterB.baumann R
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    ∃ B₀ B₁ : Subgroup G,
      elementaryAbelianMaxSubgroups R = {Q, V ⊔ D, B₀, B₁} ∧
      (B₀.subgroupOf (K ⊔ S)).map h.action = line 0 ∧
      (B₁.subgroupOf (K ⊔ S)).map h.action = line 1 := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let Q := (K ⊔ S).pCoreIn 2
  let D := S ⊓ centralizer (K : Set G)
  let σ := h.action.comp (inclusion (show S ≤ K ⊔ S from le_sup_right))
  have hSmap : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hVS : V ≤ S := (map_mono h.module_le).trans_eq hSmap
  have hWS : V ⊔ D ≤ S := sup_le hVS inf_le_left
  have hQS : Q ≤ S := h.core.le.trans inf_le_left
  obtain ⟨B₀, B₁, hfamily, h0, h1⟩ := h.intrinsic_family_eq_four x hx hnc hphi
  refine ⟨B₀.map S.subtype, B₁.map S.subtype, ?_, ?_, ?_⟩
  · rw [← baumann_maxFamily R, maxFamily_eq_image, hfamily]
    simp only [Set.image_insert_eq, Set.image_singleton]
    change {(Q.subgroupOf S).map S.subtype, ((V ⊔ D).subgroupOf S).map S.subtype,
      B₀.map S.subtype, B₁.map S.subtype} = {Q, V ⊔ D, B₀.map S.subtype, B₁.map S.subtype}
    rw [map_subgroupOf_eq_of_le hQS, map_subgroupOf_eq_of_le hWS]
  · have hh : ((B₀.map S.subtype).subgroupOf (K ⊔ S)).map h.action = B₀.map σ := by
      ext p
      constructor
      · rintro ⟨b, ⟨c, hc, hcb⟩, rfl⟩
        refine ⟨c, hc, ?_⟩
        exact congrArg h.action (Subtype.ext hcb)
      · rintro ⟨b, hb, rfl⟩
        exact ⟨inclusion le_sup_right b, ⟨b, hb, rfl⟩, rfl⟩
    exact hh.trans h0
  · have hh : ((B₁.map S.subtype).subgroupOf (K ⊔ S)).map h.action = B₁.map σ := by
      ext p
      constructor
      · rintro ⟨b, ⟨c, hc, hcb⟩, rfl⟩
        refine ⟨c, hc, ?_⟩
        exact congrArg h.action (Subtype.ext hcb)
      · rintro ⟨b, hb, rfl⟩
        exact ⟨inclusion le_sup_right b, ⟨b, hb, rfl⟩, rfl⟩
    exact hh.trans h1
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
