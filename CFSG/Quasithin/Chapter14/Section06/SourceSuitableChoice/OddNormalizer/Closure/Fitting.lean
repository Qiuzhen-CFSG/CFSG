module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceSwapped.Detection
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The Fitting containment supplied by intrinsic component detection

An actual Ξ input is either normal in the local overgroup, or lies in
an orbit of detected ordinary components modulo its two-core. In the
normal case its odd quotient is nilpotent; in the component case its
image lies in the layer. Both cases lie in the same generalized-Fitting
preimage, which also contains the whole normal closure.

This uses the checked source component detection and complete Theorems
A and C for the full known-simple catalogue. No group-model list is
assumed. `Closure.Source` applies it to the original O²(H) inside Mc.
Source: Aschbacher--Smith 1.3.4, pp.509--510, and the containment used in
14.6.17, pp.1035--1036.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem fittingPreimage_normalized (H : Subgroup G) :
    H ≤ normalizer (ChapterA.Section04.twoGeneralizedFittingPreimage H : Set G) := by
  exact normal_subgroupOf_iff_le_normalizer (map_subtype_le _) |>.mp (by
    change (((generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H))).map H.subtype).subgroupOf H |>.Normal
    rw [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance)

omit [Finite G] in
private theorem le_fittingPreimage_of_image {H X : Subgroup G} (hX : X ≤ H)
    (hi : quotientImage H X ≤ generalizedFitting (H ⧸ pCore 2 H)) :
    X ≤ ChapterA.Section04.twoGeneralizedFittingPreimage H := by
  rw [← map_subgroupOf_eq_of_le hX]
  exact map_mono (map_le_iff_le_comap.mp hi)

private theorem componentOrbit_le_fittingPreimage {H L T : Subgroup G}
    (hL : L ≤ H) (hT : T ≤ H)
    (hc : IsComponent (XiQuotient H) (quotientImage H L)) :
    componentOrbit L T ≤ ChapterA.Section04.twoGeneralizedFittingPreimage H := by
  apply iSup_conjugates_le_of_le_normalizer
  · exact le_fittingPreimage_of_image hL (component_le_generalizedFitting _ _ hc)
  · exact hT.trans (fittingPreimage_normalized H)

/-- The Fitting-containment part of the intrinsic embedding argument does not
need the later list of component models. -/
theorem localInput_le_fittingPreimage {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hT : IsSylowIn 2 T H) :
    X ≤ ChapterA.Section04.twoGeneralizedFittingPreimage H := by
  let hA := fun (Y : Type u) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type u) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  rcases h.normal_or_detected_containment hA hC hsq hT with
    hn | ⟨L,hL,_hn,_hcomm,_hP,hX⟩
  · let := hn
    let q := QuotientGroup.mk' (pCore 2 H)
    have hXH : X ≤ H := le_sup_left.trans h.overgroup
    have hn' : H ≤ normalizer (X : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hXH).mp hn
    have hcore : X.pCoreIn 2 ≤ H.pCoreIn 2 :=
      pCoreIn_mono_of_normalizes hXH hn'
    have hcoreq : quotientImage H (X.pCoreIn 2) = ⊥ := by
      apply eq_bot_iff.mpr
      rintro _ ⟨x,hx,rfl⟩
      exact (QuotientGroup.eq_one_iff x).mpr (by
        obtain ⟨y,hy,he⟩ := hcore hx
        exact (show y = x from Subtype.ext he) ▸ hy)
    have he : quotientImage H X = quotientImage H P := by
      have hi : (X.pCoreIn 2).subgroupOf H ⊔ P.subgroupOf H = X.subgroupOf H := by
        apply map_injective H.subtype_injective
        rw [Subgroup.map_sup,map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hXH),
          map_subgroupOf_eq_of_le h.complement_le_overgroup,map_subgroupOf_eq_of_le hXH]
        exact h.complement
      unfold quotientImage
      rw [← hi,Subgroup.map_sup]
      change quotientImage H (X.pCoreIn 2) ⊔ quotientImage H P = _
      rw [hcoreq,bot_sup_eq]
      rfl
    let : Fact p.Prime := ⟨h.prime⟩
    have hp : IsPGroup p (quotientImage H X) := by
      rw [he]
      exact h.quotient_odd_complement.isPGroup
    let : Group.IsNilpotent (quotientImage H X) := hp.isNilpotent
    let : (quotientImage H X).Normal := by
      unfold quotientImage
      exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    have hf : quotientImage H X ≤ fittingSubgroup (XiQuotient H) :=
      le_sSup ⟨inferInstance,inferInstance⟩
    exact le_fittingPreimage_of_image hXH (hf.trans le_sup_left)
  · exact hX.trans (componentOrbit_le_fittingPreimage hL.mem.1
      (le_sup_right.trans h.overgroup) hL.component)

/-- Normality of the Fitting preimage also contains the entire closure. -/
theorem localInput_closure_le_fittingPreimage {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hT : IsSylowIn 2 T H) :
    conjugateSpanBy X H ≤ ChapterA.Section04.twoGeneralizedFittingPreimage H :=
  conjugateSpanBy_le (localInput_le_fittingPreimage h hsq hT) (fittingPreimage_normalized H)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
