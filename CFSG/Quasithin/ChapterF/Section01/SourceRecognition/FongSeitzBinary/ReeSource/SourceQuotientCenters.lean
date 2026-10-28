module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalStructure

/-!
# Full centers on the original source quotient

The natural markings of the original faithful panels construct genuine
(6H) data and identify the images of Z(S) and Z(O₂(P₂)) under literally Q.q
with the perpendicular Omega subgroup. Their embedded centers agree before
quotienting. Local characteristic two then identifies C_S(O₂(P₂)) with this
common center. The ambient group need not be finite, and the Suzuki marking
includes m=0 and q=2.

Source: Fong--Seitz I (1973), (6H)(g), p.55, applied to the original
Aschbacher--Smith F.1.1 configuration. Only the preceding octagonal family
selection and odd-degree premise remain explicit.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Characteristic two identifies the centralizer inside the original Sylow
subgroup with the embedded center of the original parabolic two-core. -/
private theorem sylow_core_centralizer (h : HypothesisF11 L S) (i : Fin 2) :
    S ⊓ centralizer ((parabolic L S i).pCoreIn 2 : Set G) =
      (center (pCore 2 (parabolic L S i))).map
        ((parabolic L S i).subtype.comp (pCore 2 (parabolic L S i)).subtype) := by
  let P := parabolic L S i
  let K := pCore 2 P
  have hSP : S ≤ P := le_sup_right.trans le_sup_left
  have hKS : P.pCoreIn 2 ≤ S := h.parabolic_core_le_S i
  let := h.finite_parabolic i
  have hc : centralizer (K : Set P) ≤ K :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two i)
  apply le_antisymm
  · rintro x ⟨hxS,hxc⟩
    let xp : P := ⟨x,hSP hxS⟩
    have hxp : xp ∈ centralizer (K : Set P) := by
      intro k hk
      exact Subtype.ext (hxc k (mem_map_of_mem P.subtype hk))
    let xk : K := ⟨xp,hc hxp⟩
    refine ⟨xk,mem_center_iff.mpr ?_,rfl⟩
    intro k
    apply Subtype.ext
    exact hxp k k.property
  · rintro x ⟨z,hz,rfl⟩
    refine ⟨hKS (mem_map_of_mem P.subtype z.property),?_⟩
    intro k hk
    obtain ⟨a,ha,rfl⟩ := hk
    exact congrArg (fun a : K => ((a : P) : G)) (mem_center_iff.mp hz ⟨a,ha⟩)

variable (Q : SourceQuotient L S)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include h hm hn μ₀ T hB₀ μ₁ hB₁ in
/-- The actual second two-core center has the perpendicular Omega image under
Q.q, from the original natural panel markings. -/
theorem quotient_source_radical_center_image :
    (center (pCore 2 (parabolic L S 1))).map
      ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
        (pCore 2 (parabolic L S 1)).subtype) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  let d := quotientSourceReeSixHData Q h split hm n hn m μ₀ T hB₀ μ₁ hB₁
  exact original_source_radical_center_image_quotient Q split n hn m
    d.linear d.linearSylow d.linearBorel d.suzuki d.suzukiBorel h hm

include h hm hn μ₀ T hB₀ μ₁ hB₁ in
/-- The same literal quotient carries the original Sylow center onto Omega. -/
theorem quotient_source_sylow_center_image :
    (center S).map (Q.q.comp (inclusion
      ((show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left).trans
        (parabolic_le_generated 1)))) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  let d := quotientSourceReeSixHData Q h split hm n hn m μ₀ T hB₀ μ₁ hB₁
  exact original_source_sylow_center_image_quotient Q split n hn m
    d.linear d.linearSylow d.linearBorel d.suzuki d.suzukiBorel h hm

include Q h split hm hn μ₀ T hB₀ μ₁ hB₁ in
/-- Equality of the original embedded centers, before passing to Q.q. -/
theorem quotient_source_sylow_center_eq_radical_center :
    (center S).map S.subtype =
      (center (pCore 2 (parabolic L S 1))).map
        ((parabolic L S 1).subtype.comp (pCore 2 (parabolic L S 1)).subtype) := by
  let d := quotientSourceReeSixHData Q h split hm n hn m μ₀ T hB₀ μ₁ hB₁
  exact original_source_sylow_center_eq_radical_center Q (originalMarkedIso Q)
    split n hn m d.linear d.linearSylow d.linearBorel d.suzuki d.suzukiBorel h hm

include Q h split hm hn μ₀ T hB₀ μ₁ hB₁ in
/-- The actual original centralizer C_S(O₂(P₂)) is Z(S). -/
theorem quotient_source_sylow_centralizer_radical_eq_center :
    S ⊓ centralizer ((parabolic L S 1).pCoreIn 2 : Set G) =
      (center S).map S.subtype := by
  exact (sylow_core_centralizer h 1).trans
    (quotient_source_sylow_center_eq_radical_center Q h split hm n hn m μ₀ T hB₀ μ₁ hB₁).symm

include Q h split hm hn μ₀ T hB₀ μ₁ hB₁ in
/-- The source centralizer is also the same embedded radical center. -/
theorem quotient_source_sylow_centralizer_radical_eq_radical_center :
    S ⊓ centralizer ((parabolic L S 1).pCoreIn 2 : Set G) =
      (center (pCore 2 (parabolic L S 1))).map
        ((parabolic L S 1).subtype.comp (pCore 2 (parabolic L S 1)).subtype) := by
  exact (quotient_source_sylow_centralizer_radical_eq_center Q h split hm n hn m μ₀ T hB₀ μ₁ hB₁).trans
    (quotient_source_sylow_center_eq_radical_center Q h split hm n hn m μ₀ T hB₀ μ₁ hB₁)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
