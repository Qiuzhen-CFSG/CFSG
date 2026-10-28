module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Multiplicity

/-!
# Source assembly of the marked geometry and natural quotient in 14.7.73

For the original k outside L₁T, the Steinberg commutator calculation places
S = ⟨Uᴸ⟩ in K. The original V/V₁ coordinates identify the Sylow image of S
with a field-line root group, and its conjugate by the same k generates
SL₂(4). Lifting gives K = ⟨S,Sᵏ⟩ and the ordered product P = O₂(K).

On the literal P/E, E = S ∩ Sᵏ, the two root spaces are complementary.
Their marked orbit constructs every projective recognition condition. Apply
the universal G.1.3 implication to this action, then use the genuine 71 dual
coordinates and centralizer bound to prove multiplicity one and E = C_P(U).
The resulting natural section uses the original qK throughout. The final
application discharges every marked-image, generation and natural-section
premise of `RootRecognition.source_quotient_outputs`.

The explicit preceding inputs are the earlier normalizers/starred Sylow
statement, 71's two-core image and dual coordinates/centralizer bound, and
72's core, center, Frattini, Steinberg and U₀ = V₁ conclusions. Their source
producers remain with qt-14-07-endgame-chief-factors and
qt-14-07-endgame-steinberg; universal G.1.3 remains with qt-g-01. These are
conditional source-branch theorems. The parabolic equalities, index and
fixed-kernel count, and final 14.7.73 assembly remain with
qt-14-07-endgame-roots.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.71–73, printed pp.1075–1077 (PDF pp.1092–1094).
-/

public noncomputable section
open Subgroup Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Source
open Chapter12.Section08 CriticalFusion.Source
open ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (earlier : Images.Earlier d) (k : K F)
  (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G))
  (hS : S L F = L.pCoreIn 2)
  (hcenter : (center (S L F)).map (S L F).subtype = V)
  (hPhi : (frattini (S L F)).map (S L F).subtype = V)
  (hpoint : d.U₀ = F.Vi 1)
  (himage : Images.TwoCoreImage (L := L) (F := F))
  (dual : ChiefFactors.QKDualCoordinates d)
  (hcentralizer : ⁅K F, ChiefFactors.C F⁆ ≤ F.U)
  (steinberg : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
  (recognition : NaturalRecognition.{u})

include d earlier k hk hS hcenter hPhi hpoint himage dual hcentralizer steinberg recognition

/-- The original marked images, canonical P/E action, complementary root
spaces and all G.1.3 conditions, with exactly one natural summand. Every
marked-image and multiplicity premise is discharged from the earlier inputs. -/
theorem projective_one_copy :
    ∃ m : MarkedImages d k,
    let := intersection_normal d k hS hPhi earlier.sylow_normalizes m
    let := quotient_elementary d k hS hPhi earlier.sylow_normalizes m
    ∃ (σ : Representation (ZMod 2) SL2FourNatural.SL
        (Additive ((K F).pCoreIn 2 ⧸ (E L F k).subgroupOf ((K F).pCoreIn 2))))
      (c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
        (σ.comp (qK d)))
      (φ : Point SL2FourNatural.F → Submodule (ZMod 2)
        (Additive ((K F).pCoreIn 2 ⧸ (E L F k).subgroupOf ((K F).pCoreIn 2)))),
      (∀ p : (K F).pCoreIn 2, (c.coordinates p).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((E L F k).subgroupOf ((K F).pCoreIn 2)) p)) ∧
      IsCompl (c.imageSpace (S L F ⊓ (K F).pCoreIn 2))
        (c.imageSpace ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2)) ∧
      Criterion σ φ ∧
      φ m.point = c.imageSpace (S L F ⊓ (K F).pCoreIn 2) ∧
      φ (translate (qK d k⁻¹) m.point) =
        c.imageSpace ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) ∧
      NaturalCopies σ 1 ∧
      E L F k = (K F).pCoreIn 2 ⊓ centralizer (F.U : Set G) := by
  obtain ⟨m⟩ := Images.markedImages d earlier k hk hS hcenter hpoint himage steinberg
  refine ⟨m, ?_⟩
  let := intersection_normal d k hS hPhi earlier.sylow_normalizes m
  let := quotient_elementary d k hS hPhi earlier.sylow_normalizes m
  obtain ⟨σ, c, φ, hc, hcriterion, hfirst, hsecond⟩ :=
    exists_projective_quotient d k hS hPhi earlier.sylow_normalizes m
  obtain ⟨r, hr⟩ := recognition _ σ φ hcriterion
  have hr1 := Multiplicity.multiplicity_eq_one d k hS hPhi earlier.sylow_normalizes m
    dual hcentralizer hpoint steinberg σ c hr
  have hone : NaturalCopies σ 1 := hr1 ▸ hr
  obtain ⟨hprod, hinter⟩ := core_factors d k hS hPhi earlier.sylow_normalizes m
  exact ⟨σ, c, φ, hc, c.isCompl_imageSpace _ _ hprod hinter, hcriterion, hfirst,
    hsecond, hone, Multiplicity.intersection_eq_centralizer d k hS hPhi
      earlier.sylow_normalizes m dual hcentralizer σ c hone⟩

/-- The source quotient application, retaining the original qK and k.
Generation, the actual marked Sylow image and the natural P/E section
are constructed here. Both the P₀ identity and the literal ordered product
use O₂(K); no identification with the larger O₂(H) is made. -/
theorem quotient_outputs :
    Nonempty (BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d))) ∧
    E L F k = (K F).pCoreIn 2 ⊓ centralizer (F.U : Set G) ∧
    K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹) ∧
    P₀ L F k = (K F).pCoreIn 2 ∧
    ((K F).pCoreIn 2 : Set G) =
      ((S L F ⊓ (K F).pCoreIn 2 : Subgroup G) : Set G) *
      (((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2 : Subgroup G) : Set G) ∧
    letI : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
    IsElementaryAbelian 2 ((K F).pCoreIn 2 ⧸ F.U.subgroupOf ((K F).pCoreIn 2)) ∧
      ⁅(K F).pCoreIn 2, K F⁆ ⊔ F.U = (K F).pCoreIn 2 ∧
      (K F).pCoreIn 2 = (S L F ⊓ (K F).pCoreIn 2) ⊔
        ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) ∧
      ∃ R : Sylow 2 (K F),
        (R : Subgroup (K F)).map (K F).subtype = S L F ⊔ (K F).pCoreIn 2 := by
  obtain ⟨m, hm⟩ := projective_one_copy d earlier k hk hS hcenter hPhi hpoint
    himage dual hcentralizer steinberg recognition
  let := intersection_normal d k hS hPhi earlier.sylow_normalizes m
  let := quotient_elementary d k hS hPhi earlier.sylow_normalizes m
  obtain ⟨σ, c, _, _, _, _, _, _, hone, hE⟩ := hm
  obtain ⟨n⟩ := natural_section_of_one_copy d k σ c hone
  have hgen := generation d k hS earlier.sylow_normalizes m
  have hP₀ := product_eq_core d k hS hPhi earlier.sylow_normalizes m
  have hproduct := (congrArg (fun A : Subgroup G => (A : Set G)) hP₀).symm.trans
    (P₀_coe_eq_product k (QH_normalizes_S hS earlier.sylow_normalizes))
  have hi (A : Subgroup G) (hA : A ≤ K F) :
      A ⊓ F.H.pCoreIn 2 = A ⊓ (K F).pCoreIn 2 := by
    rw [K_core_eq_intersection]
    exact le_antisymm (fun _ h => ⟨h.1, hA h.1, h.2⟩) (fun _ h => ⟨h.1, h.2.2⟩)
  rw [hi _ m.le_residual, hi _ (le_sup_right.trans hgen.ge)] at hproduct
  exact ⟨⟨n⟩, hE, hgen, hP₀, hproduct,
    RootRecognition.source_quotient_outputs d k hS hPhi earlier.sylow_normalizes
      hgen m.sylow m.sylow_image n⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Source
