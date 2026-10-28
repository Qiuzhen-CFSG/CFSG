module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion.Inputs
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Construction

/-!
# Source root generation, natural quotient and cardinalities

The preceding normalizer and starred Sylow inputs are constructed, and the
71 two-core placement and pairing supply the exact dual coordinates. The
marked projective-root argument produces the natural P/E section and
E=C_P(U); coprime fixed-point transport then gives every parabolic and
cardinality conclusion. The only independent recognition premise is the
universal earlier G.1.3 theorem, owned by qt-g-01.

The final consumer retains the literal qK and feeds the RuTwo constructor
after the later 74 equality O₂(H)=O₂(K).
Source: Aschbacher–Smith 14.7.73–75, printed pp.1076–1078.
-/

public section
noncomputable section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

structure Conclusion73 (k : K F) : Prop where
  natural : Nonempty (BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
    (SL2FourNatural.naturalRepresentation.comp (qK d)))
  generation : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹)
  sylow_image : ∃ R : Sylow 2 SL2FourNatural.SL,
    ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _)
  product_eq_core : P₀ L F k = (K F).pCoreIn 2
  ordered_product : ((K F).pCoreIn 2 : Set G) =
    ((S L F ⊓ (K F).pCoreIn 2 : Subgroup G) : Set G) *
    (((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2 : Subgroup G) : Set G)
  intersection : E L F k = (K F).pCoreIn 2 ⊓ centralizer (F.U : Set G)
  parabolic : S L F ⊔ (K F).pCoreIn 2 = (F.Li L 1).pCoreIn 2
  sylow_intersection : (F.Li L 1).pCoreIn 2 = (T : Subgroup G) ⊓ K F
  sylow_witness : ∃ R : Sylow 2 (K F),
    (R : Subgroup (K F)).map (K F).subtype = (F.Li L 1).pCoreIn 2
  index : ((T : Subgroup G) ⊓ K F).relIndex ((T : Subgroup G) ⊓ L) = 2
  elementary :
    letI : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
    IsElementaryAbelian 2 ((K F).pCoreIn 2 ⧸ F.U.subgroupOf ((K F).pCoreIn 2))
  commutator_generation : ⁅(K F).pCoreIn 2, K F⁆ ⊔ F.U = (K F).pCoreIn 2
  root_product : (K F).pCoreIn 2 = (S L F ⊓ (K F).pCoreIn 2) ⊔
    ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2)
  fixed_counts : ∀ B : Sylow 3 (F.Li L 1),
    Nat.card (S L F ⊓ centralizer (ParabolicCounting.cubic B : Set G) : Subgroup G) = 8 ∧
    Nat.card (F.U ⊓ centralizer (ParabolicCounting.cubic B : Set G) : Subgroup G) = 2
  kernel_index : F.U.relIndex (E L F k) = 4
  card : Nat.card ((K F).pCoreIn 2) = 2 ^ 11

theorem roots_of_source_sections
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hS : S L F = L.pCoreIn 2)
    (hcenter : (center (S L F)).map (S L F).subtype = V)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hp : d.U₀ = F.Vi 1)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (recognition : Geometry.NaturalRecognition.{u}) (k : K F)
    (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G)) : Conclusion73 d k := by
  let earlier := source_geometry_earlier d structural e.separation mark
  have himage : Geometry.Images.TwoCoreImage (L := L) (F := F) :=
    Geometry.Images.twoCoreImage_iff.mpr (ChiefFactors.QKPlacement.star_twoCore_le_S d structural c e mark)
  obtain ⟨X,aX,mX,hd⟩ := CriticalIntersections.exists_sourceDuality d e.sectionCentralizer
  let := aX
  let := mX
  obtain ⟨dual⟩ := hd
  obtain ⟨b⟩ := ChiefFactors.HAccounting.exists_qKDualCoordinates d e.sectionCentralizer dual hcomm
  have hcentralizer := ChiefFactors.centralizer_commutator d c e
  obtain ⟨⟨n⟩,hE,hgen,hP₀,hproduct,helem,hcommP,hprod,_⟩ :=
    Geometry.Source.quotient_outputs d earlier k hk hS hcenter hPhi hp himage b hcentralizer s recognition
  obtain ⟨R,hR⟩ := Geometry.Images.exists_sylow_image d hS (le_sup_left.trans hgen.ge) earlier.sylow himage
  obtain ⟨g,hmark⟩ := Geometry.Images.exists_point_residual_image d
  let B : Sylow 3 (F.Li L 1) := Classical.choice inferInstance
  obtain ⟨hSP,hTK,hSyl,hindex,_,_,_,_,_,hEU,hcard⟩ :=
    ParabolicCounting.source_parabolic_outputs d k hS hPhi earlier.sylow_normalizes hgen R hR hp s n g hmark B
  exact {
    natural := ⟨n⟩
    generation := hgen
    sylow_image := ⟨R,hR⟩
    product_eq_core := hP₀
    ordered_product := hproduct
    intersection := hE
    parabolic := hSP
    sylow_intersection := hTK
    sylow_witness := hSyl
    index := hindex
    elementary := helem
    commutator_generation := hcommP
    root_product := hprod
    fixed_counts := ParabolicCounting.source_fixed_counts d hS
      ((U_le_E d k).trans (n.kernel_le.trans (pCoreIn_le 2 _))) hp s
      (ParabolicCounting.SteinbergGeneration.marked_image_card d g hmark)
    kernel_index := hEU
    card := hcard }

theorem ruTwo_of_roots (k : K F) (h : Conclusion73 d k)
    (hS : S L F = L.pCoreIn 2)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hp : d.U₀ = F.Vi 1)
    (hz : ChapterJ.sylowCenter T = F.Vi 1)
    (hcore : F.H.pCoreIn 2 = (K F).pCoreIn 2) : Nonempty (ChapterJ.RuTwo V T) := by
  obtain ⟨n⟩ := h.natural
  obtain ⟨R,hR⟩ := h.sylow_image
  exact source_ruTwo d k hS hPhi hTL h.generation R hR n h.kernel_index hp hz hcore

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
