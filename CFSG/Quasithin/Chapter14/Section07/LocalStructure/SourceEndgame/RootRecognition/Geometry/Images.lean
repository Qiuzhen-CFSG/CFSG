module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images.NaturalLine
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images.PointResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting.SteinbergGeneration

/-!
# Constructing the original marked root images

The genuine earlier O₂(L₁*) Sylow statement and exact71 containment identify
the original S-image as Sylow. Its fixed plane is the coordinate image of
V/V₁, so its literal root group, movement by the original k, and normalizer
lifts all follow from the original natural section and earlier normalizers.
The two line fixers generate SL₂(4), with right conjugation by this same k.
Applying Geometry gives generation of K and the literal ordered P₀ product.

The original natural and Steinberg sections give S = [S,L₁] ≤ L₁ ≤ K.
The PointResidual leaf constructs the required point-residual image in the
unchanged qL marking. Thus the final constructor and product consumer have
no containment or marked-image premises. Only genuine earlier setup and
the indicated 14.7.71–72 outputs remain explicit; their source producers
and the remaining clauses of 14.7.73 belong to the parent assembly.

Source: Aschbacher–Smith, printed pp.1069, 1075–1077,
combined manuscript of 1 March 2004, 14.7.64 and 14.7.71–73.
-/

public section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images
open Chapter12.Section08 CriticalFusion.Source
open ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The genuine earlier normalizer and starred Sylow statements. None refers
to the image of S, a projective line, or a normalizer of a root group. -/
structure Earlier (d : Data T L V F W) : Prop where
  sylow_normalizes : (T : Subgroup G) ≤ normalizer L
  separation : d.ModuleSeparation
  point_normalizer : F.H ⊓ normalizer (V : Set G) = F.Li L 1 ⊔ (T : Subgroup G)
  sylow : EarlierSylow (L := L) (F := F)

private theorem image_conjugate (A : Subgroup G) (hAK : A ≤ K F) (k : K F) :
    ((A.conjBy (k : G)).subgroupOf (K F)).map (qK d) =
      ((A.subgroupOf (K F)).map (qK d)).map (MulAut.conj (qK d k)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨b, ⟨a, ha, hab⟩, rfl⟩
    refine ⟨qK d ⟨a, hAK ha⟩, ⟨⟨a, hAK ha⟩, ha, rfl⟩, ?_⟩
    have hb : b = k * (⟨a, hAK ha⟩ : K F) * k⁻¹ := Subtype.ext hab.symm
    rw [hb, map_mul, map_mul, map_inv]
    rfl
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨k * a * k⁻¹, ⟨a, ha, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]

/-- Construct the marked images after placing the original S in K.
The final `markedImages` constructor below discharges this containment. -/
theorem markedImages_of_le_residual (e : Earlier d) (k : K F)
    (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G))
    (hS : S L F = L.pCoreIn 2)
    (hcenter : (center (S L F)).map (S L F).subtype = V)
    (hp : d.U₀ = F.Vi 1)
    (h71 : TwoCoreImage (L := L) (F := F)) (hSK : S L F ≤ K F) :
    Nonempty (MarkedImages d k) := by
  have hUK : F.U ≤ K F := (le_conjugateSpanBy F.U L).trans hSK
  obtain ⟨R, hR⟩ := exists_sylow_image d hS hSK e.sylow h71
  obtain ⟨P, hP, hroot⟩ := exists_seed_line d hp hUK hcenter R hR
  have hkV : (k : G) ∉ normalizer (V : Set G) := by
    intro h
    apply hk
    rw [← e.point_normalizer]
    exact ⟨K_le_H F k.property, h⟩
  have hkP : qK d k ∉ MulAction.stabilizer SL2FourNatural.SL
      (P.val : Set SL2FourNatural.V) := by
    intro h
    exact hkV ((stabilizer_preimage d hp hUK P hP k).mp h)
  have hmoved : P.val ≠ P.val.map (Representation.specialLinearNatural 2 (qK d k⁻¹)) := by
    intro h
    have hstab : qK d k⁻¹ ∈ MulAction.stabilizer SL2FourNatural.SL
        (P.val : Set SL2FourNatural.V) := by
      rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
      intro v hv
      change Representation.specialLinearNatural 2 (qK d k⁻¹) v ∈ P.val
      rw [h]
      exact ⟨v, hv, rfl⟩
    have hn := (stabilizer_preimage d hp hUK P hP k⁻¹).mp hstab
    exact hkV (by simpa only [inv_inv, Subgroup.coe_inv] using (normalizer _).inv_mem hn)
  have hBK : (S L F).conjBy ((k : G)⁻¹) ≤ K F := by
    rintro x ⟨s, hs, rfl⟩
    exact (K F).mul_mem ((K F).mul_mem ((K F).inv_mem k.property) (hSK hs))
      ((K F).inv_mem ((K F).inv_mem k.property))
  have hpair : ((S L F ⊔ (S L F).conjBy ((k : G)⁻¹)).subgroupOf (K F)).map
      (qK d) = ⊤ := by
    have hi := image_conjugate d _ hSK k⁻¹
    simp only [Subgroup.coe_inv] at hi
    rw [subgroupOf_sup hSK hBK, Subgroup.map_sup, hi, hR,
      hroot, root_eq_fixer P, map_inv]
    exact Matrix.SpecialLinearGroup.fixing_line_sup_right_conjugate P.val P.property (qK d k) hkP
  refine ⟨{
    le_residual := hSK
    sylow := R
    sylow_image := hR
    pair_image := hpair
    point := P
    root_image := hR.trans hroot
    point_moved := hmoved
    normalizer_lift := ?_ }⟩
  intro a ha
  rw [root_eq_fixer P, Matrix.SpecialLinearGroup.normalizer_fixing_line P.val P.property] at ha
  obtain ⟨l, hl⟩ := qK_surjective d a
  have hlV := (stabilizer_preimage d hp hUK P hP l).mp (hl ▸ ha)
  have hlLT : (l : G) ∈ L ⊔ (T : Subgroup G) :=
    (d.lemma_14_7_67_five e.separation).ge hlV
  have hlL : (l : G) ∈ normalizer L :=
    sup_le L.le_normalizer e.sylow_normalizes hlLT
  refine ⟨l, hl, ?_⟩
  rw [hS]
  exact normalizer_le_normalizer_characteristic_image L (pCore 2 L) hlL

/-- Apply the original generation and product consumers after placing S in K.
The final `source_products` theorem below discharges this containment. -/
theorem source_products_of_le_residual (e : Earlier d) (k : K F)
    (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G))
    (hS : S L F = L.pCoreIn 2)
    (hcenter : (center (S L F)).map (S L F).subtype = V)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hp : d.U₀ = F.Vi 1)
    (h71 : TwoCoreImage (L := L) (F := F)) (hSK : S L F ≤ K F) :
    K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹) ∧
      P₀ L F k = (K F).pCoreIn 2 ∧
      ((K F).pCoreIn 2 : Set G) =
        ((S L F ⊓ F.H.pCoreIn 2 : Subgroup G) : Set G) *
        (((S L F).conjBy ((k : G)⁻¹) ⊓ F.H.pCoreIn 2 : Subgroup G) : Set G) := by
  obtain ⟨m⟩ := markedImages_of_le_residual d e k hk hS hcenter hp h71 hSK
  have hg := Geometry.generation d k hS e.sylow_normalizes m
  have hp₀ := Geometry.product_eq_core d k hS hPhi e.sylow_normalizes m
  exact ⟨hg, hp₀, (congrArg (fun A : Subgroup G => (A : Set G)) hp₀).symm.trans
    (P₀_coe_eq_product k (QH_normalizes_S hS e.sylow_normalizes))⟩

/-- The opening commutator and containment step of 14.7.73, using the
original natural coordinates and the 14.7.72 Steinberg section. The
point-residual marking is constructed from d, and L₁ ≤ K is residual
monotonicity for L ∩ H ≤ H. -/
theorem source_commutator_and_le_residual
    (hS : S L F = L.pCoreIn 2)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL)) :
    ⁅S L F, F.Li L 1⁆ = S L F ∧ S L F ≤ K F := by
  obtain ⟨g, hmark⟩ := exists_point_residual_image d
  exact ⟨ParabolicCounting.SteinbergGeneration.steinberg_commutator d s g hmark,
    (ParabolicCounting.SteinbergGeneration.S_le_L₁ d hS hTL s g hmark).trans
      ParabolicCounting.parabolic_le_K⟩

/-- All marked images for the original k, derived from genuine earlier setup
and the indicated 14.7.71–72 outputs. No containment, point-residual marking,
Sylow image, projective line, or normalizer lift is assumed. -/
theorem markedImages (e : Earlier d) (k : K F)
    (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G))
    (hS : S L F = L.pCoreIn 2)
    (hcenter : (center (S L F)).map (S L F).subtype = V)
    (hp : d.U₀ = F.Vi 1)
    (h71 : TwoCoreImage (L := L) (F := F))
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL)) :
    Nonempty (MarkedImages d k) :=
  markedImages_of_le_residual d e k hk hS hcenter hp h71
    (source_commutator_and_le_residual d hS e.sylow_normalizes s).2

/-- Generation of the original K and the literal ordered P₀ product, with
all marked-image and containment premises discharged. The earlier setup,
exact71 two-core image, and exact72 identities/section retain their source
producers; the other 14.7.73 clauses retain their parent assembly. -/
theorem source_products (e : Earlier d) (k : K F)
    (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G))
    (hS : S L F = L.pCoreIn 2)
    (hcenter : (center (S L F)).map (S L F).subtype = V)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hp : d.U₀ = F.Vi 1)
    (h71 : TwoCoreImage (L := L) (F := F))
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL)) :
    K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹) ∧
      P₀ L F k = (K F).pCoreIn 2 ∧
      ((K F).pCoreIn 2 : Set G) =
        ((S L F ⊓ F.H.pCoreIn 2 : Subgroup G) : Set G) *
        (((S L F).conjBy ((k : G)⁻¹) ⊓ F.H.pCoreIn 2 : Subgroup G) : Set G) :=
  source_products_of_le_residual d e k hk hS hcenter hPhi hp h71
    (source_commutator_and_le_residual d hS e.sylow_normalizes s).2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images
