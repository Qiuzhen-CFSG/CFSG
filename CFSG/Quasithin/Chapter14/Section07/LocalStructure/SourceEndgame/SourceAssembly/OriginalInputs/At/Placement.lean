module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Generation

/-!
# The original 14.7.71 product at the fixed group

The marked Borel generates the root four-group. The actual natural pairing
identifies the Q_K intersection with a rank-two annihilator; displacement
from the selected critical actor then proves the reverse product.
Only the structural input at the original G,T is used. Earlier-source
construction and final discharge remain with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.71–75, printed pp.1075–1078.
-/
public section

noncomputable section
open Subgroup Representation NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements

private theorem root_generated (r : ChapterJ.L2FourAction) (A : Subgroup ChapterJ.S5)
    (hA : A ≤ root r) (hne : A ≠ ⊥) :
    conjugateSpanBy A (borel r) = root r := by
  let N := conjugateSpanBy A (borel r)
  have hNR : N ≤ root r := conjugateSpanBy_le hA
    ((borel r).le_normalizer.trans (normalizer_le_root_normalizer r))
  have hRB : root r ≤ borel r := root_le_actor r (borel r) le_rfl
  let n : NormalNode (borel r) :=
    ⟨N.subgroupOf (borel r), normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy A (borel r))⟩
  have hnR : n ≤ rootNode r (borel r) le_rfl (borel r).le_normalizer :=
    subgroupOf_mono _ hNR
  rcases (rootNode_covBy r (borel r) le_rfl (borel r).le_normalizer).eq_or_eq
    bot_le hnR with hn | hn
  · exfalso
    apply hne
    apply bot_unique
    intro a ha
    have hmem : (⟨a, hRB (hA ha)⟩ : borel r) ∈ n.val := le_conjugateSpanBy _ _ ha
    rw [hn] at hmem
    exact congrArg Subtype.val (show (⟨a, hRB (hA ha)⟩ : borel r) = 1 from hmem)
  · have he := congrArg (fun n : NormalNode (borel r) => n.val.map (borel r).subtype) hn
    change (N.subgroupOf (borel r)).map (borel r).subtype =
      ((root r).subgroupOf (borel r)).map (borel r).subtype at he
    simpa only [map_subgroupOf_eq_of_le (hNR.trans hRB), map_subgroupOf_eq_of_le hRB] using he

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem marked_star (A : Subgroup G) :
    (star F A).map d.model.toMonoidHom = (A.subgroupOf F.H).map d.qH := by
  rw [CriticalFusion.Source.star, map_map]
  rfl

/-- The original critical involution generates the whole starred two-core. -/
theorem star_twoCore_eq_span_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d) :
    (star F (F.Li L 1)).pCoreIn 2 =
      conjugateSpanBy (star F c.Uα) (star F (F.Li L 1)) := by
  have hb := (compatibleBorel_of_upperMarking_at d structural mark).left_image
  have hA : ((c.Uα.subgroupOf F.H).map d.qH) ≤ root d.naturalQuotient := by
    have h := map_mono (f := d.qH) (subgroupOf_mono F.H e.images.placement)
    rw [mark] at h
    exact h
  have hn : (c.Uα.subgroupOf F.H).map d.qH ≠ ⊥ := by
    intro hn
    have hc : Nat.card ((c.Uα.subgroupOf F.H).map d.qH) = 2 := by
      rw [← marked_star d, card_map_of_injective d.model.injective]
      exact e.image_order
    rw [hn, Subgroup.card_bot] at hc
    norm_num at hc
  apply Subgroup.map_injective (f := d.model.toMonoidHom) d.model.injective
  rw [map_pCoreIn_of_injective 2 _ _ d.model.injective,
    map_conjugateSpanBy, marked_star, marked_star, hb, borel_twoCore]
  exact (root_generated d.naturalQuotient _ hA hn).symm

/-- The source (*) placement, with S intersected with H before taking its image. -/
theorem star_twoCore_le_S_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d) :
    (star F (F.Li L 1)).pCoreIn 2 ≤ star F (S F L) := by
  rw [star_twoCore_eq_span_at d structural c e mark]
  exact critical_star_span_le_S c e.conjugate

open scoped commutatorElement

/-- The plane-centralizer bound removes the ambient intersection in C_LT(V). -/
theorem centralizer_seed_eq_Q_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (sep : d.ModuleSeparation) : centralizer (V : Set G) = Q T L := by
  have hC : centralizer (V : Set G) ≤ L ⊔ (T : Subgroup G) :=
    ((centralizer_le (F.le_seed 2)).trans (d.plane_centralizer_le sep)).trans le_sup_right
  exact (inf_eq_right.mpr hC).symm.trans (d.natural.centralizer_LT_at structural)

/-- The first equality in source (**), on the literal Q_K. -/
theorem QK_centralizer_eq_intersection_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (sep : d.ModuleSeparation) :
    QK F ⊓ centralizer (V : Set G) = QK F ⊓ Q T L := by
  rw [centralizer_seed_eq_Q_at d structural sep]

/-- The original conjugate span lies in the actual two-core Q. -/
theorem S_le_Q_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (sep : d.ModuleSeparation) : S F L ≤ Q T L := by
  have hU : F.U ≤ Q T L := by
    rw [← centralizer_seed_eq_Q_at d structural sep]
    exact (le_centralizer_iff_isMulCommutative.mpr d.abelian).trans
      (centralizer_le (Data.V_le_U F))
  apply conjugateSpanBy_le hU
  exact le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- The easy containment of (**), including its actual centralizer denominator. -/
theorem product_le_QK_intersection_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (sep : d.ModuleSeparation) : (S F L ⊓ QK F) ⊔ C F ≤ QK F ⊓ Q T L := by
  apply sup_le
  · exact le_inf inf_le_right (inf_le_left.trans (S_le_Q_at d structural sep))
  · refine le_inf (show C F ≤ QK F from le_sup_right) ?_
    rw [← centralizer_seed_eq_Q_at d structural sep]
    exact inf_le_right.trans (centralizer_le (Data.V_le_U F))

/-- The same annihilator is the original intersection with Q. -/
theorem intersection_image_eq_annihilator_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (sep : d.ModuleSeparation) (b : QKDualCoordinates d) :
    b.qSection.imageSpace (QK F ⊓ Q T L) =
      ((naturalSection d).imageSpace V).dualAnnihilator := by
  rw [← QK_centralizer_eq_intersection_at d structural sep]
  exact centralizer_image_eq_annihilator d b


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

theorem source_commutator_le_at (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (b : QKDualCoordinates d) :
    ⁅c.Uα, QK F⁆ ≤ S F L ⊓ QK F := by
  apply le_inf
  · apply (commutator_mono (critical_le_S c e.conjugate) le_rfl).trans
    apply le_normalizer_iff_commutator_le_left.mp
    apply (QK_le_QH d e.sectionCentralizer).trans
    have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
      exact (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
        (map_subgroupOf_eq_of_le (F.invariant 1))
    exact hQT.trans (SteinbergRecognition.T_normalizes_S d (d.natural.sylow_normalizes_at structural))
  · rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((c.Uα_le_H e.images).trans b.qSection.normalized)

theorem intersection_image_finrank_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (sep : d.ModuleSeparation) (b : QKDualCoordinates d) :
    Module.finrank (ZMod 2) (b.qSection.imageSpace (QK F ⊓ Q T L)) = 2 := by
  rw [intersection_image_eq_annihilator_at d structural sep b]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq ((naturalSection d).imageSpace V)
  rw [seed_image_finrank d sep, SL2FourNatural.finrank_vector] at h
  omega

theorem source_intersection_image_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (b : QKDualCoordinates d) :
    b.qSection.imageSpace (S F L ⊓ QK F) = b.qSection.imageSpace (QK F ⊓ Q T L) := by
  obtain ⟨a, ha, t, ht, he⟩ := exists_upper_actor d c e.images mark e.image_order
  have hdisp := b.qSection.displacement_range_le_imageSpace_of_commutator_le
    c.Uα (S F L ⊓ QK F) (source_commutator_le_at d structural c e b) a ha
  have hle : b.qSection.imageSpace (S F L ⊓ QK F) ≤
      b.qSection.imageSpace (QK F ⊓ Q T L) :=
    b.qSection.imageSpace_mono (le_inf inf_le_right
      (inf_le_left.trans (S_le_Q_at d structural e.separation)))
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply Nat.le_antisymm (Submodule.finrank_mono hle)
  calc
    _ = 2 := intersection_image_finrank_at d structural e.separation b
    _ = _ := (dual_upper_displacement d a t ht he).symm
    _ ≤ _ := Submodule.finrank_mono hdisp

theorem reverse_product_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (b : QKDualCoordinates d) :
    QK F ⊓ Q T L = (S F L ⊓ QK F) ⊔ C F := by
  apply le_antisymm ?_ (product_le_QK_intersection_at d structural e.separation)
  intro x hx
  let q : QK F := ⟨x, hx.1⟩
  have hmem : (b.qSection.coordinates q).toAdd ∈ b.qSection.imageSpace (S F L ⊓ QK F) := by
    rw [source_intersection_image_at d structural c e mark b]
    exact (b.qSection.mem_imageSpace_iff _ _).mpr ⟨q, hx, rfl⟩
  obtain ⟨r, hr, he⟩ := (b.qSection.mem_imageSpace_iff _ _).mp hmem
  have hk : (r⁻¹ * q : QK F).val ∈ C F := by
    apply (b.qSection.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, Multiplicative.toAdd.injective he, inv_mul_cancel]
  have hq : (r * (r⁻¹ * q) : QK F).val ∈ (S F L ⊓ QK F) ⊔ C F :=
    mul_mem (mem_sup_left hr) (mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using hq

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Equation (**) on the original subgroups, with the compatible dual
coordinates constructed from the earlier 14.5.21 pairing and commutator. -/
theorem source_product_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    QK F ⊓ centralizer (V : Set G) = QK F ⊓ Q T L ∧
    QK F ⊓ Q T L = (S F L ⊓ QK F) ⊔ C F := by
  obtain ⟨b⟩ := HAccounting.exists_qKDualCoordinates d e.sectionCentralizer duality hcomm
  exact ⟨QK_centralizer_eq_intersection_at d structural e.separation,
    reverse_product_at d structural c e mark b⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
