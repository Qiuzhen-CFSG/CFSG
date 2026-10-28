module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceBorel
public import Theory.GroupTheory.ConjugateSpanSylow
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceMarking
public import Theory.GroupTheory.PCoreImage

/-!
# Core placement and the original Q_K annihilator in 14.7.71

The marked Borel's irreducible noncentral core factor shows that every
nontrivial subgroup of its root four-group generates that root under the
Borel. The original upper marking supplies the Borel image through the
proved SourceBorel adapter. Transport through the injective S₅ marking
therefore identifies O₂(L₁*) with the L₁*-span of Uα*, and the earlier
critical-span containment puts this core in S*. No containment S ≤ H is
used: every star image retains subgroupOf H.

The earlier natural-action centralizer theorem and plane-centralizer bound
give C_G(V)=Q. The compatible Q_K/C_H(U) pairing then identifies the
literal Q_K∩Q image with the annihilator of the original V-image. We also
prove S≤Q and the easy product containment in (**). The reverse product
containment, its corank-two displacement calculation, and the four actual
L₁-chief intervals remain separate obligations of QKPlacement.

Finally, the unchanged map qL has two-group kernel, so the actual bar L₁
core is the image of the actual L₁ core, with all relative embeddings
retained. This is a two-core calculation, not a two-residual calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.71, printed p.1075 (PDF p.1092), equations (*) and (**).
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
theorem star_twoCore_eq_span
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d) :
    (star F (F.Li L 1)).pCoreIn 2 =
      conjugateSpanBy (star F c.Uα) (star F (F.Li L 1)) := by
  have hb := (compatibleBorel_of_upperMarking d structural mark).left_image
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
theorem star_twoCore_le_S
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d) :
    (star F (F.Li L 1)).pCoreIn 2 ≤ star F (S F L) := by
  rw [star_twoCore_eq_span d structural c e mark]
  exact critical_star_span_le_S c e.conjugate

open scoped commutatorElement

/-- The plane-centralizer bound removes the ambient intersection in C_LT(V). -/
theorem centralizer_seed_eq_Q
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (sep : d.ModuleSeparation) : centralizer (V : Set G) = Q T L := by
  have hC : centralizer (V : Set G) ≤ L ⊔ (T : Subgroup G) :=
    ((centralizer_le (F.le_seed 2)).trans (d.plane_centralizer_le sep)).trans le_sup_right
  exact (inf_eq_right.mpr hC).symm.trans (d.natural.centralizer_LT structural)

/-- The first equality in source (**), on the literal Q_K. -/
theorem QK_centralizer_eq_intersection
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (sep : d.ModuleSeparation) :
    QK F ⊓ centralizer (V : Set G) = QK F ⊓ Q T L := by
  rw [centralizer_seed_eq_Q d structural sep]

/-- The original conjugate span lies in the actual two-core Q. -/
theorem S_le_Q
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (sep : d.ModuleSeparation) : S F L ≤ Q T L := by
  have hU : F.U ≤ Q T L := by
    rw [← centralizer_seed_eq_Q d structural sep]
    exact (le_centralizer_iff_isMulCommutative.mpr d.abelian).trans
      (centralizer_le (Data.V_le_U F))
  apply conjugateSpanBy_le hU
  exact le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- The easy containment of (**), including its actual centralizer denominator. -/
theorem product_le_QK_intersection
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (sep : d.ModuleSeparation) : (S F L ⊓ QK F) ⊔ C F ≤ QK F ⊓ Q T L := by
  apply sup_le
  · exact le_inf inf_le_right (inf_le_left.trans (S_le_Q d structural sep))
  · refine le_inf (show C F ≤ QK F from le_sup_right) ?_
    rw [← centralizer_seed_eq_Q d structural sep]
    exact inf_le_right.trans (centralizer_le (Data.V_le_U F))

/-- The compatible pairing identifies the literal centralizer with the annihilator
of the original V-image, before any dimension or displacement calculation. -/
theorem mem_centralizer_iff_annihilator (b : QKDualCoordinates d) (q : QK F) :
    (q : G) ∈ centralizer (V : Set G) ↔
      (b.qSection.coordinates q).toAdd ∈ ((naturalSection d).imageSpace V).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h v hv
    obtain ⟨a, ha, rfl⟩ := ((naturalSection d).mem_imageSpace_iff V v).mp hv
    apply (b.functional_kernel q a).mpr
    exact commutatorElement_eq_one_iff_commute.mpr (h a ha).symm
  · intro h v hv
    let a : F.U := ⟨v, Data.V_le_U F hv⟩
    have hz := h (naturalMap d a).toAdd
      (((naturalSection d).mem_imageSpace_iff V _).mpr ⟨a, hv, rfl⟩)
    exact (commutatorElement_eq_one_iff_commute.mp ((b.functional_kernel q a).mp hz)).eq.symm

/-- Surjectivity of the genuine Q_K/C coordinates gives the whole annihilator,
not merely an inclusion or an abstract isomorphism. -/
theorem centralizer_image_eq_annihilator (b : QKDualCoordinates d) :
    b.qSection.imageSpace (QK F ⊓ centralizer (V : Set G)) =
      ((naturalSection d).imageSpace V).dualAnnihilator := by
  ext f
  constructor
  · intro hf
    obtain ⟨q, hq, rfl⟩ := (b.qSection.mem_imageSpace_iff _ f).mp hf
    exact (mem_centralizer_iff_annihilator d b q).mp hq.2
  · intro hf
    obtain ⟨q, hq⟩ := b.qSection.onto (Multiplicative.ofAdd f)
    have he : (b.qSection.coordinates q).toAdd = f := congrArg Multiplicative.toAdd hq
    exact (b.qSection.mem_imageSpace_iff _ f).mpr
      ⟨q, ⟨q.property, (mem_centralizer_iff_annihilator d b q).mpr (he.symm ▸ hf)⟩, he⟩

/-- The same annihilator is the original intersection with Q. -/
theorem intersection_image_eq_annihilator
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (sep : d.ModuleSeparation) (b : QKDualCoordinates d) :
    b.qSection.imageSpace (QK F ⊓ Q T L) =
      ((naturalSection d).imageSpace V).dualAnnihilator := by
  rw [← QK_centralizer_eq_intersection d structural sep]
  exact centralizer_image_eq_annihilator d b

omit [Finite G] in
/-- Restricting the actual two-core of L₁ to L retains the subgroup embeddings. -/
theorem left_core_subgroupOf :
    ((F.Li L 1).subgroupOf L).pCoreIn 2 = ((F.Li L 1).pCoreIn 2).subgroupOf L := by
  have hleft : F.Li L 1 ≤ L := (F.Li_le L 1).trans inf_le_left
  apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
  rw [map_pCoreIn_of_injective, map_subgroupOf_eq_of_le hleft,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans hleft)]
  exact L.subtype_injective

/-- The original bar quotient has two-group kernel, so its actual L₁-image
has precisely the image of the original L₁ two-core as its two-core. -/
theorem bar_twoCore_eq_image :
    (((F.Li L 1).subgroupOf L).map d.qL).pCoreIn 2 =
      (((F.Li L 1).pCoreIn 2).subgroupOf L).map d.qL := by
  have hk : IsPGroup 2 d.qL.ker := by
    rw [d.qL_ker]
    exact (isPGroup_pCoreIn 2 L).comap_subtype
  rw [← map_pCoreIn_of_ker_isPGroup d.qL hk, left_core_subgroupOf]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement
