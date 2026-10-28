module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.NaturalSection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceChief
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Basic

/-!
# Source preparation and the centralizer step of 14.7.71

All earlier inputs refer to one critical choice. The original natural
quotient and 14.7.70 intersection give the relative index four; 14.7.66 and
69 give the even image of order two. The point centralizer normalizes Uα,
and 14.5.15(4) places C_H(U) in O₂(H). Thus the existing finite-group lifting
theorem applies with every local premise discharged from these source inputs.

The literal R=⟨U₀ᴸ⟩ application proves [R,L₁]≤R∩U once the independent
14.7.72 generation argument places R in C_H(U). We also place the L₁-span
of Uα* in S*, using subgroupOf H throughout and without assuming S≤H.
Its identification with O₂(L₁*) remains a TWO-CORE calculation.

`QKDualCoordinates` is the shared genuine pairing interface for the two
remaining branches: the H-accounting producer constructs it, and the Q_K
placement proof may consume it. It asserts neither a chief count nor the
centralizer/product identity. Final 14.7.71 assembly must construct it.

The earlier 14.5.15/21 and 14.7.2/66–70 producers remain with qt-14-07.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.71–72, printed pp.1075–1076.
-/

@[expose] public section
noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The original conjugate span, without assuming S ≤ H. -/
def S (F : InvariantFlag T V 3) (L : Subgroup G) : Subgroup G := conjugateSpanBy F.U L

/-- The literal relative centralizer, in the ambient group. -/
def C (F : InvariantFlag T V 3) : Subgroup G := F.H ⊓ centralizer (F.U : Set G)

/-- The original subgroup Q_K from the proof of 14.7.71. -/
def QK (F : InvariantFlag T V 3) : Subgroup G := ⁅F.H.pCoreIn 2, K F⁆ ⊔ C F

/-- Coordinates on the actual commutator section Q_K/C_H(U), paired
with the original U/U₀ projection. The functional kernel is an actual
commutator kernel, not an arbitrary isomorphism of abstract modules. -/
structure QKDualCoordinates (d : Data T L V F W) where
  qSection : BinaryConjugationSection F.H (QK F) (C F) (naturalAction d).dual
  functional_kernel : ∀ q : QK F, ∀ v : F.U,
    (qSection.coordinates q).toAdd ((naturalMap d v).toAdd) = 0 ↔
      ⁅(q : G), (v : G)⁆ = 1

/-- Earlier 14.7.2, 14.5.15(4) and 14.7.66–70, all at the same chosen
critical vertex. No 14.7.71 chiefness, count or placement is a field. -/
structure Earlier (d : Data T L V F W) (c : CriticalPath (L := L) F) : Prop where
  separation : d.ModuleSeparation
  sectionCentralizer : d.SectionCentralizer
  images : c.EarlierImages
  point : c.Zα ≤ F.Vi 2
  image_order : Nat.card (star F c.Uα) = 2
  intersection : F.U ⊓ c.Uα = d.U₀ ⊔ V
  commutator_seed : F.U ⊓ c.Uα = ⁅F.U, c.Uα⁆ ⊔ V
  commutator_fixed : F.U ⊓ c.Uα = ⁅F.U, c.Uα⁆ ⊔ d.U₀
  distance : c.b = 3
  conjugate : ∃ l ∈ L, c.Uα = Chapter12.Section08.conjugate F.U l

variable (d : Data T L V F W)

include d in
theorem U_le_QH : F.U ≤ F.H.pCoreIn 2 := by
  let := d.U_elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U)
    d.conjugationSection.section_le d.conjugationSection.normalized

theorem C_le_QH (hc : d.SectionCentralizer) : C F ≤ F.H.pCoreIn 2 :=
  inf_le_right.trans (CriticalIntersections.centralizer_U_le_core d hc)

include d in
theorem U_le_C : F.U ≤ C F := by
  let := d.abelian
  exact le_inf d.conjugationSection.section_le (le_centralizer_iff_isMulCommutative.mpr d.abelian)

include d in
/-- Normality is relative to H; no ambient normality is asserted. -/
theorem C_normal : ((C F).subgroupOf F.H).Normal := by
  let : (F.U.subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer d.conjugationSection.normalized
  have he : (C F).subgroupOf F.H = centralizer (F.U.subgroupOf F.H : Set F.H) := by
    ext c
    constructor
    · intro hc u hu
      exact Subtype.ext (hc.2 u hu)
    · intro hc
      refine ⟨c.property, ?_⟩
      intro u hu
      exact congrArg Subtype.val (hc ⟨u, d.conjugationSection.section_le hu⟩ hu)
  rw [he]
  infer_instance

theorem QK_le_QH (hc : d.SectionCentralizer) : QK F ≤ F.H.pCoreIn 2 := by
  have hQn : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (le_normalizer_map (H := pCore 2 F.H) F.H.subtype)
  exact sup_le (le_normalizer_iff_commutator_le_left.mp ((K_le_H F).trans hQn))
    (C_le_QH d hc)

theorem critical_index_four (c : CriticalPath (L := L) F)
    (hs : d.ModuleSeparation) (hi : F.U ⊓ c.Uα = d.U₀ ⊔ V) :
    F.U.relIndex c.Uα = 4 := by
  have hα : Nat.card c.Uα = Nat.card F.U :=
    card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective
  have hindex := relIndex_mul_relIndex (⊥ : Subgroup G) (F.U ⊓ c.Uα) c.Uα
    bot_le inf_le_right
  simp only [relIndex_bot_left, inf_relIndex_right] at hindex
  rw [hi, hα, CriticalIntersections.card_U_eq_sixteen_mul_card_U₀ d,
    CriticalIntersections.card_fixed_product d hs] at hindex
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 4 * Nat.card d.U₀ by
    exact Nat.mul_pos (by decide) Nat.card_pos)
  nlinarith

/-- Specialization of the existing finite-group lift: both containment
premises, the relative index and the even marked image are discharged. -/
theorem centralizer_commutator (c : CriticalPath (L := L) F) (e : Earlier d c) :
    ⁅K F, C F⁆ ≤ F.U := by
  have hCN : C F ≤ normalizer (c.Uα : Set G) := by
    apply inf_le_right.trans
    apply (centralizer_le (e.point.trans ((F.le_seed 2).trans (Data.V_le_U F)))).trans
    rw [CriticalIntersections.critical_point_centralizer_eq d c]
    exact (map_mono d.conjugationSection.normalized).trans (le_normalizer_map _)
  have hcard : Nat.card ((c.Uα.subgroupOf F.H).map d.qH) = 2 := by
    change Nat.card ((c.Uα.subgroupOf F.H).map
      (d.model.toMonoidHom.comp (starMap F))) = 2
    rw [← map_map, card_map_of_injective d.model.injective]
    exact e.image_order
  have hle : star F c.Uα ≤ star F (K F) := by
    exact (c.lemma_14_7_66 e.images).1.trans
      (Chapter1.isSylowIn_iff.mp (c.lemma_14_7_66 e.images).2).2.1
  have hmarked : (c.Uα.subgroupOf F.H).map d.qH ≤
      ((K F).subgroupOf F.H).map d.qH := by
    have hm := map_mono (f := d.model.toMonoidHom) hle
    simpa only [CriticalFusion.Source.star, map_map, Data.qH] using hm
  exact source_centralizer_commutator_le d c.Uα (c.Uα_le_H e.images)
    (U_le_QH d) (C_le_QH d e.sectionCentralizer) hCN
    (critical_index_four d c e.separation e.intersection) hcard hmarked

set_option backward.isDefEq.respectTransparency false in
omit [Finite G] in
/-- The original L₁ is a two-residual inside H, hence lies in K=O²(H). -/
theorem L₁_le_K : F.Li L 1 ≤ K F := by
  simpa only [InvariantFlag.Li, InvariantFlag.H, K, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,
    if_false] using
    (embedded_pResidual_mono 2 (inf_le_right : L ⊓ F.H ≤ F.H))

/-- The precise centralizer inference used in 14.7.72 for R=⟨U₀ᴸ⟩.
The independent R-generation argument supplies its containment in C_H(U). -/
theorem fixed_span_commutator (c : CriticalPath (L := L) F) (e : Earlier d c)
    (hR : conjugateSpanBy d.U₀ L ≤ C F) :
    ⁅conjugateSpanBy d.U₀ L, F.Li L 1⁆ ≤ conjugateSpanBy d.U₀ L ⊓ F.U := by
  apply le_inf
  · exact le_normalizer_iff_commutator_le_left.mp
      (((F.Li_le L 1).trans inf_le_left).trans (le_normalizer_conjugateSpanBy _ _))
  · rw [commutator_comm]
    exact (commutator_mono L₁_le_K hR).trans (centralizer_commutator d c e)

omit [Finite G] in
theorem U_le_S : F.U ≤ S F L := le_conjugateSpanBy _ _

omit [Finite G] in
theorem L_normalizes_S : L ≤ normalizer (S F L : Set G) := le_normalizer_conjugateSpanBy _ _

omit [Finite G] in
theorem critical_le_S (c : CriticalPath (L := L) F)
    (hconj : ∃ l ∈ L, c.Uα = Chapter12.Section08.conjugate F.U l) : c.Uα ≤ S F L := by
  obtain ⟨l, hl, he⟩ := hconj
  rw [he]
  rintro x ⟨u, hu, rfl⟩
  exact subset_closure ⟨l⁻¹, L.inv_mem hl, u, hu, by simp⟩

omit [Finite G] in
/-- The quotient image keeps the actual subgroupOf H, even though S is
only known to be normalized by L. -/
theorem critical_star_le_S (c : CriticalPath (L := L) F)
    (hconj : ∃ l ∈ L, c.Uα = Chapter12.Section08.conjugate F.U l) :
    star F c.Uα ≤ star F (S F L) :=
  map_mono (subgroupOf_mono F.H (critical_le_S c hconj))

omit [Finite G] in
/-- L₁-normalization descends through the original star map. -/
theorem L₁_star_normalizes_S : star F (F.Li L 1) ≤ normalizer (star F (S F L) : Set _) := by
  have hn : (F.Li L 1).subgroupOf F.H ≤ normalizer ((S F L).subgroupOf F.H : Set F.H) := by
    apply le_normalizer_iff.mpr
    intro h hh x hx
    exact le_normalizer_iff.mp (L_normalizes_S (F := F) (L := L)) h
      ((F.Li_le L 1 hh).1) x hx
  exact (map_mono hn).trans (le_normalizer_map (starMap F))

omit [Finite G] in
/-- The generated starred subgroup in (*) lies in S*. The identification
of this subgroup with the TWO-CORE of L₁* is a separate model calculation. -/
theorem critical_star_span_le_S (c : CriticalPath (L := L) F)
    (hconj : ∃ l ∈ L, c.Uα = Chapter12.Section08.conjugate F.U l) :
    conjugateSpanBy (star F c.Uα) (star F (F.Li L 1)) ≤ star F (S F L) :=
  conjugateSpanBy_le (critical_star_le_S c hconj) L₁_star_normalizes_S

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors
