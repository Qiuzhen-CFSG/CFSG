module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoFixedCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.MSRecognition

/-!
# Saturated distance-two data for the original closure MS-pair

Apply the common full-radical construction to the literal product group
L O₂(G₁) and the original quotient marking supplied by `intrinsicMSInput`.
The actual critical endpoints retain their entire fixed attachments, and
the full-core index bound holds on both sides of this same configuration.
The component intersections also give both literal T₀ factorizations and
full-radical index bounds. Paired parabolic displacements retain the whole
fixed attachments and an explicit Sylow alternative. The large-image
Sylow fixed-centralizer count now gives full-radical centrality at both
endpoints under the original saturation and distance hypotheses.
The critical centralizer bound and both full edge-center decompositions
now hold without an order-q premise. The small-movement branch of source
(3.7)(2) applies to this same original quotient and its entire opposite core.
Its remaining large-movement branch now has both critical images of order q
and the source factorization T₀ = U (T₀ ∩ Q′), retaining the full fixed
attachments and the original saturated radical. Both complete fixed
kernels lie in the actual critical commutator and have equal orders. The
fixed-core displacement meets that commutator only inside the first fixed
kernel, and its order is at most q times the order of that kernel.
The same full fixed attachment has opposite actor image of order at most 2q.
The full-radical index is now q³ in the large-movement branch, excluding the
full Sylow alternative with its order q⁴. The same original ambient cover
now identifies the entire common radical as a point radical, with its
literal quotient marking and complete core kernel retained.

The fixed-core index squeeze now excludes large movement and proves
[Z′,Q] ≤ Z_t from the original saturation and distance-two hypotheses.
The noncontained-core branch of (3) now selects a plane radical on the
original natural cover and computes both midpoint indices. The full Sylow
branch of (3) is complete, including its core decomposition and overlap indices.
The noncontained branch now has the whole-core and full-radical displacement
comparisons and the equality [T₀,Z′] = [Z,Z′], retaining both full attachments.
It also gives T₀ ≤ Z Q′, Z′ ∩ Q ≤ Z_t D and [Z′ ∩ Q,T] ≤ D through
the same full natural cover and literal quotient kernel.
For an actual field-sized critical image, the two complete fixed attachments
now agree or are disjoint complements, each of order q, in the critical
commutator. The full-Sylow branch supplies that critical-image premise.
The literal common-overlap section centralizer now moves that overlap
disjointly from both complete fixed attachments. The point-local order
bound now excludes unequal attachments at actual critical index q under
genuine saturation. Both complete attachments therefore agree, including
in the full-Sylow branch with the critical-order premise discharged.

The post-(6) star argument now makes the moving fixed attachment trivial
while retaining the full fixed core. The actual field-sized pair has a
critical commutator of order q and overlap index q in the literal quotient
by that full fixed core.

This is preparation for the conditional recognition application. The field
restriction and RootClosure's `hrecognition` premise remain open.
Source: MS93 (3.7), pp.872--877; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open ChapterC.BinaryMS.MS93 ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open ChapterC.RankTwo.NonbinarySymplectic
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

/-- The original closure marking gives a single critical configuration with
both full radical actions, both full-core index bounds and both full fixed
attachment displacement bounds. Saturation remains an explicit premise. -/
theorem msPair_saturated_distance_two_configuration
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical) :
    let h := intrinsicMSInput E m hms
    ∃ (z t : Vertex d.radical) (_path : CriticalPath d.radical g (alpha d.radical) z),
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical z t ∧
      ∃ (c : SaturatedDistanceTwo.EdgeMarking h d (alpha d.radical) t)
        (c' : SaturatedDistanceTwo.EdgeMarking h d z t),
        c.action.range = c'.action.range ∧
        (normalizer (c.action.range : Set (Sp E.input.field.Carrier))).pCoreIn 2 = c.action.range ∧
        (normalizer (c'.action.range : Set (Sp E.input.field.Carrier))).pCoreIn 2 = c'.action.range ∧
        (c.action.prod c'.action).ker =
          (Q d.radical (alpha d.radical) ⊓ Q d.radical z).subgroupOf (Q d.radical t) ∧
        (Nat.card c.action.range = Nat.card E.input.field.Carrier ^ 3 ∨
          Nat.card c.action.range = Nat.card E.input.field.Carrier ^ 4) ∧
        (U d.radical (alpha d.radical) ⊔ fixedCore d.radical (alpha d.radical)).relIndex
          (Q d.radical (alpha d.radical)) ≤ Nat.card E.input.field.Carrier ∧
        (U d.radical z ⊔ fixedCore d.radical z).relIndex (Q d.radical z) ≤
          Nat.card E.input.field.Carrier ∧
        ⁅fixedCore d.radical (alpha d.radical),Q d.radical t⁆ ≤
          (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ∧
        (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ≤
          fixedCore d.radical (alpha d.radical) ∧
        ⁅fixedCore d.radical z,Q d.radical t⁆ ≤
          (frattini (Q d.radical z)).map (Q d.radical z).subtype ∧
        (frattini (Q d.radical z)).map (Q d.radical z).subtype ≤ fixedCore d.radical z := by
  let h := intrinsicMSInput E m hms
  obtain ⟨z,t,path,hat,hzt,c,c',hr,hs,hs',hk,hcard⟩ :=
    SaturatedDistanceTwo.exists_paired_full_radical_actions h d g hb hsat
  refine ⟨z,t,path,hat,hzt,c,c',hr,hs,hs',hk,hcard,?_,?_,
    SaturatedDistanceTwo.paired_fixedCore_displacement h d g hb path c c'⟩
  · rw [E.input.field.card_eq]
    exact SaturatedDistanceTwo.core_relIndex_natural_sup_fixed_le h d g hb path.start_color
  · rw [E.input.field.card_eq]
    exact SaturatedDistanceTwo.core_relIndex_natural_sup_fixed_le h d g hb path.end_color

open SaturatedDistanceTwo in
/-- The original closure MS-pair supplies the complete T₀ comparisons at
both endpoints of one critical pair. Its actual product subgroup and its
original quotient marking are unchanged. The field restriction is still
required before this configuration can supply RootClosure's recognition. -/
theorem msPair_saturated_component_radical_comparison
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical) :
    let h := intrinsicMSInput E m hms
    ∃ (z t : Vertex d.radical) (_path : CriticalPath d.radical g (alpha d.radical) z),
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical z t ∧
      ∃ (c : EdgeMarking h d (alpha d.radical) t) (c' : EdgeMarking h d z t),
        c.action.range = c'.action.range ∧
        componentRadical d (alpha d.radical) t ⊔ Q d.radical (alpha d.radical) = Q d.radical t ∧
        componentRadical d z t ⊔ Q d.radical z = Q d.radical t ∧
        componentRadical d (alpha d.radical) t ⊓ Q d.radical (alpha d.radical) =
          U d.radical (alpha d.radical) ∧
        componentRadical d z t ⊓ Q d.radical z = U d.radical z ∧
        componentRadical d (alpha d.radical) t ⊓ fixedCore d.radical (alpha d.radical) =
          U d.radical (alpha d.radical) ⊓ fixedCore d.radical (alpha d.radical) ∧
        componentRadical d z t ⊓ fixedCore d.radical z = U d.radical z ⊓ fixedCore d.radical z ∧
        (componentRadical d (alpha d.radical) t ⊔ fixedCore d.radical (alpha d.radical)).relIndex
          (Q d.radical t) ≤ Nat.card E.input.field.Carrier ∧
        (componentRadical d z t ⊔ fixedCore d.radical z).relIndex (Q d.radical t) ≤
          Nat.card E.input.field.Carrier ∧
        ⁅fixedCore d.radical (alpha d.radical),componentRadical d (alpha d.radical) t⁆ = ⊥ ∧
        ⁅fixedCore d.radical z,componentRadical d z t⁆ = ⊥ ∧
        ((⁅Q d.radical t,Q d.radical t⁆ ≤ Q d.radical (alpha d.radical) ⊓ Q d.radical z ∧
          ⁅Z d.radical z,componentRadical d (alpha d.radical) t⁆ ≤ U d.radical (alpha d.radical) ∧
          ⁅⁅Z d.radical z,componentRadical d (alpha d.radical) t⁆,Q d.radical (alpha d.radical)⁆ = ⊥ ∧
          ⁅Z d.radical (alpha d.radical),componentRadical d z t⁆ ≤ U d.radical z ∧
          ⁅⁅Z d.radical (alpha d.radical),componentRadical d z t⁆,Q d.radical z⁆ = ⊥) ∨
          ∃ S : Sylow 2 (Sp E.input.field.Carrier), (S : Subgroup (Sp E.input.field.Carrier)) =
            c.action.range) ∧
        ((⁅fixedCore d.radical (alpha d.radical),componentRadical d z t⁆ ≤
            U d.radical z ⊓ (frattini (Q d.radical (alpha d.radical))).map
              (Q d.radical (alpha d.radical)).subtype ∧
          ⁅fixedCore d.radical z,componentRadical d (alpha d.radical) t⁆ ≤
            U d.radical (alpha d.radical) ⊓ (frattini (Q d.radical z)).map (Q d.radical z).subtype) ∨
          ∃ S : Sylow 2 (Sp E.input.field.Carrier), (S : Subgroup (Sp E.input.field.Carrier)) =
            c.action.range) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨z,t,path,hat,hzt,c,c',hr,_⟩ :=
    exists_paired_full_radical_actions h d g hb hsat
  refine ⟨z,t,path,hat,hzt,c,c',hr,c.componentRadical_sup_core g (by omega),
    c'.componentRadical_sup_core g (by omega),
    c.componentRadical_inf_core g hb path.start_color,
    c'.componentRadical_inf_core g hb path.end_color,
    c.componentRadical_inf_fixedCore g hb path.start_color,
    c'.componentRadical_inf_fixedCore g hb path.end_color,?_,?_,
    EdgeMarking.fixedCore_centralizes_componentRadical,
    EdgeMarking.fixedCore_centralizes_componentRadical,
    paired_componentRadical_displacement_or_sylow h d g hb hsat path hat hzt c c',
    paired_full_fixedCore_displacement_or_sylow h d g hb hsat path c c'⟩
  · rw [E.input.field.card_eq]
    exact (componentRadical_fixedCore_relIndex h d g hb path.start_color c).2
  · rw [E.input.field.card_eq]
    exact (componentRadical_fixedCore_relIndex h d g hb path.end_color c').2

open SaturatedDistanceTwo in
/-- The original closure quotient supplies both source (3.7)(1) triple
commutators in the parabolic cases and places the critical commutator in
the actual midpoint omega-center. The Sylow branch is retained explicitly. -/
theorem msPair_saturated_source_triples
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical) :
    let h := intrinsicMSInput E m hms
    ∃ (z t : Vertex d.radical) (_path : CriticalPath d.radical g (alpha d.radical) z),
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical z t ∧
      ∃ (c : EdgeMarking h d (alpha d.radical) t) (_c' : EdgeMarking h d z t),
        (⁅Z d.radical z,componentRadical d (alpha d.radical) t⁆ ≤ U d.radical (alpha d.radical) ∧
          ⁅⁅Z d.radical z,Q d.radical (alpha d.radical)⁆,
            componentRadical d (alpha d.radical) t⁆ = ⊥ ∧
          ⁅Z d.radical (alpha d.radical),componentRadical d z t⁆ ≤ U d.radical z ∧
          ⁅⁅Z d.radical (alpha d.radical),Q d.radical z⁆,componentRadical d z t⁆ = ⊥ ∧
          ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ≤ Z d.radical t) ∨
          ∃ S : Sylow 2 (Sp E.input.field.Carrier), (S : Subgroup (Sp E.input.field.Carrier)) =
            c.action.range := by
  let h := intrinsicMSInput E m hms
  obtain ⟨z,t,path,hat,hzt,c,c',_⟩ :=
    exists_paired_full_radical_actions h d g hb hsat
  exact ⟨z,t,path,hat,hzt,c,c',
    paired_source_triples_or_sylow h d g hb hsat path hat hzt c c'⟩

open SaturatedDistanceTwo in
include m in
/-- The core-comparison step of source (3.7)(5) for the literal closure
MS-pair. The source selection must still construct the equal fixed kernels,
equal displacements and contained Z-layer used here. -/
theorem msPair_source_five_core_equality
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical = 2)
    {a z t : Vertex d.radical}
    (ha : color d.radical a = false) (hz : color d.radical z = false)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hfixed : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (hmove : ⁅Z d.radical z,Q d.radical t⁆ = ⁅Z d.radical a,Q d.radical t⁆)
    (hinside : Z d.radical z ≤ Q d.radical a) :
    Q d.radical a = Q d.radical z ∧ X d.radical a = X d.radical z := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) ha hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) hz hzt
  exact source_five_core_equality h d g hb ha hz c c' hfixed hmove hinside


open SaturatedDistanceTwo in
include m in
/-- The contained-core branch of source (3.7)(3) on the literal closure
MS-pair. The source selection must still construct the critical image of
order q and discharge the remaining noncontained-core branch. -/
theorem msPair_source_three_contained_core
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical = 2)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = Nat.card E.input.field.Carrier)
    (hinside : Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    Q d.radical a = U d.radical a ⊔ fixedCore d.radical a ∧
      X d.radical a = Z d.radical a := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  apply source_three_contained_core h d path hb hat c _ hinside
  simpa only [E.input.field.card_eq] using hcritical


open SaturatedDistanceTwo in
include m in
/-- All conclusions of the contained-core subcase of source (3.7)(3),
including both literal overlap indices, for the original closure MS-pair.
The critical image is of order q; the full radical retains its original size. -/
theorem msPair_source_three_contained_core_layers
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical = 2)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = Nat.card E.input.field.Carrier)
    (hinside : Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    Q d.radical a = U d.radical a ⊔ fixedCore d.radical a ∧
      X d.radical a = Z d.radical a ∧
      Z d.radical a = U d.radical a ⊔ Z d.radical t ∧
      (Z d.radical z).relIndex (Z d.radical a) = Nat.card E.input.field.Carrier ∧
      (Z d.radical a).relIndex (Z d.radical z) = Nat.card E.input.field.Carrier := by
  let h := intrinsicMSInput E m hms
  have hc : (Q d.radical z).relIndex (Z d.radical a) = 2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hcritical
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨hQ,hX⟩ := source_three_contained_core h d path hb hat c hc hinside
  refine ⟨hQ,hX,Z_eq_moving_sup_edge_of_critical_index h d path hb hat hc,?_⟩
  simpa only [E.input.field.card_eq] using
    source_three_contained_core_overlap h d path hb hat hzt hc hinside

open SaturatedDistanceTwo in
include m in
/-- The complete Z-layer conclusion of (3.7)(5) in its order-q critical
branch, on the literal closure input. The equal-kernel, equal-displacement
and containment antecedents still belong to the source selection. -/
theorem msPair_source_five_Z_equality_of_critical_index
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical = 2)
    {a z t w : Vertex d.radical} (path : CriticalPath d.radical g a w)
    (hz : color d.radical z = false)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hfixed : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (hmove : ⁅Z d.radical z,Q d.radical t⁆ = ⁅Z d.radical a,Q d.radical t⁆)
    (hinside : Z d.radical z ≤ Q d.radical a)
    (hcritical : (Q d.radical w).relIndex (Z d.radical a) = Nat.card E.input.field.Carrier) :
    Z d.radical a = Z d.radical z := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) hz hzt
  apply source_five_Z_equality_of_critical_index h d hb path hz hat hzt c c' hfixed hmove hinside
  simpa only [E.input.field.card_eq] using hcritical

open SaturatedDistanceTwo in
include m in
/-- The order-q critical branch of (3.7)(1) for the literal closure input,
including the full Sylow radical. The critical image premise remains with
source selection; the full radical has no order-q hypothesis. -/
theorem msPair_critical_root_component_displacements
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical = 2)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = Nat.card E.input.field.Carrier) :
    ⁅Z d.radical z,componentRadical d a t⁆ ≤ U d.radical a ∧
      ⁅⁅Z d.radical z,componentRadical d a t⁆,Q d.radical a⁆ = ⊥ ∧
      ⁅Z d.radical a,componentRadical d z t⁆ ≤ U d.radical z ∧
      ⁅⁅Z d.radical a,componentRadical d z t⁆,Q d.radical z⁆ = ⊥ ∧
      ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical t := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  apply critical_root_component_displacements h d path hb hat hzt c c'
  simpa only [E.input.field.card_eq] using hcritical

open SaturatedDistanceTwo in
include m in
/-- The noncentral branch of source (3.7)(1) for the literal closure pair.
Saturation forces a full Sylow image, and both actual critical images have
order q squared. Both complete central layers retain their fixed attachments
in the midpoint omega-center. The fixed-centralizer count and contradiction
are discharged by `msPair_full_radical_critical_centrality` below. -/
theorem msPair_noncentral_full_radical_large_critical_images
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnc : ¬ ⁅Z d.radical z,Q d.radical t⁆ ≤ Q d.radical a) :
    let h := intrinsicMSInput E m hms
    ∃ (c : EdgeMarking h d a t) (S : Sylow 2 (Sp E.input.field.Carrier)),
      (S : Subgroup (Sp E.input.field.Carrier)) = c.action.range ∧
      Z d.radical a = U d.radical a ⊔ Z d.radical t ∧
      Z d.radical z = U d.radical z ⊔ Z d.radical t ∧
      (Q d.radical z).relIndex (Z d.radical a) = Nat.card E.input.field.Carrier^2 ∧
      (Q d.radical a).relIndex (Z d.radical z) = Nat.card E.input.field.Carrier^2 := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  refine ⟨c,?_⟩
  simpa only [E.input.field.card_eq] using
    noncentral_full_radical_has_large_critical_images h d path hb hsat hat hzt c c' hnc

open SaturatedDistanceTwo in
include m in
/-- Full-radical centrality in both original endpoint quotients, including
the full Sylow case. The fixed-centralizer count and its large-image
contradiction are discharged on the literal intrinsic MS input. -/
theorem msPair_full_radical_critical_centrality
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    ⁅Z d.radical z,Q d.radical t⁆ ≤ Q d.radical a ∧
      ⁅Z d.radical a,Q d.radical t⁆ ≤ Q d.radical z := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  exact full_radical_centralizes_critical_images h d path hb hsat hat hzt c c'

open SaturatedDistanceTwo in
include m in
/-- Both clauses of MS93 (3.7)(1), including the reversed Sylow triples,
on the literal closure input. The full edge and endpoint cores are retained. -/
theorem msPair_saturated_source_one
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    ⁅Z d.radical z,componentRadical d a t⁆ ≤ U d.radical a ∧
      ⁅⁅Z d.radical z,Q d.radical a⁆,componentRadical d a t⁆ = ⊥ ∧
      ⁅Z d.radical a,componentRadical d z t⁆ ≤ U d.radical z ∧
      ⁅⁅Z d.radical a,Q d.radical z⁆,componentRadical d z t⁆ = ⊥ ∧
      ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical t := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  exact paired_source_triples h d g hb hsat path hat hzt c c'

open SaturatedDistanceTwo in
include m in
/-- The literal closure MS-pair has the full natural/fixed centralizer bound
and both actual edge-center decompositions, without an order-q premise. -/
theorem msPair_distance_two_full_core_layers
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    Q d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) ≤
      U d.radical z ⊔ fixedCore d.radical z ∧
    Z d.radical a = U d.radical a ⊔ Z d.radical t ∧
    Z d.radical z = U d.radical z ⊔ Z d.radical t := by
  let h := intrinsicMSInput E m hms
  exact ⟨critical_core_centralizer_le_moving_sup_fixed h d path hb,
    Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat,
    Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt⟩

open SaturatedDistanceTwo in
include m in
/-- The small-movement subcase of MS93 (3.7)(2) on the original closure
quotient. The remaining large-movement branch is not assumed away. -/
theorem msPair_saturated_source_two_small_movement
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsmall : (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ Nat.card E.input.field.Carrier^2) :
    ⁅Z d.radical z,Q d.radical a⁆ ≤ Z d.radical t := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  exact source_two_of_small_core_movement h d g hb hsat path hat hzt c c'
    (by simpa only [E.input.field.card_eq] using hsmall)

open SaturatedDistanceTwo in
include m in
/-- The source (3.7)(2) reduction on the literal closure quotient: either
the full-core displacement lies in the midpoint center, or the remaining
large-movement branch has field-sized critical images and the actual T₀
factorization. Its fixed-core contradiction remains to be proved. -/
theorem msPair_saturated_source_two_reduction
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    ⁅Z d.radical z,Q d.radical a⁆ ≤ Z d.radical t ∨
      (Nat.card E.input.field.Carrier^2 <
        (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z) ∧
      (Q d.radical z).relIndex (componentRadical d a t) = Nat.card E.input.field.Carrier ∧
      (Q d.radical z).relIndex (U d.radical a) = Nat.card E.input.field.Carrier ∧
      (Q d.radical z).relIndex (Z d.radical a) = Nat.card E.input.field.Carrier ∧
      (Q d.radical a).relIndex (Z d.radical z) = Nat.card E.input.field.Carrier ∧
      componentRadical d a t ⊔ Q d.radical z = U d.radical a ⊔ Q d.radical z ∧
      componentRadical d a t = U d.radical a ⊔ (componentRadical d a t ⊓ Q d.radical z)) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  simpa only [E.input.field.card_eq] using source_two_reduction h d g hb hsat path hat hzt c c'

open SaturatedDistanceTwo in
include m in
/-- The large-movement branch on the literal closure quotient retains both
complete fixed attachments in its actual critical commutator, with equal
orders and the source fixed-core intersection estimate. -/
theorem msPair_saturated_source_two_paired_fixed_layers
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : Nat.card E.input.field.Carrier^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    let W := ⁅Z d.radical a,Z d.radical z⁆
    A ⊔ A' ≤ W ∧ W ≤ U d.radical a ⊓ U d.radical z ∧
      Nat.card W = Nat.card E.input.field.Carrier * Nat.card A ∧ Nat.card A = Nat.card A' ∧
      W ⊓ ⁅Z d.radical z,fixedCore d.radical a⁆ ≤ A := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hl : (2^E.input.field.degree)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z) := by
    simpa only [E.input.field.card_eq] using hlarge
  simpa only [E.input.field.card_eq] using
    source_two_large_paired_fixed_layers h d g hb hsat path hat hzt c c' hl

open SaturatedDistanceTwo in
include m in
/-- The original closure quotient satisfies the full displacement-order
bound from MS93 (3.7)(2), retaining the actual first fixed attachment. -/
theorem msPair_saturated_source_two_displacement_card
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : Nat.card E.input.field.Carrier^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    Nat.card (⁅Z d.radical z,fixedCore d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) ≤
      Nat.card E.input.field.Carrier * Nat.card
        (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
          Subgroup (FreeAmalgam d.radical)) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hl : (2^E.input.field.degree)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z) := by
    simpa only [E.input.field.card_eq] using hlarge
  simpa only [E.input.field.card_eq] using
    source_two_large_displacement_card h d g hb hsat path hat hzt c c' hl

open SaturatedDistanceTwo in
include m in
/-- The literal closure MS-pair has field-sized critical images throughout
the large-movement branch.  The first index comes from the source movement
comparison and the reciprocal index from the same path reversal, while the
original saturated radical and both edge markings remain unchanged. -/
theorem msPair_saturated_source_two_large_critical_indices
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : Nat.card E.input.field.Carrier^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)) :
    let h := intrinsicMSInput E m hms
    ∃ (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t),
      c.action.range = c'.action.range ∧
      (Q d.radical z).relIndex (Z d.radical a) = Nat.card E.input.field.Carrier ∧
      (Q d.radical a).relIndex (Z d.radical z) = Nat.card E.input.field.Carrier := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hl : (2^E.input.field.degree)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) := by
    simpa only [E.input.field.card_eq] using hlarge
  obtain ⟨ha,hz⟩ := source_two_large_critical_indices h d g hb hsat path hat hzt c c' hl
  simpa only [E.input.field.card_eq] using ⟨c,c',
    c.action_range.trans c'.action_range.symm,ha,hz⟩

open SaturatedDistanceTwo in
include m in
/-- The literal closure quotient satisfies the complete fixed-core step of
MS93 (3.7)(2). The original radical saturation and the full fixed attachment
remain explicit throughout. -/
theorem msPair_saturated_source_two_fixedCore_quadratic
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    (centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) ≤ Nat.card E.input.field.Carrier^2 ∧
      ⁅⁅Z d.radical z,fixedCore d.radical a⁆,fixedCore d.radical a⁆ = ⊥ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  refine ⟨?_, ?_⟩
  · simpa only [E.input.field.card_eq] using
      source_two_fixedCore_movement_le_square h d g hb hsat path hat hzt c c'
  · exact source_two_fixedCore_quadratic h d g hb hsat path hat hzt c c'


open SaturatedDistanceTwo in
include m in
/-- The original closure MS-pair supplies the source-(2) actor bound with
both full core kernels and the genuine radical saturation retained. -/
theorem msPair_saturated_source_two_fixedCore_actor_index
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : Nat.card E.input.field.Carrier^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)) :
    (Q d.radical z).relIndex (fixedCore d.radical a) ≤
      2 * Nat.card E.input.field.Carrier := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hl : (2^E.input.field.degree)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) := by
    simpa only [E.input.field.card_eq] using hlarge
  simpa only [E.input.field.card_eq] using
    source_two_large_fixedCore_actor_index h d g hb hsat path hat hzt c c' hl


open SaturatedDistanceTwo in
include m in
/-- The original closure MS-pair has the source-(2) cubic full-radical
index in the large-movement branch, retaining the entire opposite core. -/
theorem msPair_saturated_source_two_full_radical_card
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : Nat.card E.input.field.Carrier^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)) :
    (Q d.radical z).relIndex (Q d.radical t) =
      Nat.card E.input.field.Carrier^3 := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hl : (2^E.input.field.degree)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) := by
    simpa only [E.input.field.card_eq] using hlarge
  simpa only [E.input.field.card_eq] using
    source_two_large_full_radical_card h d g hb hsat path hat hzt c c' hl


open scoped IsMulCommutative in
open SaturatedDistanceTwo in
include m in
/-- The literal closure MS-pair supplies the original ambient natural
cover with its entire common radical identified as a point radical. -/
theorem msPair_saturated_source_two_radical_point_cover
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : Nat.card E.input.field.Carrier^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)) :
    Nonempty (RadicalPointCover d.radical
      (DistanceTwoRecognition.replacementMovedSection (intrinsicMSInput E m hms) d) E.input.field.degree z t) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hl : (2^E.input.field.degree)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) := by
    simpa only [E.input.field.card_eq] using hlarge
  exact source_two_large_radical_point_cover h d g hb hsat path hat hzt c c' hl


open SaturatedDistanceTwo in
include m in
/-- The original closure MS-pair supplies the source point-radical displacement
squeeze, retaining both complete fixed attachments and the opposite whole fixed core. -/
theorem msPair_saturated_source_two_point_displacement
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : Nat.card E.input.field.Carrier^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    let C := ⁅Z d.radical z,fixedCore d.radical a⁆
    (centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) = Nat.card E.input.field.Carrier^2 ∧
      Nat.card A = Nat.card E.input.field.Carrier ∧
      Nat.card A' = Nat.card E.input.field.Carrier ∧
      Nat.card C = Nat.card E.input.field.Carrier^2 ∧ A ≤ C ∧
      Disjoint C (fixedCore d.radical z) ∧ Disjoint A (fixedCore d.radical z) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hl : (2^E.input.field.degree)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) := by
    simpa only [E.input.field.card_eq] using hlarge
  have hi := source_two_large_fixedCore_movement_eq_square h d g hb hsat path hat hzt c c' hl
  obtain ⟨hA,hA',hC,hAC⟩ := source_two_large_fixed_attachment_displacement_card
    h d g hb hsat path hat hzt c c' hl
  obtain ⟨hCD,hAD⟩ := source_two_large_displacement_disjoint_opposite_fixedCore
    h d g hb hsat path hat hzt c c' hl
  simpa only [E.input.field.card_eq] using ⟨hi,hA,hA',hC,hAC,hCD,hAD⟩

open SaturatedDistanceTwo in
include m in
/-- The printed p.874 fixed-core indices for the literal closure MS-pair,
with both full fixed cores and the original saturated radical retained. -/
theorem msPair_saturated_source_two_fixedCore_indices
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : Nat.card E.input.field.Carrier^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)) :
    let q := Nat.card E.input.field.Carrier
    let T₀ := componentRadical d a t
    let D₀ := fixedCore d.radical a
    let D₁ := fixedCore d.radical z
    (Q d.radical z).relIndex D₀ = q ∧
      (T₀ ⊔ D₀).relIndex (Q d.radical t) = q ∧
      D₁.relIndex (D₀ ⊓ Q d.radical z) ≤ q^3 ∧ D₁.relIndex D₀ ≤ q^4 ∧
      (T₀ ⊔ D₁).relIndex D₀ ≤ q^3 ∧ (T₀ ⊔ D₁).relIndex (Q d.radical t) ≤ q^4 := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hl : (2^E.input.field.degree)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) := by
    simpa only [E.input.field.card_eq] using hlarge
  obtain ⟨hD,hr⟩ := source_two_large_fixedCore_exact_indices h d g hb hsat path hat hzt c c' hl
  obtain ⟨h₃,h₄⟩ := source_two_large_fixedCore_overlap_index_le h d g hb hsat path hat hzt c c' hl
  obtain ⟨hD₃,hT₄⟩ := source_two_large_component_fixedCore_index_upper
    h d g hb hsat path hat hzt c c' hl
  simpa only [E.input.field.card_eq] using ⟨hD,hr,h₃,h₄,hD₃,hT₄⟩

open scoped commutatorElement in
open SaturatedDistanceTwo in
include m in
/-- Source (3.7)(2)'s midpoint containment for the actual closure input,
with its original quotient, saturation and both full endpoint cores. -/
theorem msPair_saturated_source_two_midpoint_containment
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    ⁅Z d.radical z,Q d.radical a⁆ ≤ Z d.radical t := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  exact source_two_midpoint_containment h d g hb hsat path hat hzt c c'

open scoped IsMulCommutative in
open SaturatedDistanceTwo in
include m in
/-- The noncontained-core branch of source (3.7)(3), on the literal
Chapter11 input, selects the full plane radical on the same natural cover
and computes both midpoint indices. Its subsequent exclusion remains. -/
theorem msPair_saturated_source_three_noncontained_layers
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier)
    (hnot : ¬ Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    let h := intrinsicMSInput E m hms
    Nonempty (RadicalPlaneCover d.radical (DistanceTwoRecognition.replacementMovedSection h d) E.input.field.degree z t) ∧
      (Z d.radical t).relIndex (Z d.radical a)=(Nat.card E.input.field.Carrier)^2 ∧
      (Z d.radical t).relIndex (Z d.radical z)=(Nat.card E.input.field.Carrier)^2 ∧
      Nat.card ((d.ambient.subgroupOf _).map (DistanceTwoRecognition.componentProjection h))=
        (Nat.card E.input.field.Carrier)^3 := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (Q d.radical z).relIndex (Z d.radical a)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_three_noncontained_layers h d g hb hsat path hat hzt c c' hc hnot

open SaturatedDistanceTwo in
include m in
/-- Source (3.7)(3) is complete in the full Sylow branch of the literal
closure MS-pair; core containment and the actual critical-root size are
proved from that branch, while both full fixed attachments remain. -/
theorem msPair_saturated_source_three_of_full_sylow
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (S : Sylow 2 (Sp E.input.field.Carrier))
    (hS : (S : Subgroup (Sp E.input.field.Carrier))=
      (d.ambient.subgroupOf _).map (DistanceTwoRecognition.componentProjection (intrinsicMSInput E m hms))) :
    Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z ∧
      Q d.radical a=U d.radical a ⊔ fixedCore d.radical a ∧
      X d.radical a=Z d.radical a ∧
      (Z d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier ∧
      (Z d.radical a).relIndex (Z d.radical z)=Nat.card E.input.field.Carrier := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hS' : (S : Subgroup (Sp E.input.field.Carrier))=c.action.range := hS.trans c.action_range.symm
  simpa only [E.input.field.card_eq] using
    source_three_of_full_sylow h d g hb hsat path hat hzt c c' S hS'

open scoped commutatorElement in
open SaturatedDistanceTwo in
include m in
/-- The source-(3) whole-core and component-radical movement comparisons
for the literal closure input. Both complete fixed attachments, the original
quotient marking and the genuine saturation premise remain in force. -/
theorem msPair_saturated_source_three_noncontained_movement
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier)
    (hnot : ¬ Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    ⁅Q d.radical a,Z d.radical z⁆ ≤
        ⁅Z d.radical a,Z d.radical z⁆ ⊔ fixedCore d.radical a ∧
      ⁅Q d.radical t,Z d.radical z⁆=⁅Q d.radical a,Z d.radical z⁆ ∧
      ⁅componentRadical d a t,Z d.radical z⁆=⁅Z d.radical a,Z d.radical z⁆ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (Q d.radical z).relIndex (Z d.radical a)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hcritical
  exact ⟨source_three_whole_core_movement h d path hb hat hzt,
    source_three_noncontained_full_movement h d g hb hsat path hat hzt c c' hc hnot,
    source_three_noncontained_component_movement h d g hb hsat path hat hzt c c' hc hnot⟩

open scoped commutatorElement in
open SaturatedDistanceTwo in
include m in
/-- The component containment and full overlap comparisons of source (3)
for the literal closure MS input. The original field, quotient, saturation
hypothesis and both complete fixed attachments are preserved. -/
theorem msPair_saturated_source_three_noncontained_overlap
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier)
    (hnot : ¬ Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    componentRadical d a t ≤ Z d.radical a ⊔ Q d.radical z ∧
      ⁅Z d.radical z ⊓ Q d.radical a,componentRadical d a t⁆=⊥ ∧
      Z d.radical z ⊓ Q d.radical a ≤ Z d.radical t ⊔ fixedCore d.radical a ∧
      ⁅Z d.radical z ⊓ Q d.radical a,Q d.radical t⁆ ≤ fixedCore d.radical a := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (Q d.radical z).relIndex (Z d.radical a)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hcritical
  have ho := source_three_noncontained_overlap h d g hb hsat path hat hzt c c' hc hnot
  exact ⟨source_three_noncontained_component_containment h d g hb hsat path hat hzt c c' hc hnot,
    ho.1,ho.2,source_three_noncontained_overlap_displacement h d g hb hsat path hat hzt c c' hc hnot⟩

open SaturatedDistanceTwo in
include m in
/-- Source (3.7)(3) for an actual field-sized critical image of the literal
closure MS-pair. The plane-radical contradiction now discharges the former
core-containment premise; both complete fixed attachments remain. -/
theorem msPair_saturated_source_three_of_field_critical
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier) :
    Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z ∧
      Q d.radical a=U d.radical a ⊔ fixedCore d.radical a ∧
      X d.radical a=Z d.radical a ∧
      (Z d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier ∧
      (Z d.radical a).relIndex (Z d.radical z)=Nat.card E.input.field.Carrier := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (Q d.radical z).relIndex (Z d.radical a)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_three_of_field_critical h d g hb hsat path hat hzt c c' hc

open scoped commutatorElement in
open SaturatedDistanceTwo in
include m in
/-- The full fixed-attachment dichotomy of source (4) for an actual
field-sized critical image of the literal closure MS-pair. The maximal
complementary case remains explicit; the full radical can have larger order. -/
theorem msPair_saturated_source_four_fixed_kernels
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    A=A' ∨ Disjoint A A' ∧ Nat.card A=Nat.card E.input.field.Carrier ∧
      Nat.card A'=Nat.card E.input.field.Carrier ∧ A ⊔ A'=⁅Z d.radical a,Z d.radical z⁆ := by
  let h := intrinsicMSInput E m hms
  have hc : (Q d.radical z).relIndex (Z d.radical a)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    critical_fixed_kernels_dichotomy h d path hb hat hzt hc

open scoped commutatorElement in
open SaturatedDistanceTwo in
include m in
/-- The literal full-Sylow branch supplies the critical-image premise of
source (4)'s attachment comparison. Neither attachment is discarded, and
no additional critical-image order is assumed. -/
theorem msPair_saturated_source_four_fixed_kernels_of_full_sylow
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (S : Sylow 2 (Sp E.input.field.Carrier))
    (hS : (S : Subgroup (Sp E.input.field.Carrier))=
      (d.ambient.subgroupOf _).map (DistanceTwoRecognition.componentProjection (intrinsicMSInput E m hms))) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    A=A' ∨ Disjoint A A' ∧ Nat.card A=Nat.card E.input.field.Carrier ∧
      Nat.card A'=Nat.card E.input.field.Carrier ∧ A ⊔ A'=⁅Z d.radical a,Z d.radical z⁆ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hS' : (S : Subgroup (Sp E.input.field.Carrier))=c.action.range := hS.trans c.action_range.symm
  have hc := (critical_indices_eq_field_of_full_sylow h d path hb hat hzt c c' S hS').1
  simpa only [E.input.field.card_eq] using
    critical_fixed_kernels_dichotomy h d path hb hat hzt hc

open scoped commutatorElement in
open SaturatedDistanceTwo in
include m in
/-- The centralizer of the actual common-overlap section moves it disjointly
from both full fixed attachments, with the literal closure quotient retained.
The lower bound needed to finish the complementary-kernel exclusion remains. -/
theorem msPair_saturated_source_four_common_overlap
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier) :
    let V := Z d.radical a ⊓ Z d.radical z
    let W := ⁅Z d.radical a,Z d.radical z⁆
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    ∃ B : Subgroup (FreeAmalgam d.radical), B ≤ Q d.radical t ∧
      (∀ b : FreeAmalgam d.radical,
        b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ v ∈ V, ⁅b,v⁆ ∈ W) ∧
      ⁅V,B⁆ ≤ W ∧ Disjoint ⁅V,B⁆ A ∧ Disjoint ⁅V,B⁆ A' := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (Q d.radical z).relIndex (Z d.radical a)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hcritical
  exact source_four_common_overlap_centralizer h d g hb hsat path hat hzt c c' hc

open SaturatedDistanceTwo in
include m in
/-- The order-q branch of source (4) identifies the full fixed attachments
of the literal closure MS-pair under its genuine saturation hypothesis. -/
theorem msPair_saturated_source_four_equality
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (Q d.radical z).relIndex (Z d.radical a)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hcritical
  exact source_four_of_field_critical h d g hb hsat path hat hzt c c' hc

open SaturatedDistanceTwo in
include m in
/-- The full-Sylow closure branch gives equality of the complete fixed
attachments with its critical-image order proved from the supplied Sylow. -/
theorem msPair_saturated_source_four_equality_of_full_sylow
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (S : Sylow 2 (Sp E.input.field.Carrier))
    (hS : (S : Subgroup (Sp E.input.field.Carrier))=
      (d.ambient.subgroupOf _).map (DistanceTwoRecognition.componentProjection (intrinsicMSInput E m hms))) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  exact source_four_of_full_sylow h d g hb hsat path hat hzt c c' S
    (hS.trans c.action_range.symm)

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The large-critical-image branch supplies both actual plane-radical
covers and the common full displacement for the literal closure MS-pair.
The two complete attachments are retained in R, without asserting equality. -/
theorem msPair_saturated_source_four_large_geometry
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a)) :
    Nonempty (RadicalPlaneCover d.radical
      (replacementMovedSection (intrinsicMSInput E m hms) d) E.input.field.degree a t) ∧
      Nonempty (RadicalPlaneCover d.radical
        (replacementMovedSection (intrinsicMSInput E m hms) d) E.input.field.degree z t) ∧
      (Z d.radical t).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier^2 ∧
      (Z d.radical t).relIndex (Z d.radical z)=Nat.card E.input.field.Carrier^2 ∧
      ⁅Z d.radical a,Q d.radical t⁆=⁅Z d.radical a,Z d.radical z⁆ ∧
      ⁅Z d.radical z,Q d.radical t⁆=⁅Z d.radical a,Z d.radical z⁆ ∧
      (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) ⊔
        (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) ≤
          ⁅Z d.radical a,Z d.radical z⁆ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hc

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The literal closure MS-pair has a full Z-hyperplane whose section
centralizer moves it in a field-sized complement to the entire attachment. -/
theorem msPair_saturated_source_four_large_hyperplane
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=Nat.card E.input.field.Carrier ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_hyperplane_attachment h d g hb hsat path hat hzt c c' hc

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The escaping opposite centralizer on the literal closure hyperplane
fills its fixer modulo the original core. The opposite movement retains
its complete fixed attachment and has exactly q times its order. -/
theorem msPair_saturated_source_four_hyperplane_escape
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z)=Nat.card E.input.field.Carrier)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z) :
    let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
    let Y := Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    Y.relIndex (Z d.radical a)=Nat.card E.input.field.Carrier ∧
      (Q d.radical z).relIndex Y=Nat.card E.input.field.Carrier ∧
      P=Q d.radical z ⊔ Y ∧ ⁅Z d.radical z,P⁆=⁅Z d.radical z,Y⁆ ∧
      A ≤ ⁅X,Z d.radical a⁆ ∧ A.relIndex ⁅X,Z d.radical a⁆=Nat.card E.input.field.Carrier ∧
      Nat.card (⁅X,Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical))=
        Nat.card E.input.field.Carrier * Nat.card A := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  have hi' : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hi
  obtain ⟨hy,hq,hp,hm⟩ := source_four_large_escaping_hyperplane h d g hb hsat path hat hzt c c'
    hc P hP hpoint hi' hescape
  have hmoving := source_four_large_escaping_movement h d g hb hsat path hat hzt c c'
    hc P hP hpoint hi' hescape
  simpa only [E.input.field.card_eq] using And.intro hy (And.intro hq (And.intro hp (And.intro hm hmoving)))

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- For unequal full attachments, the literal closure hyperplane has the
source escape noncontainment, and escape forces both attachments to have
the full field order. The original quotient and full kernels are retained. -/
theorem msPair_saturated_source_four_unequal_hyperplane
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      let A₁ := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=Nat.card E.input.field.Carrier ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      (¬ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z →
        ¬ ⁅X,Z d.radical a⁆ ≤ H₀ ∧
        Nat.card A₁=Nat.card E.input.field.Carrier ∧ Nat.card A₀=Nat.card E.input.field.Carrier) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_unequal_hyperplane h d g hb hsat path hat hzt c c' hc hne


open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The literal closure hyperplane has a field-sized intersection of its two
movements in the unequal-attachment escape branch. Both complete attachments,
the section centralizer and the original quotient/action maps are retained. -/
theorem msPair_saturated_source_four_unequal_intersection
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      let A₁ := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=Nat.card E.input.field.Carrier ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      (¬ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z →
        ¬ ⁅X,Z d.radical a⁆ ≤ H₀ ∧
        Nat.card A₁=Nat.card E.input.field.Carrier ∧ Nat.card A₀=Nat.card E.input.field.Carrier ∧
        Nat.card (⁅X,Z d.radical a⁆ ⊓ H₀ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_unequal_intersection h d g hb hsat path hat hzt c c' hc hne

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- For the literal closure input, every nontrivially moving element in the
escaping opposite centralizer has a commutator outside the root movement.
This applies the full-cover field-span argument with both original attachments
and the actual quotient/action maps. -/
theorem msPair_saturated_source_four_unequal_value_escape
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      let A₁ := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=Nat.card E.input.field.Carrier ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      (¬ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z →
        ¬ ⁅X,Z d.radical a⁆ ≤ H₀ ∧
        Nat.card A₁=Nat.card E.input.field.Carrier ∧ Nat.card A₀=Nat.card E.input.field.Carrier ∧
        Nat.card (⁅X,Z d.radical a⁆ ⊓ H₀ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
        ∀ y ∈ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)),
          (∃ b ∈ Z d.radical z, ⁅b,y⁆ ≠ 1) →
            ∃ b ∈ Z d.radical z, ⁅b,y⁆ ∉ ⁅X,Z d.radical a⁆) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_unequal_value_escape h d g hb hsat path hat hzt c c' hc hne

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- In the escaping unequal-attachment branch of the literal closure input,
the opposite section centralizer equals the pointwise centralizer of the
actual hyperplane and has field index. The full kernels and original
quotient/action maps are retained. -/
theorem msPair_saturated_source_four_unequal_section_centralizer
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      let A₁ := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=Nat.card E.input.field.Carrier ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      (¬ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z →
        ¬ ⁅X,Z d.radical a⁆ ≤ H₀ ∧
        Nat.card A₁=Nat.card E.input.field.Carrier ∧ Nat.card A₀=Nat.card E.input.field.Carrier ∧
        Nat.card (⁅X,Z d.radical a⁆ ⊓ H₀ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
        Z d.radical a ⊓ B=Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
        (Z d.radical a ⊓ B).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_unequal_section_centralizer h d g hb hsat path hat hzt c c' hc hne

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The literal closure hyperplane generates the full common radical
movement. Its field index and the original quotient/action maps are retained. -/
theorem msPair_saturated_source_four_hyperplane_full_movement
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z)=Nat.card E.input.field.Carrier) :
    ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Q d.radical t⁆=
      ⁅Z d.radical a,Z d.radical z⁆ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  have hi' : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hi
  exact source_four_large_hyperplane_full_movement h d g hb hsat path hat hzt c c' hc P hP hi'

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The literal closure common movement has index q squared over the complete
fixed attachment. Its exact order retains that attachment as a factor. -/
theorem msPair_saturated_source_four_displacement_order
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a)) :
    let A := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    let D := ⁅Z d.radical a,Z d.radical z⁆
    A ≤ D ∧ A.relIndex D=Nat.card E.input.field.Carrier^2 ∧
      Nat.card D=Nat.card E.input.field.Carrier^2 * Nat.card A := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_displacement_order h d g hb hsat path hat hzt c c' hc

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- In the escaping unequal-attachment branch of the literal closure input,
the hyperplane has radical movement of order q cubed and an actual radical
commutator outside the opposite movement. -/
theorem msPair_saturated_source_four_unequal_radical_escape
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z)=Nat.card E.input.field.Carrier)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
    Nat.card (⁅X,Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier^3 ∧
      ∃ x ∈ X, ∃ b ∈ Q d.radical t, ⁅x,b⁆ ∉ ⁅X,Z d.radical a⁆ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  have hi' : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hi
  simpa only [E.input.field.card_eq] using
    source_four_large_unequal_radical_escape h d g hb hsat path hat hzt c c' hc P hP hpoint hi' hescape hne

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The literal full hyperplane has a section centralizer of field index in the common radical. -/
theorem msPair_saturated_source_four_hyperplane_section_index
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Nat.card E.input.field.Carrier)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=Nat.card E.input.field.Carrier ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧ B.relIndex (Q d.radical t)=Nat.card E.input.field.Carrier := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_hyperplane_section_index h d g hb hsat path hat hzt c c' hc

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The literal escaping unequal-attachment branch has the full radical factorization and disjoint hyperplane movements, with both original attachments retained. -/
theorem msPair_saturated_source_four_unequal_complement
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Nat.card E.input.field.Carrier)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      let A₁ := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=Nat.card E.input.field.Carrier ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      B.relIndex (Q d.radical t)=Nat.card E.input.field.Carrier ∧
      (¬ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z →
        Nat.card A₁=Nat.card E.input.field.Carrier ∧ Nat.card A₀=Nat.card E.input.field.Carrier ∧
        Q d.radical t=Z d.radical a ⊔ B ∧
        ⁅Z d.radical a,Z d.radical z⁆=⁅X,Z d.radical a⁆ ⊔ ⁅X,B⁆ ∧
        Disjoint ⁅X,Z d.radical a⁆ ⁅X,B⁆) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_unequal_complement h d g hb hsat path hat hzt c c' hc hne

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- In the original closure quotient, marked root selection and the opposite
field-span obstruction force attachment containment under the preceding
source-(4) intersection and complement premises. -/
theorem msPair_saturated_source_four_marked_attachment_le
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (P B : Subgroup (FreeAmalgam d.radical))
    (hmarked : HasMarkedHyperplane (intrinsicMSInput E m hms) d z t P B)
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=Nat.card E.input.field.Carrier)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z)
    (hfull : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier)
    (hHcard : Nat.card (⁅Z d.radical z,P⁆ : Subgroup (FreeAmalgam d.radical))=(Nat.card E.input.field.Carrier)^2)
    (hMnot : ¬ ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ≤ ⁅Z d.radical z,P⁆)
    (hmeet : (⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ⊓
      ⁅Z d.radical z,P⁆ : Subgroup (FreeAmalgam d.radical)) ≠ ⊥)
    (hcomp : Disjoint ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),B⁆) :
    U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ≤
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  have hi' : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z)=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hi
  have hf : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hfull
  have hH : Nat.card (⁅Z d.radical z,P⁆ : Subgroup (FreeAmalgam d.radical))=(2^E.input.field.degree)^2 := by
    simpa only [E.input.field.card_eq] using hHcard
  exact source_four_large_marked_attachment_le h d g hb hsat path hat hzt c c' hc
    P B hmarked hi' hescape hf hH hMnot hmeet hcomp

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The original full attachment meets the hyperplane movement in either
its entirety or the identity, through the literal covering action. -/
theorem msPair_saturated_source_four_full_attachment_dichotomy
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hfull : Nat.card (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier) :
    let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
    let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    A₀ ≤ ⁅X,Z d.radical a⁆ ∨ Disjoint ⁅X,Z d.radical a⁆ A₀ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  have hf : Nat.card (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^E.input.field.degree := by
    simpa only [E.input.field.card_eq] using hfull
  exact source_four_large_full_attachment_dichotomy h d g hb hsat path hat hzt c c' hc P hP hf

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The original closure quotient's full attachment is the exact intersection
of the two marked movements. The order and complement premises are derived. -/
theorem msPair_saturated_source_four_marked_attachment_intersection
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (P B : Subgroup (FreeAmalgam d.radical))
    (hmarked : HasMarkedHyperplane (intrinsicMSInput E m hms) d z t P B)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z) :
    U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) =
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ⊓
        ⁅Z d.radical z,P⁆ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  exact source_four_large_marked_attachment_intersection h d g hb hsat path hat hzt c c' hc
    hne P B hmarked hescape

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The actual preceding plane cover constructs the marked hyperplane with
its exact intersection comparison, in the literal original MS quotient. -/
theorem msPair_saturated_source_four_unequal_marked_intersection
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      HasMarkedHyperplane (intrinsicMSInput E m hms) d z t P B ∧ Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=Nat.card E.input.field.Carrier ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧ B.relIndex (Q d.radical t)=Nat.card E.input.field.Carrier ∧
      (¬ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z →
        A₀=⁅X,Z d.radical a⁆ ⊓ H₀) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_unequal_marked_intersection h d g hb hsat path hat hzt c c' hc hne

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The symmetric full-cover comparison excludes an escaping opposite
centralizer in the original closure quotient when the attachments differ. -/
theorem msPair_saturated_source_four_marked_centralizer_le
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (P B : Subgroup (FreeAmalgam d.radical))
    (hmarked : HasMarkedHyperplane (intrinsicMSInput E m hms) d z t P B) :
    Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  exact source_four_large_marked_centralizer_le h d g hb hsat path hat hzt c c' hc
    hne P B hmarked

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The actual plane cover constructs a hyperplane with nonescaping opposite
centralizer and the full complement data in the original MS quotient. -/
theorem msPair_saturated_source_four_unequal_nonescaping_hyperplane
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      HasMarkedHyperplane (intrinsicMSInput E m hms) d z t P B ∧ Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=Nat.card E.input.field.Carrier ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧ B.relIndex (Q d.radical t)=Nat.card E.input.field.Carrier ∧
      Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_unequal_nonescaping_hyperplane h d g hb hsat path hat hzt c c' hc hne

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The literal closure section centralizer has field index and supplies
every element of the complete hyperplane complement as an individual
commutator of the original two Z-layers. -/
theorem msPair_saturated_source_four_unequal_nonescaping_section
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      let Y := Z d.radical a ⊓ B
      HasMarkedHyperplane (intrinsicMSInput E m hms) d z t P B ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      X.relIndex (Z d.radical z)=Nat.card E.input.field.Carrier ∧
      (∀ y : FreeAmalgam d.radical, y ∈ Y ↔ y ∈ Z d.radical a ∧ ∀ x ∈ X, ⁅y,x⁆ ∈ H₀) ∧
      Y.relIndex (Z d.radical a)=Nat.card E.input.field.Carrier ∧ (Q d.radical z).relIndex Y=Nat.card E.input.field.Carrier ∧
      Q d.radical t=P ⊔ Z d.radical a ∧ B=P ⊔ Y ∧
      ⁅X,B⁆=⁅X,Y⁆ ∧ Disjoint ⁅X,Y⁆ A₀ ∧
      Nat.card (⁅X,Y⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card E.input.field.Carrier ∧
      H₀=⁅X,Y⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      ∃ y ∈ Y, y ∉ Q d.radical z ∧ ∀ v ∈ ⁅X,Y⁆, ∃ x ∈ X, ⁅y,x⁆=v := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_four_large_unequal_nonescaping_section h d g hb hsat path hat hzt c c' hc hne


open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- Source (3.7)(4) in the literal Chapter11 MS quotient: both complete
fixed attachments agree, without a critical-image-size assumption. -/
theorem msPair_saturated_source_four_fixed_attachments
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  exact source_four_fixed_attachments h d g hb hsat path hat hzt c c'

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The Q₂ element-centralizer count for the original Chapter11 quotient:
the complete core remains the kernel, and both U and Z have fixed index q. -/
theorem msPair_saturated_source_five_large_element_centralizer
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (x : FreeAmalgam d.radical) (hx : x ∈ Z d.radical a) (hne : x ∉ Z d.radical t) :
    let C := Q d.radical t ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
    (Q d.radical a).relIndex C=Nat.card E.input.field.Carrier ∧
      (centralizer (C : Set (FreeAmalgam d.radical))).relIndex (U d.radical a)=Nat.card E.input.field.Carrier ∧
      (centralizer (C : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_five_large_element_centralizer h d g hb hsat path hat hzt c c' hc x hx hne

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- Source (5)'s full omega-layer displacement count in the same original
Chapter11 quotient, modulo its entire component-fixed attachment. -/
theorem msPair_saturated_source_five_large_omega_displacement
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a))
    (x : FreeAmalgam d.radical) (hx : x ∈ Z d.radical a) (hne : x ∉ Z d.radical t) :
    let C := Q d.radical t ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
    (Q d.radical a).relIndex C=Nat.card E.input.field.Carrier ∧
      (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))).relIndex
        ⁅X d.radical a,C⁆=Nat.card E.input.field.Carrier := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_five_large_omega_displacement h d g hb hsat path hat hzt c c' hc x hx hne

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The full-omega fixed-vector criterion used in source (5), on the
literal Chapter11 quotient and with its complete component-fixed attachment. -/
theorem msPair_source_five_fixed_omega_mem_Z
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (B : Subgroup (FreeAmalgam d.radical)) (hBT : B ≤ Q d.radical t)
    (hcard : (Q d.radical a).relIndex B=Nat.card E.input.field.Carrier)
    (hmove : (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅X d.radical a,B⁆ ≤ Nat.card E.input.field.Carrier)
    (x : FreeAmalgam d.radical) (hx : x ∈ X d.radical a)
    (hfix : x ∈ centralizer (B : Set (FreeAmalgam d.radical))) :
    x ∈ Z d.radical a := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) ha hat
  apply source_five_fixed_omega_mem_Z h d g hb ha hat c B hBT
    (by simpa only [E.input.field.card_eq] using hcard)
    (by simpa only [E.input.field.card_eq] using hmove) x hx hfix

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- MS93 (3.7)(5) for the original Chapter11 MS quotient: equal full
attachments, equal radical displacements and the printed Z-containment
force equality of the generated Z-layers, including the Q₂ branch. -/
theorem msPair_saturated_source_five_Z_equality
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t v : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hvt : Adjacent d.radical v t) (hv : color d.radical v=false)
    (hfixed : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical v ⊓ centralizer (Ltilde d.radical v : Set (FreeAmalgam d.radical)))
    (hmove : ⁅Z d.radical v,Q d.radical t⁆=⁅Z d.radical a,Q d.radical t⁆)
    (hinside : Z d.radical v ≤ Q d.radical a) :
    Z d.radical v=Z d.radical a := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  obtain ⟨cv⟩ := exists_edgeMarking h d g (by omega) hv hvt
  exact source_five_Z_equality h d g hb hsat path hat hzt hvt hv c c' cv hfixed hmove hinside

open scoped commutatorElement IsMulCommutative in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The first actual element in source (6), selected from the opposite
Z-layer in the original Chapter11 MS quotient. Its centralizer on the full
first Z-layer is exactly the common midpoint omega-center. -/
theorem msPair_saturated_source_six_regular_element
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧ Z d.radical a ⊓
      centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  exact source_six_exists_regular_element h d g hb hsat path hat hzt c c' hc

open scoped commutatorElement IsMulCommutative Pointwise in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The regular element and moving conjugator in source (6), selected on
the literal Chapter11 quotient with its entire endpoint kernel. -/
theorem msPair_saturated_source_six_moving_regular_element
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤
      (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧ Z d.radical a ⊓
      centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t ∧
      ∃ y ∈ stabilizer d.radical a,
        y ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
        y ∈ normalizer (x • (Q d.radical a : Set (FreeAmalgam d.radical))) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q d.radical a ∧
        y ∉ normalizer (((Z d.radical z ⊔ Q d.radical a) :
          Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  exact source_six_exists_moving_regular_element h d g hb hsat path hat hzt c c' hc

open scoped commutatorElement IsMulCommutative Pointwise in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- Source (6)'s induced midpoint action and new critical pair for the
literal Chapter11 quotient. If its image is not already field-sized, the
same commuting elements give both centralizer indices q. -/
theorem msPair_saturated_source_six_critical_configuration
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧
      Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t ∧
      ∃ y ∈ stabilizer d.radical a, ∃ k ∈ stabilizer d.radical t,
        (∀ u ∈ Q d.radical t, (MulAut.conj k) u=(MulAut.conj y) u) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q d.radical a ∧ Commute x (y*x*y⁻¹) ∧
        y ∉ normalizer (((Z d.radical z ⊔ Q d.radical a) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        Nonempty (CriticalPath d.radical g (act d.radical k⁻¹ z) z) ∧
        ((Q d.radical z).relIndex (Z d.radical (act d.radical k⁻¹ z))=Nat.card E.input.field.Carrier ∨
          (y*x*y⁻¹ ∉ Q d.radical z ∧
            (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))).relIndex
              (Z d.radical z)=Nat.card E.input.field.Carrier ∧
            (Q d.radical (act d.radical k⁻¹ z)).relIndex
              (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical)))=Nat.card E.input.field.Carrier ∧
            (centralizer ((Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))) :
              Set (FreeAmalgam d.radical))).relIndex (Z d.radical (act d.radical k⁻¹ z))=Nat.card E.input.field.Carrier)) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_six_field_pair_or_centralizer_configuration h d g hb hsat path hat hzt c c' hc

open scoped commutatorElement IsMulCommutative Pointwise in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The source-(6) whole-core displacement comparison on the literal
Chapter11 quotient. The same selected elements and induced midpoint action
are retained; the complete attachment gives exact displacement index q. -/
theorem msPair_saturated_source_six_whole_core_movement
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧
      Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t ∧
      ∃ y ∈ stabilizer d.radical a, ∃ k ∈ stabilizer d.radical t,
        (∀ u ∈ Q d.radical t, (MulAut.conj k) u=(MulAut.conj y) u) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q d.radical a ∧ Commute x (y*x*y⁻¹) ∧
        y ∉ normalizer (((Z d.radical z ⊔ Q d.radical a) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        Nonempty (CriticalPath d.radical g (act d.radical k⁻¹ z) z) ∧
        ((Q d.radical z).relIndex (Z d.radical (act d.radical k⁻¹ z))=Nat.card E.input.field.Carrier ∨
          (y*x*y⁻¹ ∉ Q d.radical z ∧
            (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))).relIndex
              (Z d.radical z)=Nat.card E.input.field.Carrier ∧
            (Q d.radical (act d.radical k⁻¹ z)).relIndex
              (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical)))=Nat.card E.input.field.Carrier ∧
            (centralizer ((Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))) :
              Set (FreeAmalgam d.radical))).relIndex (Z d.radical (act d.radical k⁻¹ z))=Nat.card E.input.field.Carrier ∧
            (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))).relIndex
              ⁅Q d.radical (act d.radical k⁻¹ z),
                Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))⁆ = Nat.card E.input.field.Carrier ∧
            ⁅Q d.radical (act d.radical k⁻¹ z),
                Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))⁆ ⊔
              (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) ≠
                ⁅Z d.radical z,Q d.radical t⁆)) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_six_field_pair_or_small_whole_core_movement h d g hb hsat path hat hzt c c' hc

open scoped commutatorElement IsMulCommutative Pointwise in
open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The exact source-(6) centralizer index on the whole moved core, with
all selected elements, original quotient maps and full attachments retained. -/
theorem msPair_saturated_source_six_whole_core_centralizer
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : Nat.card E.input.field.Carrier^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧
      Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t ∧
      ∃ y ∈ stabilizer d.radical a, ∃ k ∈ stabilizer d.radical t,
        (∀ u ∈ Q d.radical t, (MulAut.conj k) u=(MulAut.conj y) u) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q d.radical a ∧ Commute x (y*x*y⁻¹) ∧
        y ∉ normalizer (((Z d.radical z ⊔ Q d.radical a) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        Nonempty (CriticalPath d.radical g (act d.radical k⁻¹ z) z) ∧
        ((Q d.radical z).relIndex (Z d.radical (act d.radical k⁻¹ z))=Nat.card E.input.field.Carrier ∨
          (y*x*y⁻¹ ∉ Q d.radical z ∧
            (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))).relIndex
              (Z d.radical z)=Nat.card E.input.field.Carrier ∧
            (Q d.radical (act d.radical k⁻¹ z)).relIndex
              (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical)))=Nat.card E.input.field.Carrier ∧
            (centralizer ((Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))) :
              Set (FreeAmalgam d.radical))).relIndex (Z d.radical (act d.radical k⁻¹ z))=Nat.card E.input.field.Carrier ∧
            (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))).relIndex
              ⁅Q d.radical (act d.radical k⁻¹ z),
                Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))⁆ = Nat.card E.input.field.Carrier ∧
            ⁅Q d.radical (act d.radical k⁻¹ z),
                Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))⁆ ⊔
              (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) ≠
                ⁅Z d.radical z,Q d.radical t⁆ ∧
            (centralizer ((Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))) :
              Set (FreeAmalgam d.radical))).relIndex (Q d.radical (act d.radical k⁻¹ z))=Nat.card E.input.field.Carrier)) := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hc : (2^E.input.field.degree)^2 ≤ (Q d.radical z).relIndex (Z d.radical a) := by
    simpa only [E.input.field.card_eq] using hcritical
  simpa only [E.input.field.card_eq] using
    source_six_field_pair_or_whole_core_centralizer h d g hb hsat path hat hzt c c' hc

open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- Source (3.7)(6) selects an actual field-sized critical pair for the
literal intrinsic MS quotient, using only saturation and distance two. -/
theorem msPair_saturated_source_six_field_critical_pair
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical) :
    ∃ a z, Nonempty (CriticalPath d.radical g a z) ∧
      (Q d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier := by
  let h := intrinsicMSInput E m hms
  simpa only [E.input.field.card_eq] using source_six_exists_field_critical_pair h d g hb hsat

open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The whole-core consequence of source (6), with the complete fixed core
and original quotient retained for the Chapter11 endgame. -/
theorem msPair_saturated_source_six_core_decomposition
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    Q d.radical a=U d.radical a ⊔ fixedCore d.radical a := by
  exact source_six_core_decomposition (intrinsicMSInput E m hms) d g hb hsat ha

open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The post-(6) star argument removes the moving attachment in the literal
intrinsic MS configuration, while preserving its full fixed core. -/
theorem msPair_saturated_source_moving_attachment_eq_bot
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))=⊥ :=
  source_moving_fixed_attachment_eq_bot (intrinsicMSInput E m hms) d g hb hsat ha

open SaturatedDistanceTwo DistanceTwoRecognition in
include m in
/-- The original Chapter11 MS quotient supplies the actual field-sized pair,
whole-core factors, unquotiented commutator order and full-kernel quotient
overlap required by the source endgame. -/
theorem msPair_saturated_source_field_critical_preparation
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical) :
    ∃ a z t : Vertex d.radical, ∃ _path : CriticalPath d.radical g a z,
      Adjacent d.radical a t ∧ Adjacent d.radical z t ∧
      (Q d.radical z).relIndex (Z d.radical a)=Nat.card E.input.field.Carrier ∧
      Q d.radical a=U d.radical a ⊔ fixedCore d.radical a ∧
      Disjoint (U d.radical a) (fixedCore d.radical a) ∧
      Nat.card (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical))=
        Nat.card E.input.field.Carrier ∧
      (P1Comparison.layerImage d a (Z d.radical z)).relIndex
        (P1Comparison.layerImage d a (Z d.radical a))=Nat.card E.input.field.Carrier := by
  let h := intrinsicMSInput E m hms
  simpa only [E.input.field.card_eq] using source_field_critical_preparation h d g hb hsat

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
