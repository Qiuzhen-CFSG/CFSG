module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFive
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.SubgroupTransport

/-!
# Lifting the final relative-centralizer contradiction in MS93 (3.7)

The source takes the quotient by the entire attachment
`D_alpha = C_(Q_alpha)(L_alpha)`. Its distinguished subgroup consists of
those elements of `Z_alpha Z_alpha'` centralizing `Q_1` modulo
`R = [Z_alpha,Z_alpha']`. For a point-parabolic marking, `Q_1` is the
preimage of the point radical under the retained original symplectic
marking and a specified conjugation.

If the image of `Z_alpha'` lies in that relative centralizer, its
`Q_1 ∩ T_beta` commutator maps into the image of R. The full-radical
movement theorem puts both subgroups in `U_alpha'`. Disjointness of
`D_alpha` and `U_alpha'` then lifts the image containment to the original
commutator containment. This contradicts the retained strict movement
bound when R has order q.

The statements retain the literal graph, quotient map, whole fixed
attachment, original field and edge markings. The two-section marking,
order-q relative-centralizer image and its index are the remaining inputs
to the representation argument; this module proves its terminal group step.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.0) notation, printed p.859, and (3.7), printed pp.876--877.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison
variable {G G' : Type*} [Group G] [Group G']

private theorem lift_bound (f : G →* G') (W R M : Subgroup G)
    (hk : Disjoint W f.ker) (hRW : R ≤ W) (hMW : M ≤ W)
    (hm : M.map f ≤ R.map f) : M ≤ R := by
  intro x hx
  obtain ⟨y,hy,he⟩ := hm (mem_map_of_mem f hx)
  have hxy : x * y⁻¹ = 1 := by
    apply (disjoint_iff.mp hk).le
    exact ⟨W.mul_mem (hMW hx) (W.inv_mem (hRW hy)), by
      change f (x*y⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]⟩
  exact (mul_inv_eq_one.mp hxy).symm ▸ hy

private theorem movement_le (f : G →* G') (B J Q₁ W R : Subgroup G) (C : Subgroup G')
    (hk : Disjoint W f.ker) (hRW : R ≤ W) (hMW : ⁅B,J⁆ ≤ W)
    (hJQ : J ≤ Q₁) (hn : C ≤ normalizer (R.map f : Set G'))
    (hB : B.map f ≤ commutatorPreimage C (Q₁.map f) (R.map f)) :
    ⁅B,J⁆ ≤ R := by
  apply lift_bound f W R _ hk hRW hMW
  rw [map_commutator]
  exact (commutator_mono hB (map_mono hJQ)).trans
    (commutator_commutatorPreimage_le C (Q₁.map f) (R.map f) hn)
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

/-- The whole source D-alpha in its endpoint stabilizer. -/
@[expose] def fixedAttachment (a : Vertex d.radical) : Subgroup (stabilizer d.radical a) :=
  (fixedCore d.radical a).subgroupOf (stabilizer d.radical a)

instance fixedAttachment_normal (a : Vertex d.radical) : (fixedAttachment d a).Normal :=
  normal_subgroupOf_of_le_normalizer (DistanceEight.PathCentrality.fixedCore_normalized d.radical a)

/-- The source tilde quotient is taken only inside G-alpha. -/
@[expose] def FixedQuotient (a : Vertex d.radical) :=
  stabilizer d.radical a ⧸ fixedAttachment d a

instance fixedQuotientGroup (a : Vertex d.radical) : Group (FixedQuotient d a) :=
  inferInstanceAs (Group (stabilizer d.radical a ⧸ fixedAttachment d a))

/-- The actual quotient projection by the complete fixed attachment. -/
@[expose] def fixedProjection (a : Vertex d.radical) :
    stabilizer d.radical a →* FixedQuotient d a := QuotientGroup.mk' (fixedAttachment d a)

/-- Restrict an ambient layer to G-alpha and take its actual tilde image. -/
@[expose] def layerImage (a : Vertex d.radical) (B : Subgroup (FreeAmalgam d.radical)) :
    Subgroup (FixedQuotient d a) :=
  (B.subgroupOf (stabilizer d.radical a)).map (fixedProjection d a)

/-- The full point-radical preimage for the retained quotient map and chosen
conjugation. Source use must align this parabolic with its P-one. -/
@[expose] def markedPointCore {a t : Vertex d.radical} (c : EdgeMarking h d a t) (u : Sp F) :
    Subgroup (FreeAmalgam d.radical) :=
  (pointRadicalAmbient.comap ((MulAut.conj u).toMonoidHom.comp c.quotient)).map
    (stabilizer d.radical a).subtype

/-- The commutator form of the source relative centralizer. It requires only
relative normalization of R, rather than normality of R in all of G-alpha. -/
@[expose] def relativeCentralizer {a z t : Vertex d.radical} (c : EdgeMarking h d a t) (u : Sp F) :
    Subgroup (FixedQuotient d a) :=
  commutatorPreimage (layerImage d a (Z d.radical a) ⊔ layerImage d a (Z d.radical z))
    (layerImage d a (markedPointCore h d c u))
    (layerImage d a ⁅Z d.radical a,Z d.radical z⁆)

omit [Finite H] in
theorem layerImage_commutator (a : Vertex d.radical) (B C : Subgroup (FreeAmalgam d.radical))
    (hB : B ≤ stabilizer d.radical a) (hC : C ≤ stabilizer d.radical a) :
    layerImage d a ⁅B,C⁆ = ⁅layerImage d a B,layerImage d a C⁆ := by
  rw [layerImage,SubgroupTransport.subgroupOf_commutator B C hB hC,map_commutator]
  rfl

/-- Once the opposite layer lies in the actual relative centralizer modulo
R, the original commutator is bounded by R. The quotient kernel is the
whole fixed attachment, and its disjointness from the opposite moving
layer is used to lift this bound. -/
theorem source_movement_le_critical_commutator
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) (u : Sp F)
    (hdis : Disjoint (fixedCore d.radical a) (U d.radical z))
    (hcentral : layerImage d a (Z d.radical z) ≤ relativeCentralizer h d (z := z) c u) :
    ⁅Z d.radical z,markedPointCore h d c u ⊓ Q d.radical t⁆ ≤
      ⁅Z d.radical a,Z d.radical z⁆ := by
  let S := stabilizer d.radical a
  let J := markedPointCore h d c u ⊓ Q d.radical t
  have hZaT : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
      g.distance_constant a path.start_color]
    change 1 < g.b d.radical
    omega
  have hZzT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b d.radical
    omega
  have hZaS : Z d.radical a ≤ S := hZaT.trans c.edge_le
  have hZzS : Z d.radical z ≤ S := hZzT.trans c.edge_le
  have hJS : J ≤ S := inf_le_right.trans c.edge_le
  have hmove := full_radical_Z_displacement_le_moving h d g (by omega) path.end_color c'
  have hRW : ⁅Z d.radical a,Z d.radical z⁆ ≤ U d.radical z := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZaT).trans hmove
  have hMW : ⁅Z d.radical z,J⁆ ≤ U d.radical z :=
    (commutator_mono le_rfl inf_le_right).trans hmove
  have hk : Disjoint ((U d.radical z).subgroupOf S) (fixedProjection d a).ker := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hxd : x ∈ fixedAttachment d a := (QuotientGroup.eq_one_iff _).mp hx.2
    exact (disjoint_iff.mp hdis).le ⟨hxd,hx.1⟩
  have hm := movement_le (fixedProjection d a)
    ((Z d.radical z).subgroupOf S) (J.subgroupOf S)
    ((markedPointCore h d c u).subgroupOf S) ((U d.radical z).subgroupOf S)
    ((⁅Z d.radical a,Z d.radical z⁆).subgroupOf S)
    (layerImage d a (Z d.radical a) ⊔ layerImage d a (Z d.radical z)) hk
    (subgroupOf_mono S hRW) (by
      rw [←SubgroupTransport.subgroupOf_commutator _ _ hZzS hJS]
      exact subgroupOf_mono S hMW)
    (subgroupOf_mono S inf_le_left) (by
      change _ ≤ normalizer (layerImage d a ⁅Z d.radical a,Z d.radical z⁆ : Set (FixedQuotient d a))
      rw [layerImage_commutator d a _ _ hZaS hZzS]
      exact sup_le (normalizer_commutator_ge_left _ _) (normalizer_commutator_ge_right _ _)) hcentral
  rw [←SubgroupTransport.subgroupOf_commutator _ _ hZzS hJS] at hm
  intro x hx
  exact hm (show (⟨x,((Subgroup.commutator_le_sup _ _).trans (sup_le hZzS hJS)) hx⟩ : S) ∈
    (⁅Z d.radical z,J⁆).subgroupOf S from hx)

/-- The retained strict source movement rules out equality with the opposite
layer. This proves the terminal commutator contradiction, without assuming
a callback excluding the relative centralizer. The remaining representation
argument must establish the excluded containment from the order-q image. -/
theorem source_relativeCentralizer_not_opposite
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) (u : Sp F)
    (hdis : Disjoint (fixedCore d.radical a) (U d.radical z))
    (hRcard : Nat.card (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) = 2^n)
    (hstrict : 2^n < Nat.card (⁅Z d.radical z,markedPointCore h d c u ⊓ Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical))) :
    ¬ layerImage d a (Z d.radical z) ≤ relativeCentralizer h d (z := z) c u := by
  intro hcentral
  have hle := source_movement_le_critical_commutator h d path hb hat hzt c c' u hdis hcentral
  let : Finite (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Nat.finite_of_card_ne_zero (by rw [hRcard]; exact pow_ne_zero _ (by decide))
  exact (not_lt_of_ge ((Nat.card_le_card_of_injective (inclusion hle)
    (inclusion_injective hle)).trans_eq hRcard)) hstrict

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison
