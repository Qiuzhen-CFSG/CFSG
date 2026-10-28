module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalEndpointGeneration
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.G2Three.Recognition

/-!
# The faithful completion on the original aligned cubic normalizers

The large-core branch supplies an actual marked pair, with its Sylow aligner,
original factors and torus actions retained. Its subgroup inclusions form a
faithful generating completion, with whole middle the original Borel.

The already proved ternary completion recognition applies after an isomorphism
of this original amalgam with the literal Atlas parabolic amalgam. This
isomorphism must include both commuting squares; it is the remaining local
construction, not supplied by the endpoint orders or by this record.
The independent strongly-three-embedded branch remains separate.
Source: Aschbacher–Smith I.4.5, printed p.417, and F.4.26, printed p.288.
The imported octonion model retains the attribution in LICENSES/ATLAS.txt.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}

/-- Original aligned endpoints with the actual Sylow and involution markings.
Generation and whole overlap are proved consequences, not fields. -/
structure AlignedCubicPair (t : CubicTorus c) where
  core_order : Nat.card (cubicOddCore c t.x)=243
  aligner : G
  leftReflection : G
  rightReflection : G
  aligner_normalizes : aligner∈normalizer (t.torus.map c.H.subtype:Set G)
  aligned : t.swap.leftCoreExtension.map (MulAut.conj aligner).toMonoidHom=t.leftCoreExtension
  left_mem : leftReflection∈cubicNormalizer c t.x
  right_mem : rightReflection∈(cubicNormalizer (swapFactors c) t.y).map
    (MulAut.conj aligner).toMonoidHom
  left_out : leftReflection∉t.leftCubicBorel
  right_out : rightReflection∉t.leftCubicBorel
  left_order : orderOf leftReflection=2
  right_order : orderOf rightReflection=2
  product_order : orderOf (leftReflection*rightReflection)=6
  left_normalizes : leftReflection∈normalizer (t.torus.map c.H.subtype:Set G)
  right_normalizes : rightReflection∈normalizer (t.torus.map c.H.subtype:Set G)
  left_fixed : MulAut.conj leftReflection (t.z:G)=(t.z:G)
  left_moves : MulAut.conj leftReflection (t.n:G)=(t.z:G)*(t.n:G)
  right_fixed : MulAut.conj rightReflection (MulAut.conj aligner (t.z:G))=
    MulAut.conj aligner (t.z:G)
  right_moves : MulAut.conj rightReflection (MulAut.conj aligner (t.n:G))=
    MulAut.conj aligner ((t.z:G)*(t.n:G))
  distinct_fixed : MulAut.conj aligner (t.z:G)≠(t.z:G)

namespace CubicTorus
/-- Construct the marked pair from the original order243 core, without model maps. -/
theorem nonempty_alignedCubicPair (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) : Nonempty (AlignedCubicPair t) := by
  obtain ⟨a,s,r,haA,ha,_,hs,hr,hsB,hrB,hs2,hr2,hprod,hsA,hrA,hsz,hsn,hrz,hrn,haz⟩ :=
    t.maximal_aligned_endpoint_hexagon_involutions hc
  exact ⟨⟨hc,a,s,r,haA,ha,hs,hr,hsB,hrB,hs2,hr2,hprod,hsA,hrA,hsz,hsn,hrz,hrn,haz⟩⟩
end CubicTorus
namespace AlignedCubicPair
variable {t : CubicTorus c} (d : AlignedCubicPair t)

/-- The literal first cubic normalizer. -/
abbrev leftEndpoint (_d : AlignedCubicPair t) : Subgroup G := cubicNormalizer c t.x
/-- The literal conjugate of the opposite cubic normalizer. -/
abbrev rightEndpoint : Subgroup G :=
  (cubicNormalizer (swapFactors c) t.y).map (MulAut.conj d.aligner).toMonoidHom

/-- Both endpoints generate the original ambient group. -/
theorem generated : d.leftEndpoint ⊔ d.rightEndpoint=⊤ :=
  t.aligned_endpoints_generate d.aligner d.leftReflection d.rightReflection
    d.aligner_normalizes d.left_mem d.right_mem d.left_normalizes d.right_normalizes
    d.left_fixed d.left_moves d.right_fixed d.right_moves d.distinct_fixed

/-- The middle is the whole original Borel, not an arbitrarily selected subgroup. -/
theorem overlap : d.leftEndpoint ⊓ d.rightEndpoint=t.leftCubicBorel :=
  t.maximal_aligned_endpoint_overlap d.core_order d.aligner d.aligned

/-- The original marked subgroup amalgam, with both literal inclusion maps. -/
def amalgam : RankTwoAmalgam d.leftEndpoint t.leftCubicBorel d.rightEndpoint :=
  .ofSubgroups d.leftEndpoint t.leftCubicBorel d.rightEndpoint
    t.leftCubicBorel_le (d.overlap ▸ inf_le_right)

/-- The actual original group is a faithful completion of this original amalgam. -/
def completion : RankTwoAmalgam.FaithfulCompletion d.amalgam (G:=G) :=
  .ofSubgroups d.leftEndpoint t.leftCubicBorel d.rightEndpoint
    t.leftCubicBorel_le (d.overlap ▸ inf_le_right) d.generated

@[simp] theorem completion_left_range : d.completion.left.range=d.leftEndpoint := range_subtype _
@[simp] theorem completion_right_range : d.completion.right.range=d.rightEndpoint := range_subtype _
@[simp] theorem completion_middle_range : d.completion.middle.range=t.leftCubicBorel := range_subtype _

/-- Change to the Atlas marking only using an isomorphism with both commuting squares. -/
def atlasCompletion (e : RankTwoAmalgam.Iso
    (ChapterF.GreenBook.LieModels.G2.amalgam (F:=ZMod 3)) d.amalgam) :
    ChapterF.SourceCompletion.G2Three.Completion G := d.completion.comapIso e

/-- The original completion feeds the proved F.4.26 theorem. Only compatible
local Atlas maps remain explicit; generation and all involution orders are discharged. -/
theorem nonempty_mulEquiv_of_amalgam_iso (e : RankTwoAmalgam.Iso
    (ChapterF.GreenBook.LieModels.G2.amalgam (F:=ZMod 3)) d.amalgam) :
    Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) := by
  apply ChapterF.SourceCompletion.G2Three.Completion.nonempty_mulEquiv_of_orders
    (d.atlasCompletion e) d.leftReflection d.rightReflection
  · simpa only [atlasCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      completion_left_range] using d.left_mem
  · simpa only [atlasCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      completion_right_range] using d.right_mem
  · simpa only [atlasCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range,
      completion_middle_range] using d.left_out
  · simpa only [atlasCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range,
      completion_middle_range] using d.right_out
  · exact d.left_order
  · exact d.right_order
  · exact d.product_order

end AlignedCubicPair
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
