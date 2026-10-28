module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Interface
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.QuadraticDuality
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# The two source budgets on the literal starred representation

The crossing case of (4.6.12)(5) bounds the index of a fixed preimage in
V_alpha. Its image bounds fixed codimension on V_alpha-star/Z_alpha.
The contained case instead bounds the relative order of a commutator in
the star. Duality turns that bound into fixed codimension on the dual.

Both actors are the images, under the supplied source projection, of the
intrinsic two-cores of the chosen parabolics. Each is elementary of order
four. Consequently the actual star or its dual is an FF-module. This
retains both literal denominators and assumes neither dimension six nor
natural coordinates on any layer.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(5), printed p.911.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem frame_core_image_data [Finite M] (f : Seed.Frame source) (i : Bool) :
    IsElementaryTwo ((f.core i).map source.projection) ∧
      rank ((f.core i).map source.projection) = 2 := by
  have hk : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  have he : (f.core i).map source.projection =
      (modelParabolic f.flag (if i then !f.first else f.first)).pCoreIn 2 := by
    change ((f.parabolic i).pCoreIn 2).map source.projection = _
    rw [map_pCoreIn_of_ker_isPGroup source.projection hk]
    congr 1
    exact map_comap_eq_self_of_surjective source.projection_surjective _
  rw [he]
  let P := modelParabolic f.flag (if i then !f.first else f.first)
  let e := (pCore 2 P).equivMapOfInjective P.subtype P.subtype_injective
  have hd := Matrix.PSL3Two.ParabolicCoreModel.core_data
    (modelParabolicEquivSymmetric f.flag (if i then !f.first else f.first))
  let : IsElementaryAbelian 2 (pCore 2 P) := hd.1
  have hc : Nat.card (P.pCoreIn 2) = 4 :=
    (Nat.card_congr e.toEquiv.symm).trans hd.2
  refine ⟨⟨?_, IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective⟩, ?_⟩
  · intro h
    rw [h, Subgroup.card_bot] at hc
    omega
  · change Nat.log 2 (Nat.card (P.pCoreIn 2)) = 2
    rw [hc]
    decide

private theorem fixedCodim_le_of_index [Finite M]
    {S : Subgroup (FreeAmalgam R)} (d : LayerModule source S)
    (hS : S ≤ stabilizer R (alpha R))
    (H : Subgroup M) (hn : H.map (embedM R) ≤ normalizer S)
    (hindex : (commutatorPreimage S (H.map (embedM R)) (Z R (alpha R))).relIndex S ≤ 4) :
    fixedCodim d.representation (H.map source.projection) ≤ 2 := by
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite S := Finite.of_injective (inclusion hS) (inclusion_injective hS)
  let K := commutatorPreimage S (H.map (embedM R)) (Z R (alpha R))
  let W := fixedSpace d.representation (H.map source.projection)
  let F : Subgroup S := W.toAddSubgroup.toSubgroup.comap d.projection
  have hK : ⁅K, H.map (embedM R)⁆ ≤ Z R (alpha R) :=
    commutator_commutatorPreimage_le _ _ _ (hS.trans (Z_normalized R _))
  have hKF : K.subgroupOf S ≤ F := by
    intro x hx
    change ∀ g : H.map source.projection,
      d.representation g.val (d.projection x).toAdd = (d.projection x).toAdd
    intro g
    obtain ⟨m, hm, hmg⟩ := g.property
    rw [← hmg]
    let y : S := ⟨embedM R m * x * (embedM R m)⁻¹,
      le_normalizer_iff.mp hn _ (mem_map_of_mem _ hm) _ x.property⟩
    have hz : y * x⁻¹ ∈ d.projection.ker := by
      rw [d.kernel]
      change ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ Z R (alpha R)
      rw [commutator_comm] at hK
      exact hK (commutator_mem_commutator (mem_map_of_mem _ hm) hx)
    have hq : d.projection y = d.projection x := by
      change d.projection (y * x⁻¹) = 1 at hz
      rwa [map_mul, map_inv, mul_inv_eq_one] at hz
    rw [← d.action m x y rfl, hq]
  have hind : F.index ≤ 4 := (Subgroup.index_antitone hKF).trans hindex
  rw [Subgroup.index_comap_of_surjective _ d.onto, AddSubgroup.index_toSubgroup] at hind
  change Nat.card (d.Space ⧸ W) ≤ 4 at hind
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hind
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hind

private theorem dual_fixedCodim_le_of_index
    {S : Subgroup (FreeAmalgam R)} (d : LayerModule source S)
    (H : Subgroup M) (hn : H.map (embedM R) ≤ normalizer S)
    (hindex : (Z R (alpha R)).relIndex ⁅S, H.map (embedM R)⁆ ≤ 4) :
    fixedCodim d.representation.dual (H.map source.projection) ≤ 2 := by
  have htop : d.preimage ⊤ = S := by
    ext x
    simp only [d.mem_preimage_iff, Submodule.mem_top, exists_prop, and_true]
  have hc : ⁅S, H.map (embedM R)⁆ ≤ S := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp hn
  have he := d.subspace_commutator_preimage ⊤ H hn
  rw [htop] at he
  have hm : Seed.movedSpace d.representation (H.map source.projection) ⊤ =
      Coinvariants.ker (d.representation.comp (H.map source.projection).subtype) := by
    apply congrArg (Submodule.span (ZMod 2))
    ext v
    constructor
    · rintro ⟨g, hg, w, _, rfl⟩
      exact ⟨(⟨g, hg⟩, w), rfl⟩
    · rintro ⟨⟨g, w⟩, rfl⟩
      exact ⟨g, g.property, w, trivial, rfl⟩
  rw [d.subspace_relIndex _ hc, he, hm] at hindex
  have hd := finrank_dual_quotient_invariants
    (d.representation.comp (H.map source.projection).subtype)
  change fixedCodim d.representation.dual (H.map source.projection) = _ at hd
  rw [hd]
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex

/-- The two source intersection cases give an offender on the literal star
or on its contragredient, with their different denominators preserved. -/
theorem star_or_dual_isFFModule_of_estimates [Finite M]
    (common : CommonFacts R source geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (s : CriticalSegment geometry) (hest : Estimates d f s) :
    IsFFModule (starRepresentation (geometry := geometry) d).toRepresentation ∨
      IsFFModule (starRepresentation (geometry := geometry) d).toRepresentation.dual := by
  have hV : V R (alpha R) ≤ stabilizer R (alpha R) :=
    geometry.V_local _ rfl common.large_distance
  by_cases h : ySpan f s.middle ⊓ Q R s.middle ≤ Sections.fixedPreimage s.middle
  · right
    obtain ⟨hA, hr⟩ := frame_core_image_data f false
    refine ⟨(f.core false).map source.projection, hA, ?_⟩
    rw [hr]
    apply dual_fixedCodim_le_of_index (starLayer (geometry := geometry) d) (f.core false)
      ((map_le_range (embedM R) _).trans ?_) (hest.contained_bound h)
    change Mbar R ≤ _
    simpa only [alpha, stabilizer_m_base] using
      Flags.star_normalized geometry (alpha R) (beta R)
  · left
    obtain ⟨hA, hr⟩ := frame_core_image_data f true
    refine ⟨(f.core true).map source.projection, hA, ?_⟩
    rw [hr]
    have hcodim := fixedCodim_le_of_index d hV (f.core true)
      ((map_le_range (embedM R) _).trans (by
        change Mbar R ≤ _
        simpa only [alpha, stabilizer_m_base] using DistanceEight.V_normalized R (alpha R)))
      (hest.crossing_bound h)
    exact (fixedCodim_subrepresentation_le d.representation
      (starRepresentation (geometry := geometry) d) _).trans hcodim
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
