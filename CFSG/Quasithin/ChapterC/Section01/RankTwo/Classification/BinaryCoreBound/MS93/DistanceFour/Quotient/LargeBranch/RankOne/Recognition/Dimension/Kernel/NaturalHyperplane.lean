module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Kernel.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Kernel.NaturalHyperplane.Linear
/-!
# The literal midpoint orbit in the unstarred kernel

The first intrinsic core supplies a transvection outside the second core.
The exact kernel of NaturalCopies.quotient makes its lift nontrivial, and
its square lies in the original projection kernel, hence in that second
core. It therefore acts as a nonidentity involution on the two natural copies.

Index two gives a starred intersection of dimension at least three, while
[X₁,V_c] lies in the one-dimensional midpoint image. The hyperplane lemma
first places this ambient line in the starred layer and then places every
second-parabolic translate in X₁ modulo Z_alpha. The original projection,
conjugate-span transport and restored-kernel identity lift the containment
to the literal subgroup X₁. The index premise remains with the source assembly.

Source: Meierfrankenfeld--Stellmacher (1993), Pushing up weak BN-pairs of rank
two, unstarred notation on p.905 and the final seed construction in
(4.6.12)(5), printed p.912.
-/

@[expose] public section

open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem projection_kernel_le_core (f : Seed.Frame source) (i : Bool) :
    source.projection.ker ≤ f.core i := by
  apply le_pCoreIn_of_normalizes
  · rw [source.projection_kernel]
    exact pCore_isPGroup
  · intro x hx
    change source.projection x ∈ modelParabolic f.flag (if i then !f.first else f.first)
    rw [show source.projection x = 1 from hx]
    exact one_mem _
  · exact le_normalizer_of_normal

private theorem core_image_square (f : Seed.Frame source) (i : Bool)
    (x : SL) (hx : x ∈ (f.core i).map source.projection) : x * x = 1 := by
  rw [Seed.frame_core_image, Seed.frame_parabolic_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have h := (ParabolicCoreModel.core_data
    (modelParabolicEquivSymmetric f.flag (if i then !f.first else f.first))).1
  have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.exponent_dvd_p ⟨a, ha⟩
  have hh' := congrArg (fun z : pCore 2 (modelParabolic f.flag (if i then !f.first else f.first)) =>
    ((z : modelParabolic f.flag (if i then !f.first else f.first)) : SL)) hh
  simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one,
    Subgroup.subtype_apply, pow_two] using hh'

private theorem transvection_outside (f : Seed.Frame source) :
    ∃ t : SL, t ∈ (f.core false).map source.projection ∧
      t ∉ (f.core true).map source.projection := by
  obtain ⟨hQP, t, s, ht, hs, hgen⟩ := Seed.frame_transvection_generators f
  refine ⟨t, ht, ?_⟩
  intro htQ
  have hn : s ∈ normalizer ((f.core true).map source.projection) := by
    obtain ⟨m, hm, rfl⟩ := hs
    exact le_normalizer_map _ (mem_map_of_mem _ (f.core_normalized true hm))
  have hle := hgen _ le_rfl htQ (le_normalizer_iff.mp le_rfl _ hn _ htQ)
  have he : (f.parabolic true).map source.projection = (f.core true).map source.projection :=
    le_antisymm hle (map_mono (map_subtype_le _))
  have hc : Nat.card ((f.parabolic true).map source.projection) = 24 := by
    rw [Seed.frame_parabolic_image]
    change Nat.card (modelParabolic f.flag (!f.first)) = 24
    rw [Nat.card_congr (modelParabolicEquivSymmetric f.flag (!f.first)).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [he, f.core_image_card] at hc
  contradiction

private theorem actual_involution {d : LayerModule source (V R (alpha R))}
    {f : Seed.Frame source} (n : NaturalCopies (geometry := geometry) d f) :
    ∃ m : f.parabolic true,
      source.projection m ∈ (f.core false).map source.projection ∧
      n.quotient m ≠ 1 ∧ n.quotient m * n.quotient m = 1 := by
  obtain ⟨t, ht, htQ⟩ := transvection_outside f
  have hQP := (Seed.frame_transvection_generators f).1
  obtain ⟨m, hm, he⟩ := hQP ht
  let m' : f.parabolic true := ⟨m, hm⟩
  have hq (a : f.parabolic true) : n.quotient a = 1 ↔ (a : M) ∈ f.core true := by
    change a ∈ n.quotient.ker ↔ _
    rw [n.kernel]
    constructor
    · intro h
      exact mem_map_of_mem _ h
    · rintro ⟨b, hb, he⟩
      have hba : b = a := Subtype.ext he
      rwa [hba] at hb
  refine ⟨m', ?_, ?_, ?_⟩
  · change source.projection m ∈ _
    rwa [he]
  · intro h
    exact htQ (he ▸ mem_map_of_mem _ ((hq m').mp h))
  · rw [← map_mul]
    apply (hq _).mpr
    apply projection_kernel_le_core f true
    change source.projection (m * m) = 1
    rw [map_mul, he]
    exact core_image_square f false t ht


private noncomputable def coordinateEmbedding
    {d : LayerModule source (V R (alpha R))} {f : Seed.Frame source}
    (n : NaturalCopies (geometry := geometry) d f) :
    NaturalHyperplane.W →ₗ[ZMod 2] d.Space :=
  (Seed.secondTildeStar (geometry := geometry) d f 1).subtype.comp
    n.coordinates.symm.toLinearMap

omit [Finite M] in
private theorem coordinateEmbedding_injective
    {d : LayerModule source (V R (alpha R))} {f : Seed.Frame source}
    (n : NaturalCopies (geometry := geometry) d f) :
    Function.Injective (coordinateEmbedding n) :=
  Subtype.val_injective.comp n.coordinates.symm.injective

omit [Finite M] in
private theorem coordinateEmbedding_action
    {d : LayerModule source (V R (alpha R))} {f : Seed.Frame source}
    (n : NaturalCopies (geometry := geometry) d f) (m : f.parabolic true)
    (v : NaturalHyperplane.W) :
    coordinateEmbedding n (NaturalHyperplane.act (n.quotient m) v) =
      d.representation (source.projection m) (coordinateEmbedding n v) := by
  let w : Seed.secondTildeStar (geometry := geometry) d f 1 :=
    ⟨d.representation (source.projection m) (n.coordinates.symm v),
      secondStar_normalized d f m m.property _ (n.coordinates.symm v).property⟩
  have he : n.coordinates w = NaturalHyperplane.act (n.quotient m) v := by
    ext j i
    have hh := n.action m (n.coordinates.symm v) w rfl j
    simpa only [LinearEquiv.apply_symm_apply, NaturalHyperplane.act, LinearMap.pi_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply] using congrFun hh i
  rw [← he]
  change (n.coordinates.symm (n.coordinates w) : d.Space) = _
  rw [n.coordinates.symm_apply_apply]
  rfl

/-- The index-two unstarred kernel contains the entire literal midpoint orbit.
Nonzero displacement first puts the ambient midpoint line in the starred layer. -/
theorem naturalCopies_midpoint_containments
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) (n : NaturalCopies (geometry := geometry) d f)
    (hindex : (midpointKernel d f s.middle).relIndex (secondPreimage d f) = 2) :
    d.subspace (Z R s.middle) ≤ Seed.secondTildeStar (geometry := geometry) d f 1 ∧
      midpointSpan f s.middle ≤ midpointKernel d f s.middle := by
  classical
  let H := (starredMidpointKernel (geometry := geometry) d f s.middle).map
    n.coordinates.toLinearMap
  have hH : 3 ≤ Module.finrank (ZMod 2) H := by
    rw [show Module.finrank (ZMod 2) H = Module.finrank (ZMod 2)
      (starredMidpointKernel (geometry := geometry) d f s.middle) from
        n.coordinates.finrank_map_eq _]
    exact starredMidpointKernel_finrank_ge_three common s d f n hindex
  have heH (v : NaturalHyperplane.W) (hv : v ∈ H) :
      coordinateEmbedding n v ∈ d.subspace (midpointKernel d f s.middle) := by
    obtain ⟨w, hw, rfl⟩ := hv
    change (n.coordinates.symm (n.coordinates w) : d.Space) ∈ _
    rw [n.coordinates.symm_apply_apply]
    exact hw
  obtain ⟨m, hm, hm0, hm2⟩ := actual_involution n
  have hactor := Seed.midpointActor_eq_first_core common radius hb s hbc f hf
    (Flags.RankOne.flagControl source geometry common hb radius.toEarlyFacts)
  have hbound := midpointKernel_moved_le_line common radius s hbc d f
  rw [hactor] at hbound
  have hmove : ∀ v ∈ H,
      coordinateEmbedding n (NaturalHyperplane.disp (n.quotient m) v) ∈
        d.subspace (Z R s.middle) := by
    intro v hv
    change coordinateEmbedding n (NaturalHyperplane.act (n.quotient m) v - v) ∈ _
    rw [map_sub, coordinateEmbedding_action]
    exact hbound (Submodule.subset_span ⟨source.projection m, hm,
      coordinateEmbedding n v, heH v hv, rfl⟩)
  obtain ⟨v, hv, hv0, hline, horbit⟩ := NaturalHyperplane.line_orbit
    (coordinateEmbedding n) (coordinateEmbedding_injective n) (n.quotient m) hm0 hm2 H hH
    (d.subspace (Z R s.middle)) (Seed.midpoint_line_dimension d radius s hs hbc) hmove
  constructor
  · rw [hline]
    apply Submodule.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    exact (n.coordinates.symm (NaturalHyperplane.disp (n.quotient m) v)).property
  · have hspace : midpointSpace d f s.middle ≤ d.subspace (midpointKernel d f s.middle) := by
      change d.subspace (conjugateSpanBy (Z R s.middle)
        ((f.parabolic true).map (embedM R))) ≤ _
      rw [d.subspace_conjugateSpan _ (Seed.midpoint_Z_le_radius s) _
        ((f.ambient_le true).trans (DistanceEight.V_normalized R (alpha R)))]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩
      rw [hline] at hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [map_smul]
      apply Submodule.smul_mem
      rw [← coordinateEmbedding_action n ⟨a, ha⟩]
      exact heH _ (horbit (n.quotient ⟨a, ha⟩))
    have hpre := (d.subspace_le_iff_le_preimage _ (midpointSpan_le_radius f s) _).mp hspace
    rwa [midpointKernel_preimage common s d f] at hpre

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
