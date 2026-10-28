module
public import Mathlib.Algebra.Module.Submodule.Equiv
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Interface
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Candidate
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Splitting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Geometry.Parabolics

/-!
# The literal second star as an adjacent parabolic span

The estimates fix Y under the first ordered residual and the second core.
Their join is the full first parabolic. The actual edge star lies in Y,
so its entire image is fixed by that parabolic. The second parabolic
normalizes its core, making every adjacent edge image core-fixed already.
Thus the second star is precisely the span of these adjacent images.
The edge images generate the whole starred module under SL3(2).

This supplies the geometric inputs to the homogeneous restriction calculation;
it does not yet calculate the resulting natural rank-one coordinates.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(5), pp.911--912,
with the adjacent fixed-space definition on pp.905 and 910.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction

section Linear
variable {W X : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X]

private theorem fixed_join (ρ : Representation (ZMod 2) SL W)
    (H K : Subgroup SL) (v : W)
    (hH : v ∈ fixedSpace ρ H) (hK : v ∈ fixedSpace ρ K) :
    v ∈ fixedSpace ρ (H ⊔ K) := by
  let F : Subgroup SL := {
    carrier := {a | ρ a v = v}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      change ρ (a * b) v = v
      change ρ a v = v at ha
      change ρ b v = v at hb
      rw [map_mul, Module.End.mul_apply, hb, ha]
    inv_mem' := by
      intro a ha
      change ρ a⁻¹ v = v
      change ρ a v = v at ha
      simpa only [ρ.inv_self_apply] using (congrArg (ρ a⁻¹) ha).symm }
  have h : H ⊔ K ≤ F := sup_le (fun a ha => hH ⟨a, ha⟩) (fun a ha => hK ⟨a, ha⟩)
  exact fun g => h g.property

/-- An equivariant linear map carries a literal orbit span to the orbit span
of the image, retaining the same subgroup of SL3(2). -/
theorem orbitSpace_map (ρ : Representation (ZMod 2) SL W)
    (σ : Representation (ZMod 2) SL X) (l : W →ₗ[ZMod 2] X)
    (hl : ∀ g v, l (ρ g v) = σ g (l v))
    (H : Subgroup SL) (A : Submodule (ZMod 2) W) :
    (Seed.orbitSpace ρ H A).map l = Seed.orbitSpace σ H (A.map l) := by
  unfold Seed.orbitSpace
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨g, hg, v, hv, rfl⟩, rfl⟩
    exact ⟨g, hg, l v, ⟨v, hv, rfl⟩, (hl g v).symm⟩
  · rintro ⟨g, hg, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨ρ g v, ⟨g, hg, v, hv, rfl⟩, hl g v⟩

private theorem orbitSpace_invariant (ρ : Representation (ZMod 2) SL W)
    (H : Subgroup SL) (A : Submodule (ZMod 2) W) (g : SL) (hg : g ∈ H) :
    ∀ v ∈ Seed.orbitSpace ρ H A, ρ g v ∈ Seed.orbitSpace ρ H A := by
  change Seed.orbitSpace ρ H A ≤ (Seed.orbitSpace ρ H A).comap (ρ g)
  apply Submodule.span_le.mpr
  rintro _ ⟨h, hh, v, hv, rfl⟩
  change ρ g (ρ h v) ∈ Seed.orbitSpace ρ H A
  rw [← Module.End.mul_apply, ← map_mul]
  exact Submodule.subset_span ⟨g * h, H.mul_mem hg hh, v, hv, rfl⟩

end Linear

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem radius_normalized (m : M) :
    embedM R m ∈ normalizer (V R (alpha R)) := by
  apply DistanceEight.V_normalized R (alpha R)
  rw [alpha, stabilizer_m_base]
  exact ⟨m, rfl⟩

private theorem subspace_fixed_of_commutator
    (d : LayerModule source (V R (alpha R)))
    (T : Subgroup (FreeAmalgam R)) (H : Subgroup M)
    (hc : ⁅T, H.map (embedM R)⁆ ≤ Z R (alpha R)) :
    d.subspace T ≤ fixedSpace d.representation (H.map source.projection) := by
  rw [commutator_comm] at hc
  intro v hv g
  obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff T v).mp hv
  obtain ⟨m, hm, he⟩ := g.property
  change d.representation (g : SL) (d.projection x).toAdd = (d.projection x).toAdd
  rw [← he]
  exact (d.fixed_iff_commutator_mem m (radius_normalized m) x).mpr
    (hc (commutator_mem_commutator (mem_map_of_mem _ hm) hx))

/-- The two actual fixation estimates generate the full first parabolic. -/
theorem Y_le_first_fixed [Finite M]
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (s : CriticalSegment geometry) (hest : Estimates d f s) :
    d.subspace (Sections.fixedPreimage s.middle) ≤
      fixedSpace d.representation ((f.parabolic false).map source.projection) := by
  rw [← f.actor_eq false, Seed.actor_image_generation]
  intro v hv
  exact fixed_join d.representation _ _ v
    (subspace_fixed_of_commutator d _ _ hest.Y_fixed hv)
    (subspace_fixed_of_commutator d _ _
      ((commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans hest.span_fixed) hv)

/-- The literal edge image is fixed by the full first parabolic, using the
source section calculation that places the edge star in Y. -/
theorem edge_le_first_fixed [Finite M] (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s) :
    d.subspace (edgeStar R geometry (alpha R) (beta R)) ≤
      fixedSpace d.representation ((f.parabolic false).map source.projection) :=
  (d.subspace_mono (Escape.edgeStar_le_fixedPreimage common radius hb s hbc d)).trans
    (Y_le_first_fixed d f s hest)

private theorem firstStar_eq_map (d : LayerModule source (V R (alpha R))) (m : M) :
    Seed.firstTildeStar (geometry := geometry) d m =
      (d.subspace (edgeStar R geometry (alpha R) (beta R))).map
        (d.representation (source.projection m)) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff _ v).mp hv
    obtain ⟨y, hy, he⟩ := hx
    have hyV : y ∈ V R (alpha R) :=
      (Flags.edgeStar_le_star geometry _ _).trans (Flags.star_le_radius geometry _ _) hy
    refine ⟨(d.projection ⟨y, hyV⟩).toAdd,
      (d.mem_subspace_iff _ _).mpr ⟨⟨y, hyV⟩, hy, rfl⟩, ?_⟩
    exact (d.action m ⟨y, hyV⟩ x he.symm).symm
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff _ v).mp hv
    let y : V R (alpha R) := ⟨embedM R m * x * (embedM R m)⁻¹,
      (mem_normalizer_iff.mp (radius_normalized (R := R) m) x).mp x.property⟩
    exact (d.mem_subspace_iff _ _).mpr ⟨y, mem_map_of_mem _ hx, d.action m x y rfl⟩

private theorem secondCore_one (f : Seed.Frame source) : Seed.secondCore f 1 = f.core true := by
  have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id M := by ext m; simp
  simp only [Seed.secondCore, he, map_id]

/-- Every adjacent first star is already fixed by the second core. The
intersection in the definition of the second star therefore loses no vectors. -/
theorem adjacent_le_second_core_fixed [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s) (p : f.parabolic true) :
    Seed.firstTildeStar (geometry := geometry) d p ≤
      fixedSpace d.representation ((f.core true).map source.projection) := by
  rw [firstStar_eq_map]
  rintro _ ⟨v, hv, rfl⟩
  have hvfix : v ∈ fixedSpace d.representation ((f.core true).map source.projection) :=
    fun g => edge_le_first_fixed common radius hb s hbc d f hest hv
      ⟨g, map_mono (f.core_le_parabolic true false) g.property⟩
  have hn : source.projection p ∈ normalizer ((f.core true).map source.projection) :=
    le_normalizer_map _ (mem_map_of_mem _ (f.core_normalized true p.property))
  intro a
  have ha : (source.projection p)⁻¹ * (a : SL) * source.projection p ∈
      (f.core true).map source.projection := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer _).inv_mem hn) a).mp a.property
  have he := congrArg (d.representation (source.projection p)) (hvfix ⟨_, ha⟩)
  change d.representation (source.projection p)
    (d.representation ((source.projection p)⁻¹ * (a : SL) * source.projection p) v) =
      d.representation (source.projection p) v at he
  change d.representation (a : SL) (d.representation (source.projection p) v) = _
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left,
    mul_assoc, inv_mul_cancel, mul_one] using he

/-- The actual adjacent fixed-space sum is precisely the second-parabolic
orbit span of the literal edge image. No dimension or model witness is used. -/
theorem secondStar_eq_orbitSpace [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s) :
    Seed.secondTildeStar (geometry := geometry) d f 1 =
      Seed.orbitSpace d.representation ((f.parabolic true).map source.projection)
        (d.subspace (edgeStar R geometry (alpha R) (beta R))) := by
  have hterm (p : f.parabolic true) :
      Seed.firstTildeStar (geometry := geometry) d (1 * p) ⊓
        fixedSpace d.representation ((Seed.secondCore f 1).map source.projection) =
      (d.subspace (edgeStar R geometry (alpha R) (beta R))).map
        (d.representation (source.projection p)) := by
    rw [one_mul, secondCore_one, inf_eq_left.mpr
      (adjacent_le_second_core_fixed common radius hb s hbc d f hest p), firstStar_eq_map]
  unfold Seed.secondTildeStar
  simp_rw [hterm]
  apply le_antisymm
  · apply iSup_le
    intro p
    rintro _ ⟨v, hv, rfl⟩
    exact Submodule.subset_span ⟨source.projection p, mem_map_of_mem _ p.property, v, hv, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨p, hp, rfl⟩, v, hv, rfl⟩
    exact (le_iSup (fun q : f.parabolic true =>
      (d.subspace (edgeStar R geometry (alpha R) (beta R))).map
        (d.representation (source.projection q))) ⟨p, hp⟩) ⟨v, hv, rfl⟩

/-- The actual edge image, now viewed inside the starred module. -/
noncomputable def edgeSpace (d : LayerModule source (V R (alpha R))) :
    Submodule (ZMod 2) (starRepresentation (geometry := geometry) d).toSubmodule :=
  (d.subspace (edgeStar R geometry (alpha R) (beta R))).comap
    (starRepresentation (geometry := geometry) d).toSubmodule.subtype

/-- The inclusion of the starred module sends this edge space onto the
original edge image, with no quotient or projection changed. -/
theorem edgeSpace_map (d : LayerModule source (V R (alpha R))) :
    (edgeSpace (geometry := geometry) d).map
      (starRepresentation (geometry := geometry) d).toSubmodule.subtype =
      d.subspace (edgeStar R geometry (alpha R) (beta R)) := by
  apply Submodule.map_comap_eq_self
  rw [Submodule.range_subtype]
  exact d.subspace_mono (Flags.edgeStar_le_star geometry _ _)

/-- In the actual starred action the edge space is fixed by the literal
first model parabolic. This is the orientation-selecting premise. -/
theorem edgeSpace_le_fixed [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s) :
    edgeSpace (geometry := geometry) d ≤
      fixedSpace (starRepresentation (geometry := geometry) d).toRepresentation
        (modelParabolic f.flag f.first) := by
  intro v hv g
  apply Subtype.ext
  have he := edge_le_first_fixed common radius hb s hbc d f hest hv
  rw [Seed.frame_parabolic_image] at he
  exact he g

/-- The SL3(2) translates of the actual edge space generate the entire
starred module; this is the definition of the ambient starred subgroup,
transported through the supplied quotient. -/
theorem edgeSpace_generates (d : LayerModule source (V R (alpha R))) :
    Seed.orbitSpace (starRepresentation (geometry := geometry) d).toRepresentation
      ⊤ (edgeSpace (geometry := geometry) d) = ⊤ := by
  let ds := starLayer (geometry := geometry) d
  let C := Seed.orbitSpace ds.representation ⊤ (edgeSpace (geometry := geometry) d)
  have hE : edgeStar R geometry (alpha R) (beta R) ≤ ds.preimage C := by
    intro x hx
    have hxS := Flags.edgeStar_le_star geometry (alpha R) (beta R) hx
    apply (ds.mem_preimage_iff C x).mpr
    refine ⟨hxS, ?_⟩
    have hv : (ds.projection ⟨x, hxS⟩).toAdd ∈ edgeSpace (geometry := geometry) d :=
      (d.mem_subspace_iff _ _).mpr ⟨_, hx, rfl⟩
    exact Submodule.subset_span ⟨1, mem_top _, _, hv, by simp⟩
  have hnorm : stabilizer R (alpha R) ≤ normalizer (ds.preimage C) := by
    have hS : (⊤ : Subgroup M).map (embedM R) ≤ normalizer
        (VStar R geometry (alpha R) (beta R)) := by
      rw [← MonoidHom.range_eq_map]
      simpa only [alpha, stabilizer_m_base, Mbar] using
        Flags.star_normalized geometry (alpha R) (beta R)
    have hn := ds.preimage_normalized C ⊤ hS (fun m _ v hv =>
      orbitSpace_invariant ds.representation ⊤ _ _ (mem_top _) v hv)
    simpa only [← MonoidHom.range_eq_map, alpha, stabilizer_m_base, Mbar] using hn
  have hSC : VStar R geometry (alpha R) (beta R) ≤ ds.preimage C :=
    iSup_conjugates_le_of_le_normalizer _ _ _ hE hnorm
  apply top_unique
  intro v _
  obtain ⟨x, rfl⟩ := ds.onto (Multiplicative.ofAdd v)
  exact ((ds.mem_preimage_iff C x).mp (hSC x.property)).2

/-- The second-parabolic span inside the actual starred module. -/
noncomputable def secondOrbit (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) :
    Submodule (ZMod 2) (starRepresentation (geometry := geometry) d).toSubmodule :=
  Seed.orbitSpace (starRepresentation (geometry := geometry) d).toRepresentation
    (modelParabolic f.flag (!f.first)) (edgeSpace (geometry := geometry) d)

/-- Inclusion into the radius quotient identifies the model orbit space
with the literal second-star fixed-space sum. -/
theorem secondOrbit_map [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s) :
    (secondOrbit (geometry := geometry) d f).map
      (starRepresentation (geometry := geometry) d).toSubmodule.subtype =
      Seed.secondTildeStar (geometry := geometry) d f 1 := by
  have he := orbitSpace_map
    (starRepresentation (geometry := geometry) d).toRepresentation
    d.representation (starRepresentation (geometry := geometry) d).toSubmodule.subtype
    (fun _ _ => rfl) (modelParabolic f.flag (!f.first)) (edgeSpace (geometry := geometry) d)
  rw [edgeSpace_map] at he
  refine he.trans ?_
  rw [secondStar_eq_orbitSpace common radius hb s hbc d f hest, Seed.frame_parabolic_image]
  rfl

/-- The literal second star is linearly the adjacent orbit space in the
same starred action; the map is just subtype inclusion in both directions. -/
noncomputable def secondStarEquivOrbit [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s) :
    (Seed.secondTildeStar (geometry := geometry) d f 1) ≃ₗ[ZMod 2]
      secondOrbit (geometry := geometry) d f :=
  ((Submodule.equivMapOfInjective _ (Submodule.injective_subtype _)
    (secondOrbit (geometry := geometry) d f)).trans
      (LinearEquiv.ofEq _ _ (secondOrbit_map common radius hb s hbc d f hest))).symm

/-- The preceding equivalence preserves the original radius-quotient vector. -/
theorem secondStarEquivOrbit_apply [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s) (v : Seed.secondTildeStar (geometry := geometry) d f 1) :
    ((secondStarEquivOrbit common radius hb s hbc d f hest v :
      (starRepresentation (geometry := geometry) d).toSubmodule) : d.Space) = v := by
  exact Submodule.map_equivMapOfInjective_symm_apply
    (starRepresentation (geometry := geometry) d).toSubmodule.subtype
    (Submodule.injective_subtype _) (secondOrbit (geometry := geometry) d f)
    ((LinearEquiv.ofEq _ _ (secondOrbit_map common radius hb s hbc d f hest)).symm v)

/-- The linear identification intertwines the full parabolic on every
actual lift of the specified SL2(2) quotient action. -/
theorem secondStarEquivOrbit_action [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s) (m : f.parabolic true)
    (v : Seed.secondTildeStar (geometry := geometry) d f 1) :
    (secondStarEquivOrbit common radius hb s hbc d f hest
      (secondRankOneAction d f (parabolicQuotient f true m) v) :
        (starRepresentation (geometry := geometry) d).toSubmodule) =
    (starRepresentation (geometry := geometry) d).toRepresentation (source.projection m)
      (secondStarEquivOrbit common radius hb s hbc d f hest v :
        (starRepresentation (geometry := geometry) d).toSubmodule) := by
  apply Subtype.ext
  rw [secondStarEquivOrbit_apply]
  exact (secondRankOneAction_apply d f m v).trans
    (congrArg (d.representation (source.projection m))
      (secondStarEquivOrbit_apply common radius hb s hbc d f hest v).symm)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction
