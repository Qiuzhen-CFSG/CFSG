module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections

/-!
# Literal layers for the starred dimension calculation

The unstarred second-color layer uses conjugates of V_beta; the starred
layer from Seed uses conjugates of edgeStar. Their inclusion transports
clause (4)'s escape to the unstarred layer. The two spans used in (5) keep
their actual conjugating actors and the same quotient modulo Z_alpha.

Estimates records the separate endpoint/Y-span calculation. NaturalCopies
specifies an equivariant identification with the two natural rank-one
copies. Neither record is constructed here. Their source producers and the
midpoint-kernel calculation remain necessary for the dimension-six theorem.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation on printed p.905 and (4.6.12)(5), pp.911--912.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The unstarred first-color layer, a conjugate of the actual V_beta. -/
noncomputable def firstLayer (m : M) : Subgroup (FreeAmalgam R) :=
  (V R (beta R)).map (MulAut.conj (embedM R m)).toMonoidHom

/-- The unstarred second-color tilde layer from p.905, in the supplied radius quotient. -/
noncomputable def secondLayer (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (m : M) : Submodule (ZMod 2) d.Space :=
  ⨆ p : f.parabolic true,
    d.subspace (firstLayer (m * p)) ⊓
      fixedSpace d.representation ((Seed.secondCore f m).map source.projection)

/-- The literal full-second-actor conjugate span of Y on p.911. -/
noncomputable def ySpan (f : Seed.Frame source) (c : Vertex R) :
    Subgroup (FreeAmalgam R) :=
  conjugateSpanBy (Sections.fixedPreimage c) ((f.actor true).map (embedM R))

/-- The actual second-parabolic conjugate span of Z_c proposed on p.912. -/
noncomputable def midpointSpan (f : Seed.Frame source) (c : Vertex R) :
    Subgroup (FreeAmalgam R) :=
  conjugateSpanBy (Z R c) (f.ambient true)

/-- The image of the canonical midpoint span modulo the original Z_alpha. -/
noncomputable def midpointSpace (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (c : Vertex R) : Submodule (ZMod 2) d.Space :=
  d.subspace (midpointSpan f c)

/-- The geometric estimates used in (4.6.12)(5). These are explicit intermediate
obligations, not a proved source result. The two final fields retain both
intersection cases and their distinct literal denominators. -/
structure Estimates (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (s : CriticalSegment geometry) : Prop where
  endpoint_bound :
    (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
      (V R (alpha R)) ≤ 4
  radius_bound : (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex
    (V R (alpha R)) ≤ 64
  Y_fixed : ⁅Sections.fixedPreimage s.middle, (f.residual false).map (embedM R)⁆ ≤
    Z R (alpha R)
  unstarred_le_span : d.preimage (secondLayer d f 1) ≤ ySpan f s.middle
  span_escape : ¬ ySpan f s.middle ≤ Q R s.middle
  span_fixed : ⁅ySpan f s.middle, (f.core true).map (embedM R)⁆ ≤ Z R (alpha R)
  crossing_bound : (¬ ySpan f s.middle ⊓ Q R s.middle ≤ Sections.fixedPreimage s.middle) →
    (commutatorPreimage (V R (alpha R)) ((f.core true).map (embedM R))
      (Z R (alpha R))).relIndex (V R (alpha R)) ≤ 4
  contained_bound : ySpan f s.middle ⊓ Q R s.middle ≤ Sections.fixedPreimage s.middle →
    (Z R (alpha R)).relIndex
      ⁅VStar R geometry (alpha R) (beta R), (f.core false).map (embedM R)⁆ ≤ 4

/-- An actual full-rank-one quotient and equivariant coordinates on two natural
copies. The kernel is the intrinsic two-core of the supplied parabolic; the
actor is full SL2(2), not its derived subgroup. Constructing this data is a
remaining source calculation, not an assumption of the requested final theorem. -/
structure NaturalCopies (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) where
  quotient : f.parabolic true →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
  onto : Function.Surjective quotient
  kernel : quotient.ker = pCore 2 (f.parabolic true)
  coordinates : (Seed.secondTildeStar (geometry := geometry) d f 1) ≃ₗ[ZMod 2]
    (Fin 2 → Fin 2 → ZMod 2)
  action : ∀ (m : f.parabolic true)
    (v w : Seed.secondTildeStar (geometry := geometry) d f 1),
    (w : d.Space) = d.representation (source.projection m) v →
    ∀ j, coordinates w j = (quotient m).val.mulVec (coordinates v j)

/-- The starred first-color layer is contained in its unstarred counterpart. -/
theorem firstStar_le_firstLayer (m : M) :
    Seed.firstStar geometry m ≤ firstLayer (R := R) m := by
  apply map_mono
  rw [Flags.RankOne.V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
  apply iSup_le
  intro c
  apply iSup_le
  intro hc
  exact le_iSup_of_le c (le_iSup_of_le hc.2 le_rfl)

/-- Taking adjacent core-fixed spans preserves the starred/unstarred inclusion. -/
theorem secondStar_le_secondLayer (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (m : M) :
    Seed.secondTildeStar (geometry := geometry) d f m ≤ secondLayer d f m := by
  apply iSup_le
  intro p
  apply le_iSup_of_le p
  exact inf_le_inf_right _ (d.subspace_mono (firstStar_le_firstLayer (m * p)))

/-- Clause (4) also forces the literal unstarred second layer to escape Q_c. -/
theorem secondLayer_escape (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (c : Vertex R)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R c) :
    ¬ d.preimage (secondLayer d f 1) ≤ Q R c := by
  intro h
  apply hescape
  intro x hx
  obtain ⟨hxV, hxA⟩ := (d.mem_preimage_iff _ x).mp hx
  exact h ((d.mem_preimage_iff _ x).mpr
    ⟨hxV, secondStar_le_secondLayer d f 1 hxA⟩)

/-- The full-second-actor span of Y remains inside the original radius group. -/
theorem ySpan_le_radius (f : Seed.Frame source) (c : Vertex R) :
    ySpan f c ≤ V R (alpha R) := by
  apply conjugateSpanBy_le ((commutatorPreimage_le _ _ _).trans inf_le_left)
  apply le_trans (map_le_range (embedM R) _)
  change Mbar R ≤ _
  simpa only [alpha, stabilizer_m_base] using DistanceEight.V_normalized R (alpha R)

/-- The full second actor normalizes its literal conjugate span of Y. -/
theorem ySpan_normalized (f : Seed.Frame source) (c : Vertex R) :
    (f.actor true).map (embedM R) ≤ normalizer (ySpan f c) :=
  le_normalizer_conjugateSpanBy _ _


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
