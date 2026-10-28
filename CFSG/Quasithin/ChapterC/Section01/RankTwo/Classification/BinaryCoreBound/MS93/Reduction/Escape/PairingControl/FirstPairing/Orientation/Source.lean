module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!+# The two remaining deductions in the first orientation argument

`FrameAt` aligns the natural subgroup U and the full natural section of V/Z
under one actual quotient projection. Its existence is proved from the earlier
module facts and natural-section input. `SameOrientation` says that their
markings differ by an inner automorphism; its negation constructs an actual
`MovingOrientationAt`, with the correct radical denominator.

`BoundsAt` records the two commutator bounds obtained from the first use of
(1.7)(i). The first has the precise bracket placement [V,[Q,Ltilde]]. The
second involves the fixed preimage B, whereas the pairing input W is Q.
These bounds transport to every M-vertex by amalgam conjugation. Their producer
and the two image-order cases eliminating them remain separate obligations.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), pp.883--884.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation
open RankOnePairing
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The two actual natural sections, with their quotient marking aligned.
This structure does not assert any relation between their orientations. -/
structure FrameAt (a : Vertex R) where
  projection : stabilizer R a →* SL
  naturalU : NaturalFactor projection ⊤ ((U R a).subgroupOf (stabilizer R a)) ⊥
  natural_section : SingleNaturalSection projection
    ((Q R a).subgroupOf (stabilizer R a))
    (pResidual 2 (stabilizer R a))
    ((V R a).subgroupOf (stabilizer R a))
    ((Z R a).subgroupOf (stabilizer R a))

/-- Being inner is the actual equivalence of the two natural orientations,
not an unconnected recognition label. -/
def FrameAt.SameOrientation {a : Vertex R} (f : FrameAt a) : Prop :=
  f.naturalU.marking.symm.trans f.natural_section.natural.marking ∈
    MulAut.innerSubgroup SL

/-- Construct the full opposite coordinates once the shared orientation is
excluded. The moving section and its radical denominator are preserved. -/
noncomputable def FrameAt.movingOrientation {a : Vertex R} (f : FrameAt a)
    (h : ¬ f.SameOrientation) : MovingOrientationAt a where
  projection := f.projection
  naturalU := f.naturalU
  natural_section := f.natural_section
  dual := dualFactorOfNotInner f.naturalU f.natural_section.natural h

/-- The two source bounds following the first quotient application of (1.7).
These are intermediate conclusions to be proved, not source assumptions. -/
structure BoundsAt (geometry : Geometry R) (a : Vertex R) : Prop where
  triple : ⁅V R a, ⁅Q R a, Ltilde R a⁆⁆ ≤ fixedCore R a
  fixed : ⁅B R a (geometry.Z_normal a), Q R a⁆ ≤ fixedCore R a

variable [Finite M] {source : LocalSource L R} {geometry : Geometry R}

/-- Aligning the two natural structures requires no contrary hypothesis. -/
theorem frame_nonempty (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false)
    (s : NaturalSectionAt a (V R a) (Z R a)) : Nonempty (FrameAt a) := by
  obtain ⟨n⟩ := naturalU_nonempty modules a ha s.projection
    s.module_section.projection_surjective s.module_section.projection_kernel
  exact ⟨⟨s.projection, n, s.module_section⟩⟩

/-- Both commutator bounds are covariant under the actual amalgam action. -/
theorem bounds_act_iff (hb : 2 < geometry.b R)
    (g : FreeAmalgam R) (a : Vertex R) (ha : color R a = false) :
    BoundsAt geometry (act R g a) ↔ BoundsAt geometry a := by
  have ht : (⁅V R (act R g a), ⁅Q R (act R g a), Ltilde R (act R g a)⁆⁆ ≤
      fixedCore R (act R g a)) ↔
      ⁅V R a, ⁅Q R a, Ltilde R a⁆⁆ ≤ fixedCore R a := by
    rw [V_act, Q_act, Ltilde_act, fixedCore_act, ← map_commutator,
      ← map_commutator, map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
  have hf : (⁅B R (act R g a) (geometry.Z_normal _), Q R (act R g a)⁆ ≤
      fixedCore R (act R g a)) ↔
      ⁅B R a (geometry.Z_normal a), Q R a⁆ ≤ fixedCore R a := by
    rw [B_act hb g a ha, Q_act, fixedCore_act, ← map_commutator,
      map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
  exact ⟨fun h => ⟨ht.mp h.triple, hf.mp h.fixed⟩,
    fun h => ⟨ht.mpr h.triple, hf.mpr h.fixed⟩⟩

/-- The bounds at one M-vertex supply precisely the bounds needed at the
other vertices in both p.884 image-order cases. -/
theorem bounds_everywhere (hb : 2 < geometry.b R)
    {a : Vertex R} (ha : color R a = false) (h : BoundsAt geometry a)
    (b : Vertex R) (hbcolor : color R b = false) : BoundsAt geometry b := by
  obtain ⟨g, hg⟩ := exists_mVertex_of_color R ha
  obtain ⟨k, hk⟩ := exists_mVertex_of_color R hbcolor
  have he : act R (g⁻¹ * k) a = b := by
    rw [hg, act_mVertex, mul_inv_cancel_left, ← hk]
  exact he ▸ (bounds_act_iff hb (g⁻¹ * k) a ha).mpr h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation
