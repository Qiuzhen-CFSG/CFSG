module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Bounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Fixation.Preparation

/-!
# A marked cubic and reflection for the fixation argument

The interface retains a cubic and an inverting reflection in the original
SL3(2) quotient. It asks that the cubic norm land in the literal Y and that
these two elements, together with the actual edge kernel, generate the full
first actor. It contains no fixation, rank or dimension conclusion.

The final transport below proves full-actor fixation from fixation by the
two displayed generators. The edge kernel already fixes Y by its definition;
no ordered residual is substituted for the full actor.

Source: Meierfrankenfeld--Stellmacher (1993), the opening of (4.6.12)(5),
printed p.911, with the marked notation on p.905 and the sections on p.910.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Fixation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Algebraic data for the same marked module and full first actor. The norm
condition records the two quadratic cubic sections, without asserting fixation. -/
structure CubicData (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (c : Vertex R) where
  cubic : SL
  reflection : SL
  cube : cubic ^ 3 = 1
  square : reflection ^ 2 = 1
  inverts : reflection * cubic = cubic ^ 2 * reflection
  norm_mem : ∀ v : d.Space,
    (d.representation cubic ^ 2 + d.representation cubic + 1 : Module.End (ZMod 2) d.Space) v ∈
      d.subspace (Sections.fixedPreimage c)
  generates : (f.actor false).map source.projection ≤
    (R.map source.projection ⊔ zpowers cubic) ⊔ zpowers reflection

/-- The literal source estimates supply both numerical inputs for any such
marked cubic/reflection, with no assumed dimension or small-displacement fact. -/
theorem CubicData.saturation_inputs
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (cubic : CubicData d f s.middle)
    (hendpoint :
      (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
        (V R (alpha R)) ≤ 4) :
    4 ≤ Module.finrank (ZMod 2) (d.Space ⧸ d.subspace (Sections.fixedPreimage s.middle)) ∧
      Module.finrank (ZMod 2) (LinearMap.range (d.representation cubic.reflection - 1)) ≤ 2 :=
  ⟨fixedPreimage_quotient_finrank_ge_four common radius hb s hs hbc d,
    involution_displacement_le_two_of_endpoint_bound common s d hendpoint
      cubic.reflection cubic.square⟩

/-- Fixation by the displayed cubic and reflection, together with the defining
edge fixation, implies the requested full first-actor commutator containment. -/
theorem CubicData.first_actor_fixed
    (common : CommonFacts R source geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) (c : Vertex R)
    (cubic : CubicData d f c)
    (hfixed : ∀ v ∈ d.subspace (Sections.fixedPreimage c),
      d.representation cubic.cubic v = v ∧ d.representation cubic.reflection v = v) :
    ⁅Sections.fixedPreimage c, (f.actor false).map (embedM R)⁆ ≤ Z R (alpha R) := by
  have hfull : d.subspace (Sections.fixedPreimage c) ≤
      fixedSpace d.representation ((f.actor false).map source.projection) := by
    intro v hv
    let F : Subgroup SL := {
      carrier := {g | d.representation g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro g h hg hh
        change d.representation (g * h) v = v
        change d.representation g v = v at hg
        change d.representation h v = v at hh
        rw [map_mul, Module.End.mul_apply, hh, hg]
      inv_mem' := by
        intro g hg
        change d.representation g⁻¹ v = v
        change d.representation g v = v at hg
        simpa only [d.representation.inv_self_apply] using
          (congrArg (d.representation g⁻¹) hg).symm }
    have hR : R.map source.projection ≤ F := by
      have hvR := hv
      rw [Sections.fixedPreimage_subspace common d c] at hvR
      exact fun g hg => hvR.2 ⟨g, hg⟩
    have hgen : (f.actor false).map source.projection ≤ F :=
      cubic.generates.trans (sup_le (sup_le hR (zpowers_le.mpr (hfixed v hv).1))
        (zpowers_le.mpr (hfixed v hv).2))
    exact fun g => hgen g.property
  have hYV : Sections.fixedPreimage c ≤ V R (alpha R) :=
    (commutatorPreimage_le _ _ _).trans inf_le_left
  apply (commutator_mono
    ((d.subspace_le_iff_le_preimage _ hYV _).mp le_rfl) le_rfl).trans
  apply d.preimage_commutator_le_Z
  · rintro _ ⟨m, _, rfl⟩
    apply DistanceEight.V_normalized R (alpha R)
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  · exact hfull

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Fixation
