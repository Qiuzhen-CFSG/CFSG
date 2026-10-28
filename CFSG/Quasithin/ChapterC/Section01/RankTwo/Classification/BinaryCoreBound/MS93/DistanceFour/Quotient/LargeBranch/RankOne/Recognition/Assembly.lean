module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Requirements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed

/-!
# Assembling recognition from the remaining starred-layer calculations

Transport preserves the actual quotient map and its marked ambient action
when two midpoint orbit spans agree. This reduces recognition to critical
segments through beta. The final conditional theorem then consumes the
escaping compatible frame of (4) and the dimension-six and seed construction
of (5), applying the proved clause (3) and converting dimension into the
literal relative index 64.

The two geometric construction premises are still to be proved. Keeping this
assembly downstream of Seed avoids changing its shared transport imports.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(3)--(5), pp.910--912.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  {common : CommonFacts R source geometry}

/-- Transport the literal quotient along equality of ambient orbit spans.
The map, exact relative kernel and original dual marking are retained. -/
noncomputable def SpanQuotient.of_span_eq {c d : Vertex R}
    (h : orbitSpan c = orbitSpan d) (q : SpanQuotient source common d) :
    SpanQuotient source common c where
  quotient := q.quotient.comp (inclusion h.le)
  onto := by
    intro w
    obtain ⟨x, hx⟩ := q.onto w
    exact ⟨⟨x, h.ge x.property⟩, hx⟩
  kernel := by
    rw [← MonoidHom.comap_ker, q.kernel]
    rfl
  action m x y hy := q.action m ((inclusion h.le) x)
    ((inclusion h.le) y) hy

/-- A proof on critical segments through beta suffices for every critical
segment. The same ambient span carries the same marked dual quotient. -/
theorem spanRecognition_of_base_edge [Finite M]
    (h : ∀ s : CriticalSegment geometry, ¬ s.SmallIntersection →
      Adjacent R (beta R) s.middle →
      orbitSpan s.middle ≤ Q R s.middle ∧
        Nonempty (SpanQuotient source common s.middle) ∧
          (Z R (alpha R)).relIndex (VStar R geometry (alpha R) (beta R)) = 64) :
    SpanRecognition source common := by
  intro s hs
  obtain ⟨g, hg, hgb⟩ := exists_segment_on_base_edge s
  generalize ht : translateSegment s g hg = t at hgb
  have hm : t.middle = act R g s.middle := by
    rw [← ht]
    rfl
  have hns : ¬ t.SmallIntersection := by
    rw [← ht]
    exact fun hsmall => hs ((translateSegment_small_iff s g hg).mp hsmall)
  obtain ⟨hkernel, ⟨q⟩, hindex⟩ := h t hns hgb
  have hQ : orbitSpan s.middle ≤ Q R s.middle := by
    rw [hm] at hkernel
    exact (orbitSpan_le_kernel_act_iff s.middle g hg).mp hkernel
  have he : orbitSpan s.middle = orbitSpan t.middle := by
    rw [hm, orbitSpan_act_eq s.middle g hg]
  exact ⟨hQ, ⟨SpanQuotient.of_span_eq he q⟩, hindex⟩

/-- Reduce the source recognition to its two remaining geometric steps.
The first input constructs a compatible incident frame and proves (4).
The second proves the dimension and seed assertions in (5), conditionally
on that noncontainment. Both inputs must be discharged before claiming
the unconditional source theorem. -/
theorem spanRecognition_of_star_escape_and_dimension [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4)
    (hescape : ∀ (s : CriticalSegment geometry), ¬ s.SmallIntersection →
      Adjacent R (beta R) s.middle →
      ∀ d : LayerModule source (V R (alpha R)),
        ∃ f : Seed.Frame source, Seed.Compatible f s ∧
          ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hconstruction : ∀ (s : CriticalSegment geometry), ¬ s.SmallIntersection →
      Adjacent R (beta R) s.middle →
      ∀ (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source),
        Seed.Compatible f s →
        (¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle) →
        Module.finrank (ZMod 2) (d.subspace (VStar R geometry (alpha R) (beta R))) = 6 ∧
          Nonempty (Seed.Input (geometry := geometry) d f s.middle)) :
    SpanRecognition source common := by
  apply spanRecognition_of_base_edge
  intro s hs hbc
  obtain ⟨d⟩ := exists_radiusModule common radius
  obtain ⟨f, hf, hnot⟩ := hescape s hs hbc d
  obtain ⟨hdim, ⟨x⟩⟩ := hconstruction s hs hbc d f hf hnot
  obtain ⟨_, hQ, hquot⟩ := Seed.conjugate_seed_recognition common radius hb s hs hbc d f hf x
  refine ⟨hQ, hquot, ?_⟩
  rw [d.subspace_relIndex _ (Flags.star_le_radius geometry _ _), hdim]
  norm_num

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
