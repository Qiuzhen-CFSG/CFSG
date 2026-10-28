module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Geometry


/-!
# Transporting the actual midpoint span and its marking

The coset graph carries a right action, so transport by g conjugates groups
by g inverse. We keep this convention in the M-embedding, its range, the
span, and its individual Z-generators. Pullback through that embedding
preserves both quotient subgroups, hence every clause of SingleSection.
An escaping span then supplies a single element transporting the ordered
pair to an escaping generator. Proving that the span escapes is separate.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (2), p.906;
the full c(U)=1 notation is on p.881.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The original M-embedding conjugated by the inverse graph transporter. -/
def transportedEmbedding (g : FreeAmalgam R) : M →* FreeAmalgam R :=
  (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)

/-- The actual conjugate of the midpoint span under that same transporter. -/
noncomputable def transportedSpan (p : FlagCriticalData source geometry i)
    (g : FreeAmalgam R) : Subgroup (FreeAmalgam R) :=
  (midpointSpan p).map (MulAut.conj g⁻¹).toMonoidHom

/-- Transport preserves the faithful embedding of the finite local group. -/
theorem transportedEmbedding_injective (g : FreeAmalgam R) :
    Function.Injective (transportedEmbedding g) :=
  (MulAut.conj g⁻¹).injective.comp (embedM_injective R)

/-- The transported embedding has exactly the transported vertex stabilizer as its image. -/
theorem transportedEmbedding_range (g : FreeAmalgam R) :
    (transportedEmbedding g).range = stabilizer R (act R g (alpha R)) := by
  rw [transportedEmbedding, MonoidHom.range_comp, stabilizer_act, alpha, stabilizer_m_base]
  rfl

/-- Pullback through the transported embedding retains the original numerator. -/
theorem transportedSpan_comap (p : FlagCriticalData source geometry i)
    (g : FreeAmalgam R) :
    (transportedSpan p g).comap (transportedEmbedding g) =
      (midpointSpan p).comap (embedM R) := by
  rw [transportedSpan, transportedEmbedding, ← comap_comap,
    comap_map_eq_self_of_injective (MulAut.conj g⁻¹).injective]

/-- Pullback through the transported embedding retains the original denominator. -/
theorem transportedZ_comap (g : FreeAmalgam R) :
    (Z R (act R g (alpha R))).comap (transportedEmbedding g) =
      (Z R (alpha R)).comap (embedM R) := by
  rw [Z_act, transportedEmbedding, ← comap_comap,
    comap_map_eq_self_of_injective (MulAut.conj g⁻¹).injective]

/-- The transported span is a subgroup of the new vertex radius group. -/
theorem transportedSpan_le_radius (p : FlagCriticalData source geometry i)
    (g : FreeAmalgam R) : transportedSpan p g ≤ V R (act R g (alpha R)) := by
  rw [transportedSpan, V_act]
  exact map_mono (span_le_radius p)

/-- Normalization is by the transported local stabilizer. -/
theorem transportedSpan_normalized (p : FlagCriticalData source geometry i)
    (g : FreeAmalgam R) :
    stabilizer R (act R g (alpha R)) ≤ normalizer (transportedSpan p g) := by
  rw [transportedSpan, stabilizer_act]
  exact (map_mono (span_normalized p)).trans (le_normalizer_map _)

/-- Every generator transports the ordered pair by one actual amalgam element. -/
theorem transportedSpan_eq_iSup (p : FlagCriticalData source geometry i)
    (g : FreeAmalgam R) :
    transportedSpan p g = ⨆ h : stabilizer R (alpha R),
      Z R (act R ((h : FreeAmalgam R)⁻¹ * g) p.middle) := by
  rw [transportedSpan, midpointSpan, Early.Containment.neighborSpan, Subgroup.map_iSup]
  apply iSup_congr
  intro h
  rw [act_mul, Z_act, Z_act, inv_inv]

/-- An escaping span has an escaping generator with the same base image. -/
theorem escapingTransport_of_span (p : FlagCriticalData source geometry i)
    (g : FreeAmalgam R) (t : Vertex R) (hg : act R g (alpha R) = t)
    (hescape : ¬ transportedSpan p g ≤ Q R (alpha R)) :
    ∃ k : FreeAmalgam R, act R k (alpha R) = t ∧
      ¬ Z R (act R k p.middle) ≤ Q R (alpha R) := by
  classical
  rw [transportedSpan_eq_iSup, iSup_le_iff] at hescape
  obtain ⟨h, hh⟩ := not_forall.mp hescape
  refine ⟨(h : FreeAmalgam R)⁻¹ * g, ?_, hh⟩
  rw [act_mul, show act R (h : FreeAmalgam R)⁻¹ (alpha R) = alpha R from
    (stabilizer R (alpha R)).inv_mem h.property]
  exact hg

/-- Transport preserves the entire marked natural-section statement, including
the fixed/moving splitting, because both literal preimages are unchanged. -/
theorem singleSection_transport_iff (p : FlagCriticalData source geometry i)
    (g : FreeAmalgam R) :
    Nonempty (Escape.SingleNaturalSection source.projection source.projection.ker
      (pResidual 2 M) ((transportedSpan p g).comap (transportedEmbedding g))
      ((Z R (act R g (alpha R))).comap (transportedEmbedding g))) ↔ SingleSection p := by
  rw [transportedSpan_comap, transportedZ_comap]
  rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
