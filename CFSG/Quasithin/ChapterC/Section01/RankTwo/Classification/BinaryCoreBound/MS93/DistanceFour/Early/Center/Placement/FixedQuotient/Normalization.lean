module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.FixedQuotient.Cover
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.EdgeRadius
public import Theory.GroupTheory.CharacteristicCentralizerSylow
/-!
# The relative normalizer acts on the incident edge radius

The holomorph realizes every automorphism of its kernel R, so the pullback
of V_beta to R is characteristic. The characteristic-image normalizer lemma
therefore gives invariance under the full ambient normalizer of Q_beta.
Conjugation transports this to every edge. Restriction to G_d gives the
relative normalizer G_d intersect N(Q_b) used by the source; no ordinary
edge-stabilizer action is substituted for it.

Source: Meierfrankenfeld--Stellmacher (1993), notation on printed p.881 and
the conjugate-span calculation in (4.6.7), printed p.904.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
open Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem base_kernel_normalizer_le_radius_normalizer
    (common : CommonFacts R source geometry) :
    normalizer (Q R (beta R) : Set (FreeAmalgam R)) ≤
      normalizer (V R (beta R) : Set (FreeAmalgam R)) := by
  let K := (V R (beta R)).comap (embedS R)
  let : K.Characteristic := edgeRadius_comap_characteristic
  have hVS : V R (beta R) ≤ (embedS R).range := by
    have h := ((edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R)).trans
      (radius_le_Q common (alpha R) rfl)).trans
        (Q_le_adjacent_h R rfl (base_adjacent R))
    simpa only [beta, neighborhoodKernel_h_base_eq_Sbar, Sbar] using h
  have hmap : K.map (embedS R) = V R (beta R) := by
    dsimp only [K]
    rw [map_comap_eq]
    exact inf_eq_right.mpr hVS
  have hn := normalizer_le_normalizer_characteristic_map
    (embedM R) (embedM_injective R) R K
  rw [map_map, embedM_comp_subtype, hmap, ← Q_beta R] at hn
  exact hn

/-- The full normalizer of the incident kernel preserves the edge radius. -/
theorem edge_kernel_normalizer_le_radius_normalizer
    (common : CommonFacts R source geometry)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b) :
    normalizer (Q R b : Set (FreeAmalgam R)) ≤
      normalizer (V R b : Set (FreeAmalgam R)) := by
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common R d b).mp hdb
  · have hQ := Q_act R g (beta R)
    have hV := V_act (R := R) g (beta R)
    simp only [beta, act_hVertex, one_mul] at hQ hV
    rw [hQ, hV, ← map_equiv_normalizer_eq, ← map_equiv_normalizer_eq]
    exact map_mono (base_kernel_normalizer_le_radius_normalizer common)
  · change true = false at hd
    cases hd

/-- The relative normalizer used on source p.881 acts on the edge radius. -/
theorem relative_normalizer_normalizes_edge_radius
    (common : CommonFacts R source geometry)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b) :
    stabilizer R d ⊓ normalizer (Q R b : Set (FreeAmalgam R)) ≤
      normalizer (V R b : Set (FreeAmalgam R)) :=
  inf_le_right.trans (edge_kernel_normalizer_le_radius_normalizer common d b hd hdb)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
