module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Lifting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure

/-!
# The canonical moving subgroup of a recognized orbit span

Take the commutator of the full span with the actual local two-residual.
It is normalized by the stabilizer, contains U_alpha, and lies in the core.
The local residual maps onto SL3(2). Every dual vector is a difference of
an orbit vector and its translate, so a marked full-span quotient remains
surjective on this moving subgroup. Its kernel calculation then gives
span = Z_alpha times the moving subgroup.

Only the intersection movingSpan ∩ Z_alpha = U_alpha remains to turn this
canonical subgroup into a CoreLift. This equality is an explicit premise,
not a claimed consequence of a quotient by Z_alpha alone. No equality with
the full coreOrbit, core-center equality, or core order bound is used.

Source: original Meierfrankenfeld--Stellmacher (1993), (4.6.12)(3),(5),
printed pp.910--912; the conversion from the full span to its moving subgroup.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The actual moving subgroup of the full orbit span under the local two-residual. -/
noncomputable def movingSpan (c : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⁅orbitSpan c, Ltilde R (alpha R)⁆

/-- The local residual normalizes the span, so its commutators stay in the span. -/
theorem movingSpan_le_span (c : Vertex R) : movingSpan c ≤ orbitSpan c :=
  le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans (orbitSpan_normalized c))

/-- Both commutator factors are invariant under the actual vertex stabilizer. -/
theorem movingSpan_normalized (c : Vertex R) :
    stabilizer R (alpha R) ≤ normalizer (movingSpan c : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (movingSpan c).map (MulAut.conj g).toMonoidHom = movingSpan c
  have hs := orbitSpan_normalized c hg
  rw [mem_normalizer_iff_map_conj_eq] at hs
  change (orbitSpan c).map (MulAut.conj g).toMonoidHom = orbitSpan c at hs
  have hl := Ltilde_act R g⁻¹ (alpha R)
  have hga : act R g⁻¹ (alpha R) = alpha R := (stabilizer R (alpha R)).inv_mem hg
  rw [hga, inv_inv] at hl
  rw [movingSpan, map_commutator, hs, ← hl]

/-- The full local Z-layer in the span contributes U_alpha to its moving subgroup. -/
theorem U_le_movingSpan [Finite M] (c : Vertex R)
    (hd : (cosetGraph R).dist (alpha R) c = 2) : U R (alpha R) ≤ movingSpan c :=
  commutator_mono (Z_le_orbitSpan_of_distance_two c hd) le_rfl

/-- The radius-kernel containment puts the moving span in the actual commutator core. -/
theorem movingSpan_le_core (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (c : Vertex R) (hd : (cosetGraph R).dist (alpha R) c = 2) :
    movingSpan c ≤ core R (alpha R) :=
  commutator_mono ((orbitSpan_le_radius c
    ((cosetGraph R).dist_comm.trans hd).le).trans
      (Flags.V_le_Q geometry hlarge (alpha R) rfl)) le_rfl

private theorem dual_difference (w : Linear.W) :
    ∃ (g : SL) (v : Linear.W), Linear.dual g v - v = w := by
  obtain ⟨v, hv, hvw⟩ := (show ∀ w : Linear.W, ∃ v, v ≠ 0 ∧ v + w ≠ 0 by decide) w
  obtain ⟨g, hg⟩ := Linear.dual_orbit hv hvw
  exact ⟨g, v, by rw [hg]; abel⟩

private theorem residual_projection_onto [Finite M] (source : LocalSource L R) (g : SL) :
    ∃ m ∈ L, source.projection m = g := by
  have hm := congrArg (Subgroup.map source.projection) source.residual_sup_core
  rw [Subgroup.map_sup, ← source.projection_kernel, Subgroup.map_ker_self,
    sup_bot_eq, map_top_of_surjective _ source.projection_surjective] at hm
  exact hm.ge (mem_top g)

variable {source : LocalSource L R} {geometry : Geometry R}
  {common : CommonFacts R source geometry}

namespace SpanQuotient
variable {c : Vertex R} (q : SpanQuotient source common c)

/-- Every dual vector is the image of a commutator with an actual residual element. -/
theorem moving_onto [Finite M] :
    Function.Surjective (q.quotient.comp (inclusion (movingSpan_le_span c))) := by
  intro w
  obtain ⟨g, v, hgv⟩ := dual_difference w.toAdd
  obtain ⟨m, hmL, hmg⟩ := residual_projection_onto source (common.natural.marking.symm g)
  have hmg' : common.natural.marking (source.projection m) = g := by simp [hmg]
  have hm : embedM R m ∈ Ltilde R (alpha R) := by
    rw [Ltilde_alpha, source.residual]
    exact mem_map_of_mem _ hmL
  have hmS : embedM R m ∈ stabilizer R (alpha R) := map_subtype_le _ hm
  obtain ⟨x, hx⟩ := q.onto (Multiplicative.ofAdd v)
  let y : orbitSpan c := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
    (mem_normalizer_iff.mp (orbitSpan_normalized c hmS) _).mp x.property⟩
  let z : orbitSpan c := y * x⁻¹
  have hz : (z : FreeAmalgam R) ∈ movingSpan c := by
    change ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ movingSpan c
    rw [movingSpan, commutator_comm]
    exact commutator_mem_commutator hm x.property
  refine ⟨⟨z, hz⟩, ?_⟩
  change q.quotient z = w
  apply congrArg Multiplicative.ofAdd
  change (q.quotient (y * x⁻¹)).toAdd = w.toAdd
  rw [map_mul, map_inv]
  simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
  rw [q.action m x y rfl, hmg', hx]
  exact hgv

include q in
/-- Surjectivity on the moving subgroup reconstructs the full span modulo Z_alpha. -/
theorem span_eq_Z_sup_moving [Finite M]
    (hd : (cosetGraph R).dist (alpha R) c = 2) :
    orbitSpan c = Z R (alpha R) ⊔ movingSpan c := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := q.moving_onto (q.quotient ⟨x, hx⟩)
    let y : orbitSpan c := inclusion (movingSpan_le_span c) a
    have hqxy : q.quotient ((⟨x, hx⟩ : orbitSpan c) * y⁻¹) = 1 := by
      rw [map_mul, map_inv]
      change q.quotient ⟨x, hx⟩ * (q.quotient (inclusion (movingSpan_le_span c) a))⁻¹ = 1
      rw [show q.quotient (inclusion (movingSpan_le_span c) a) = q.quotient ⟨x, hx⟩ from ha]
      exact mul_inv_cancel _
    have hz : x * (a : FreeAmalgam R)⁻¹ ∈ Z R (alpha R) := by
      change ((⟨x, hx⟩ : orbitSpan c) * y⁻¹) ∈ (Z R (alpha R)).subgroupOf (orbitSpan c)
      rw [← q.kernel]
      exact hqxy
    have h := (Z R (alpha R) ⊔ movingSpan c).mul_mem (mem_sup_left hz) (mem_sup_right a.property)
    simpa only [inv_mul_cancel_right] using h
  · exact sup_le (Z_le_orbitSpan_of_distance_two c hd) (movingSpan_le_span c)

end SpanQuotient

/-- The exact intersection with Z_alpha supplies a canonical CoreLift.
The required intersection equality remains an explicit mathematical input. -/
noncomputable def movingCoreLift [Finite M] (common : CommonFacts R source geometry)
    (c : Vertex R) (hd : (cosetGraph R).dist (alpha R) c = 2)
    (q : SpanQuotient source common c)
    (hker : movingSpan c ⊓ Z R (alpha R) = U R (alpha R)) : CoreLift c where
  factor := (movingSpan c).subgroupOf (core R (alpha R))
  normalized := by
    intro m x hx
    have hm : embedM R m ∈ stabilizer R (alpha R) := by
      rw [alpha, stabilizer_m_base]
      exact ⟨m, rfl⟩
    exact (mem_normalizer_iff.mp (movingSpan_normalized c hm) _).mp hx
  intersect := by
    rw [map_subgroupOf_eq_of_le (movingSpan_le_core geometry common.large_distance c hd)]
    exact hker
  decomposition := by
    rw [map_subgroupOf_eq_of_le (movingSpan_le_core geometry common.large_distance c hd)]
    exact q.span_eq_Z_sup_moving hd

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
