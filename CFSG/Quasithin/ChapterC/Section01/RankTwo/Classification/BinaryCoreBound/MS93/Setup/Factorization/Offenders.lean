module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Offenders.Algebra

/-!
# Both actual factorization offenders in MS93 2.2(vi)

Compare the displacement indices of the two endpoint layers of a critical
pair. In a favorable orientation, join the opposite layer with Q at the
initial vertex. The edge-centralizer equality identifies its centralizer
kernel with its intersection with Q, giving the offender bound.

If the comparison is reversed, reverse the critical pair and use edge
transitivity to move its first edge to the originally specified edge.
Covariance preserves both displacement indices. Thus both Z and X have an
offender at the requested vertex and edge, without assuming X = Z or an
escape theorem. Elementary structure and finiteness concern the literal
local subgroups of the generally infinite free amalgam.

The quotient actions below and `Offenders.Witness.action` are actual
conjugation actions. `Offenders.Witness.action_fixed` identifies their fixed
subgroups and `Offenders.quotientConjugation_restrict` identifies restriction
from the full local quotient. The module imports the proved normalization
and elementary-layer APIs from `Factorization.Basic`.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), 2.2(vi), printed pp.856--857.
-/

@[expose] public section

open Subgroup

open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

omit [Finite M] in
private theorem elementary_of_le_X (a : Vertex R) (Y : Subgroup (FreeAmalgam R))
    (h : Y ≤ X R a) : IsElementaryAbelian 2 Y := by
  refine {
    toIsMulCommutative := isMulCommutative_iff.mpr ?_
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · intro x y
    exact Subtype.ext ((mem_omegaCenter_iff.mp (h y.property)).2.2 x
      (omegaCenter_le (Q R a) (h x.property)))
  · intro x
    exact Subtype.ext (mem_omegaCenter_iff.mp (h x.property)).2.1

private theorem favorable_layer (g : Geometry R) (hC : EdgeCentralizerCondition R)
    (Y : Vertex R → Subgroup (FreeAmalgam R))
    (hnorm : ∀ a, stabilizer R a ≤ normalizer (Y a : Set (FreeAmalgam R)))
    (hlower : ∀ a, color R a = false → Z R a ≤ Y a)
    (hupper : ∀ a, color R a = false → Y a ≤ X R a)
    (a : Vertex R) (ha : color R a = false)
    (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    (b : Vertex R) (hc : CriticalPair R a b (g.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist a b)
    (hcomp : Offenders.displacement (Y a) (Y b) ≤ Offenders.displacement (Y b) (Y a)) :
    Nonempty (Offenders.Witness (Q R a) (Q R t) (Y a)) := by
  have hbcol := critical_endpoint_color R a ha _ hc
  have htcol : color R t = true := by
    have hh := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have hNT : Q R a ≤ Q R t := Q_le_adjacent_h R htcol hat
  have hTGa : Q R t ≤ stabilizer R a := fun x hx => hx.2 a (adjacent_symm R hat)
  have hsmall : (cosetGraph R).dist b t < criticalDistance R b (g.exists_critical b hbcol) := by
    rw [SimpleGraph.dist_comm, g.distance_constant b hbcol, ← g.distance_constant a ha]
    have hd := hc.1
    omega
  have hET : Y b ≤ Q R t := (hupper b hbcol).trans
    (X_le_Q_of_dist_lt R g hC b hbcol t hsmall)
  have hNY : Q R a ≤ centralizer (Y a : Set (FreeAmalgam R)) :=
    (Q_le_centralizer_X R a).trans (centralizer_le (hupper a ha))
  have hCY : Q R t ⊓ centralizer (Y a : Set (FreeAmalgam R)) = Q R a := by
    apply le_antisymm
    · calc
        _ ≤ Q R t ⊓ centralizer (Z R a : Set (FreeAmalgam R)) :=
          inf_le_inf_left _ (centralizer_le (hlower a ha))
        _ = _ := hC a t ha hat
    · exact le_inf hNT hNY
  have hrev := critical_reverse R g hC a ha hb b hbcol hc
  let := elementary_of_le_X R b (Y b) (hupper b hbcol)
  exact Offenders.favorable (Q R a) (Q R t) (Y a) (Y b) hNT hET
    (hTGa.trans (Q_normalized R a)) (hTGa.trans (hnorm a)) hNY hCY
    (fun h => hrev.2 ((hlower b hbcol).trans h)) hcomp

private theorem layer_offender (g : Geometry R) (hC : EdgeCentralizerCondition R)
    (Y : Vertex R → Subgroup (FreeAmalgam R))
    (hact : ∀ f a, Y (act R f a) = (Y a).map (MulAut.conj f⁻¹).toMonoidHom)
    (hnorm : ∀ a, stabilizer R a ≤ normalizer (Y a : Set (FreeAmalgam R)))
    (hlower : ∀ a, color R a = false → Z R a ≤ Y a)
    (hupper : ∀ a, color R a = false → Y a ≤ X R a)
    (a : Vertex R) (ha : color R a = false)
    (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    (b : Vertex R) (hc : CriticalPair R a b (g.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist a b) :
    Nonempty (Offenders.Witness (Q R a) (Q R t) (Y a)) := by
  by_cases hcomp : Offenders.displacement (Y a) (Y b) ≤ Offenders.displacement (Y b) (Y a)
  · exact favorable_layer R g hC Y hnorm hlower hupper a ha hb b hc t hat ht hcomp
  have hbcol := critical_endpoint_color R a ha _ hc
  have hrev := critical_reverse R g hC a ha hb b hbcol hc
  obtain ⟨s, hbs, hs⟩ := exists_adjacent_dist_sub_one R b a (by
    rw [SimpleGraph.dist_comm, hc.1]
    exact hb)
  obtain ⟨f, hf | hf⟩ := edge_transitive R hbs hat
  · obtain ⟨hfb, hfs⟩ := hf
    have hfcol : color R (act R f b) = false := by rw [action_preserves_color, hbcol]
    have hnew := (criticalPair_act_iff R f b a (g.exists_critical b hbcol)
      (g.exists_critical (act R f b) hfcol)).mpr hrev
    have hnew' : CriticalPair R a (act R f a) (g.exists_critical a ha) := by
      simpa only [hfb] using hnew
    have hpath : (cosetGraph R).dist t (act R f a) + 1 =
        (cosetGraph R).dist a (act R f a) := by
      calc
        _ = (cosetGraph R).dist (act R f s) (act R f a) + 1 := by rw [hfs]
        _ = (cosetGraph R).dist s a + 1 := by rw [dist_act]
        _ = (cosetGraph R).dist b a := hs
        _ = (cosetGraph R).dist (act R f b) (act R f a) := (dist_act R f b a).symm
        _ = _ := by rw [hfb]
    have hcmp : Offenders.displacement (Y a) (Y (act R f a)) ≤
        Offenders.displacement (Y (act R f a)) (Y a) := by
      have hh : Offenders.displacement (Y (act R f b)) (Y (act R f a)) ≤
          Offenders.displacement (Y (act R f a)) (Y (act R f b)) := by
        rw [hact, hact, Offenders.displacement_map, Offenders.displacement_map]
        exact (le_of_lt (lt_of_not_ge hcomp))
      simpa only [hfb] using hh
    exact favorable_layer R g hC Y hnorm hlower hupper a ha hb (act R f a) hnew'
      t hat hpath hcmp
  · have he : color R t = false := by rw [← hf.1, action_preserves_color, hbcol]
    exact (adjacent_color_ne R hat (ha.trans he.symm)).elim

/-- Source 2.2(vi), for the actual Z-layer and the specified first edge. -/
theorem Z_factorization_offender (g : Geometry R) (hC : EdgeCentralizerCondition R)
    (a : Vertex R) (ha : color R a = false)
    (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    (b : Vertex R) (hc : CriticalPair R a b (g.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist a b) :
    Nonempty (Offenders.Witness (Q R a) (Q R t) (Z R a)) := by
  apply layer_offender R g hC (Z R) (Z_act R) (Z_normalized R) (fun _ _ => le_rfl)
    ?_ a ha hb b hc t hat ht
  intro c hc
  apply g.omega_bound c hc
  rw [g.distance_constant c hc, ← g.distance_constant a ha]
  exact hb

/-- Source 2.2(vi), independently for X; no equality X = Z is assumed. -/
theorem X_factorization_offender (g : Geometry R) (hC : EdgeCentralizerCondition R)
    (a : Vertex R) (ha : color R a = false)
    (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    (b : Vertex R) (hc : CriticalPair R a b (g.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist a b) :
    Nonempty (Offenders.Witness (Q R a) (Q R t) (X R a)) := by
  apply layer_offender R g hC (X R) (X_act R) (X_normalized R) ?_
    (fun _ _ => le_rfl) a ha hb b hc t hat ht
  intro c hc
  apply g.omega_bound c hc
  rw [g.distance_constant c hc, ← g.distance_constant a ha]
  exact hb

/-- Both failure-of-factorization assertions of MS93 2.2(vi). -/
theorem factorization_offenders (g : Geometry R) (hC : EdgeCentralizerCondition R)
    (a : Vertex R) (ha : color R a = false)
    (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    (b : Vertex R) (hc : CriticalPair R a b (g.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (ht : (cosetGraph R).dist t b + 1 = (cosetGraph R).dist a b) :
    Nonempty (Offenders.Witness (Q R a) (Q R t) (Z R a)) ∧
      Nonempty (Offenders.Witness (Q R a) (Q R t) (X R a)) :=
  ⟨Z_factorization_offender R g hC a ha hb b hc t hat ht,
    X_factorization_offender R g hC a ha hb b hc t hat ht⟩

/-- The full local quotient acts on the literal Z-layer by conjugation. -/
noncomputable def Z_quotientConjugation (a : Vertex R) (ha : color R a = false) :
    letI := Q_normal R a
    stabilizer R a ⧸ (Q R a).subgroupOf (stabilizer R a) →* MulAut (Z R a) :=
  Offenders.quotientConjugation _ _ _ (Q_normal R a) (Z_normalized R a)
    (le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)))

/-- The full local quotient acts on the literal X-layer by conjugation. -/
noncomputable def X_quotientConjugation (a : Vertex R) :
    letI := Q_normal R a
    stabilizer R a ⧸ (Q R a).subgroupOf (stabilizer R a) →* MulAut (X R a) :=
  Offenders.quotientConjugation _ _ _ (Q_normal R a) (X_normalized R a)
    (Q_le_centralizer_X R a)

theorem Z_quotientConjugation_apply (a : Vertex R) (ha : color R a = false)
    (x : stabilizer R a) (y : Z R a) :
    letI := Q_normal R a
    (Z_quotientConjugation R a ha (QuotientGroup.mk' _ x) y : FreeAmalgam R) =
      (x : FreeAmalgam R) * y * (x : FreeAmalgam R)⁻¹ :=
  Offenders.quotientConjugation_apply _ _ _ _ _ _ _ _

omit [Finite M] in
theorem X_quotientConjugation_apply (a : Vertex R)
    (x : stabilizer R a) (y : X R a) :
    letI := Q_normal R a
    (X_quotientConjugation R a (QuotientGroup.mk' _ x) y : FreeAmalgam R) =
      (x : FreeAmalgam R) * y * (x : FreeAmalgam R)⁻¹ :=
  Offenders.quotientConjugation_apply _ _ _ _ _ _ _ _

/-- Finiteness of each layer comes from its vertex stabilizer. -/
theorem finite_Z (a : Vertex R) : Finite (Z R a) := by
  let := finite_stabilizer R a
  exact Finite.of_injective (inclusion (Z_le_stabilizer R a)) (inclusion_injective _)

theorem finite_X (a : Vertex R) : Finite (X R a) := by
  let := finite_stabilizer R a
  exact Finite.of_injective
    (inclusion ((omegaCenter_le (Q R a)).trans (fun _ hx => hx.1))) (inclusion_injective _)

/-- Offender preimages are finite although the ambient amalgam is not. -/
theorem Offenders.Witness.finite {a t : Vertex R} {Y : Subgroup (FreeAmalgam R)}
    (w : Offenders.Witness (Q R a) (Q R t) Y) : Finite w.A := by
  let := finite_stabilizer R t
  exact Finite.of_injective
    (inclusion (w.le_edge.trans (fun _ hx => hx.1))) (inclusion_injective _)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
