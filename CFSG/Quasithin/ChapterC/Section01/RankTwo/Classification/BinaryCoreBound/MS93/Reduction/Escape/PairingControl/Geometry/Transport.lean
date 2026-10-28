module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Source

/-!
# Transporting the contrary assumption to a selected configuration

The fixed-core bound is equivalent to vanishing of a triple commutator:
the first commutator already lies in Q. Conjugation transports this equation
through the actual amalgam embeddings. Thus a new critical configuration
inherits the bad bound at its start, even when its start has changed.

Source: MS93 (1993), the changes of critical configuration in (4.3.2),
pp.883--885. This does not construct the centralizer-based path choice.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : MS93.Geometry R}

theorem fixed_bound_iff_triple (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) :
    ⁅V R a, Q R a⁆ ≤ fixedCore R a ↔ ⁅⁅V R a, Q R a⁆, Ltilde R a⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  constructor
  · exact fun h => h.trans inf_le_right
  · intro h
    exact le_inf ((Subgroup.commutator_le_sup _ _).trans
      (sup_le (geometry.V_le_Q hb a ha) le_rfl)) h

omit [Finite M] in
theorem triple_eq_bot_iff_base (a : Vertex R) (ha : color R a = false) :
    ⁅⁅V R a, Q R a⁆, Ltilde R a⁆ = ⊥ ↔
      ⁅⁅V R (alpha R), Q R (alpha R)⁆, Ltilde R (alpha R)⁆ = ⊥ := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hV := V_act R g (alpha R)
  have hQ := Q_act R g (alpha R)
  have hL := Ltilde_act R g (alpha R)
  simp only [alpha, act_mVertex, one_mul] at hV hQ hL
  rw [hV, hQ, hL, ← map_commutator, ← map_commutator]
  exact map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective

/-- Every M-vertex has the same truth value for the contrary fixed-core bound. -/
theorem bad_at (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    (bad : ¬ ⁅V R a, Q R a⁆ ≤ fixedCore R a)
    (d : Vertex R) (hd : color R d = false) :
    ¬ ⁅V R d, Q R d⁆ ≤ fixedCore R d := by
  intro h
  apply bad
  apply (fixed_bound_iff_triple hb a ha).mpr
  apply (triple_eq_bot_iff_base a ha).mpr
  apply (triple_eq_bot_iff_base d hd).mp
  exact (fixed_bound_iff_triple hb d hd).mp h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry
