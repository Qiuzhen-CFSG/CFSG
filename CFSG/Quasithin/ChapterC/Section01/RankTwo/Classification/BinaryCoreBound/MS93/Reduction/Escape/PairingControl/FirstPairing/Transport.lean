module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Source

/-!
# Transport for the first escape pairing

The fixed core and the literal fixed preimage B are covariant under the
right-coset amalgam action. Thus moving-neighbor membership, contrary
commutator bounds, and whole contrary configurations transport. In particular
one contrary configuration gives such a configuration starting at every
vertex of M-type. No finiteness of the amalgam is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2)--(3), pp.883--884.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

private theorem centralizer_map_equiv {G : Type*} [Group G]
    (E : Subgroup G) (f : G ≃* G) :
    (centralizer (E : Set G)).map f.toMonoidHom =
      centralizer (E.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

theorem fixedCore_act (g : FreeAmalgam R) (a : Vertex R) :
    fixedCore R (act R g a) = (fixedCore R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [fixedCore, Q_act, Ltilde_act, fixedCore,
    Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective, centralizer_map_equiv]

/-- The contrary hypothesis transports with the whole configuration. -/
theorem bad_act_iff (g : FreeAmalgam R) (a : Vertex R) :
    (¬ ⁅V R (act R g a), Q R (act R g a)⁆ ≤ fixedCore R (act R g a)) ↔
      ¬ ⁅V R a, Q R a⁆ ≤ fixedCore R a := by
  rw [V_act, Q_act, fixedCore_act, ← map_commutator,
    map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]

/-- Transport a contrary configuration to any prescribed M-type vertex. -/
theorem contrary_at (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (a : Vertex R) (ha : color R a = false) :
    ∃ q : Counterexample geometry, q.a = a ∧
      ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a := by
  obtain ⟨g, hg⟩ := exists_mVertex_of_color R p.color_a
  obtain ⟨h, hh⟩ := exists_mVertex_of_color R ha
  let k := g⁻¹ * h
  let q : Counterexample geometry := {
    a := act R k p.a
    a' := act R k p.a'
    c := act R k p.c
    color_a := by rw [action_preserves_color]; exact p.color_a
    critical := (criticalPair_act_iff R k p.a p.a' _ _).mpr p.critical
    before := by simpa only [Before, dist_act] using p.before
    trapped := by rw [V_act, Q_act]; exact map_mono p.trapped }
  refine ⟨q, ?_, (bad_act_iff k p.a).mpr bad⟩
  change act R (g⁻¹ * h) p.a = a
  rw [hg, act_mVertex, mul_inv_cancel_left, ← hh]

theorem edgeDisplacement_act (g : FreeAmalgam R) (a t : Vertex R) :
    edgeDisplacement (act R g a) (act R g t) =
      (edgeDisplacement a t).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [edgeDisplacement, Z_act, Q_act, ← map_commutator]
  rfl

variable [Finite M]

/-- Covariance of the actual fixed preimage, without a later center formula. -/
theorem B_act (hb : 2 < geometry.b R) (g : FreeAmalgam R)
    (a : Vertex R) (ha : color R a = false) :
    B R (act R g a) (geometry.Z_normal _) =
      (B R a (geometry.Z_normal a)).map (MulAut.conj g⁻¹).toMonoidHom := by
  let f := MulAut.conj g⁻¹
  have hV : V R a ≤ stabilizer R a :=
    (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hVg : V R (act R g a) ≤ stabilizer R (act R g a) :=
    (geometry.V_le_Q hb _ (by rwa [action_preserves_color])).trans (fun _ hx => hx.1)
  ext x
  rw [mem_B_iff R _ _ hVg]
  constructor
  · rintro ⟨hx, hc⟩
    rw [V_act] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, (mem_B_iff R a _ hV y).mpr ⟨hy, ?_⟩, rfl⟩
    intro l hl
    have hl' : f l ∈ Ltilde R (act R g a) := by
      rw [Ltilde_act]
      exact mem_map_of_mem _ hl
    have hh := hc (f l) hl'
    rw [Z_act] at hh
    change ⁅f l, f y⁆ ∈ (Z R a).map f.toMonoidHom at hh
    rw [← map_commutatorElement f] at hh
    obtain ⟨z, hz, he⟩ := hh
    exact f.injective he ▸ hz
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy, hc⟩ := (mem_B_iff R a _ hV y).mp hy
    refine ⟨?_, ?_⟩
    · rw [V_act]
      exact mem_map_of_mem _ hy
    · intro l hl
      rw [Ltilde_act] at hl
      obtain ⟨k, hk, rfl⟩ := hl
      rw [Z_act, ← map_commutatorElement f.toMonoidHom]
      exact mem_map_of_mem _ (hc k hk)

theorem movingNeighbors_act_iff (hb : 2 < geometry.b R)
    (g : FreeAmalgam R) (a d : Vertex R) (ha : color R a = false) :
    act R g d ∈ movingNeighbors geometry (act R g a) ↔
      d ∈ movingNeighbors geometry a := by
  change (_ = 2 ∧ ¬ _ ≤ _) ↔ (_ = 2 ∧ ¬ _ ≤ _)
  rw [dist_act, B_act hb g a ha, Z_act,
    map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
