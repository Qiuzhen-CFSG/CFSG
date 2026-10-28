module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Transporting a selected critical configuration

The whole counterexample and its centralizer choice are conjugated together.
The centralizer equality is transported through the actual amalgam action;
its radius commutator and both endpoint-side kernels move with the path.
This permits a residual-span hypothesis to be used at a new starting vertex.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2), printed p.885.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : MS93.Geometry R}

/-- All three vertices move under the same amalgam element. -/
def translate (p : Counterexample geometry) (g : FreeAmalgam R) : Counterexample geometry where
  a := act R g p.a
  a' := act R g p.a'
  c := act R g p.c
  color_a := by rw [action_preserves_color]; exact p.color_a
  critical := (criticalPair_act_iff R g p.a p.a' _ _).mpr p.critical
  before := by simpa only [Before, dist_act] using p.before
  trapped := by rw [V_act, Q_act]; exact map_mono p.trapped

private theorem centralizer_map (E : Subgroup (FreeAmalgam R)) (f : FreeAmalgam R ≃* FreeAmalgam R) :
    (centralizer (E : Set (FreeAmalgam R))).map f.toMonoidHom =
      centralizer (E.map f.toMonoidHom : Set (FreeAmalgam R)) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

/-- The selected predecessor and its literal centralizer equality move too. -/
def translateChoice {p : Counterexample geometry} (selected : CentralizerChoice p)
    (g : FreeAmalgam R) : CentralizerChoice (translate p g) where
  t := act R g selected.t
  before := by simpa only [translate, Before, dist_act] using selected.before
  centralizer_eq := by
    change Q R (act R g selected.t) ⊓
      centralizer (radiusCommutator (act R g p.a) (act R g p.a') : Set (FreeAmalgam R)) =
      Q R (act R g p.c)
    rw [Q_act, Q_act, radiusCommutator, V_act, Z_act, ← map_commutator,
      ← centralizer_map, ← Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective]
    exact congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) selected.centralizer_eq

/-- A prescribed M-vertex admits the whole translated selected configuration. -/
theorem exists_selected_at (p : Counterexample geometry) (selected : CentralizerChoice p)
    (a : Vertex R) (ha : color R a = false) :
    ∃ r : Counterexample geometry, r.a = a ∧ Nonempty (CentralizerChoice r) := by
  obtain ⟨g, hg⟩ := exists_mVertex_of_color R p.color_a
  obtain ⟨h, hh⟩ := exists_mVertex_of_color R ha
  refine ⟨translate p (g⁻¹ * h), ?_, ⟨translateChoice selected _⟩⟩
  change act R (g⁻¹ * h) p.a = a
  rw [hg, act_mVertex, mul_inv_cancel_left, ← hh]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
