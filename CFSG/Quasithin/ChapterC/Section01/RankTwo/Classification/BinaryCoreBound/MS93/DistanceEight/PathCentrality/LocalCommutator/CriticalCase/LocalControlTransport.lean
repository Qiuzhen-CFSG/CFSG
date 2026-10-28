module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Transport of the complete local-control counterexample

`LocalControlAt` has two clauses, and its first clause contains the actual
intersection `Q_a ⊓ Q_c`; transporting only the orbit span is therefore not
sufficient.  Conjugation transports both kernel factors, the fixed core, and
all cyclic actors.  The result keeps the full failure of local control attached
to the original source pair and to every retained local conjugator.

Source: MS93 (4.4.1), pp.890--892.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
open LocalCommutator
variable {M : Type*} [Group M] {R : Subgroup M}

/-- Complete `LocalControlAt` is invariant under the literal simultaneous
conjugation action, including the two endpoint kernels in its first clause. -/
theorem localControlAt_act (g : FreeAmalgam R) {a c : Vertex R}
    (h : LocalControlAt R a c) :
    LocalControlAt R (act R g a) (act R g c) := by
  constructor
  · have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h.1
    rwa [map_commutator, map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      ← Q_act, ← Q_act, ← localZSpan_act,
      ← Escape.PairingControl.FirstPairing.fixedCore_act] at hh
  · intro x hx hn
    obtain ⟨y, rfl⟩ := (MulAut.conj g⁻¹).surjective x
    have hy : y ∈ Q R c := by
      rw [Q_act, mem_map_equiv] at hx
      simpa only [MulEquiv.symm_apply_apply] using hx
    have hyne : ¬ ⁅localZSpan R a c, zpowers y⁆ ≤ fixedCore R c := by
      intro hh
      apply hn
      have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hh
      rwa [map_commutator, MonoidHom.map_zpowers, ← localZSpan_act,
        ← Escape.PairingControl.FirstPairing.fixedCore_act] at hm
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (h.2 y hy hyne)
    rwa [Subgroup.map_sup, map_commutator, MonoidHom.map_zpowers,
      ← localZSpan_act, ← Z_act,
      ← Escape.PairingControl.FirstPairing.fixedCore_act] at hm

/-- The complete local-control condition is equivalent on a conjugate pair. -/
theorem localControlAt_act_iff (g : FreeAmalgam R) (a c : Vertex R) :
    LocalControlAt R (act R g a) (act R g c) ↔ LocalControlAt R a c := by
  constructor
  · intro h
    simpa only [← act_mul, mul_inv_cancel, act_one] using localControlAt_act g⁻¹ h
  · exact localControlAt_act g

/-- Local conjugation at a fixed center preserves the complete local-control
condition, with the source's original center unchanged definitionally. -/
theorem localControlAt_local_conjugator_iff {a c : Vertex R} {g : FreeAmalgam R}
    (hg : g ∈ stabilizer R c) :
    LocalControlAt R (act R g a) c ↔ LocalControlAt R a c := by
  have hgc : act R g c = c := hg
  simpa only [hgc] using localControlAt_act_iff g a c

variable {geometry : Geometry R}

/-- A backward witness transports the full local-control failure, not only the
failure of its natural section.  The original conjugator and center are kept. -/
theorem backward_localControlAt_iff {a c : Vertex R}
    (w : BackwardWitness R geometry a c) :
    LocalControlAt R w.backward c ↔ LocalControlAt R a c := by
  rw [← w.conjugator_image]
  exact localControlAt_local_conjugator_iff w.local_conjugator

/-- Explicit failure form consumed by the terminal source branch. -/
theorem backward_localControlAt_failure {a c : Vertex R}
    (w : BackwardWitness R geometry a c)
    (hfail : ¬ LocalControlAt R a c) :
    ¬ LocalControlAt R w.backward c := by
  intro h
  exact hfail ((backward_localControlAt_iff w).mp h)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
