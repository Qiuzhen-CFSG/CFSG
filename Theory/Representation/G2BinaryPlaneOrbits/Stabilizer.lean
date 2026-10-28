module

public import Theory.Representation.G2BinaryPlaneOrbits.Basic
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.StandardPair

/-!
# The stabilizer of the literal binary null plane

A singular trace-zero octonion whose quotient class lies in the marked plane
has zero diagonal entries: the trace identifies them and the norm forces their
square to vanish. Thus preserving the quotient plane is equivalent to preserving
the original null octonion plane. The existing geometric parabolic identification
and its derived order give the stabilizer order 96.

Source: Aschbacher–Smith, printed p.1132 (PDF p.1149), C.1.30 and B.5.3–6.
The original octonion parabolic calculation is from the attributed ATLAS port;
see LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
namespace Atlas.G2.Natural.BinaryPlane
open Atlas.SplitOctonion Atlas.G2.LieParabolicSetup
open Representation.BinaryOffender

private theorem mk_mem_standardPlane (x : TraceZero (ZMod 2))
    (hx : x.val ∈ shortPlane) : mk (ZMod 2) x ∈ standardPlane := by
  apply (mem_standardPlane_iff _).mpr
  exact ⟨hx 2 (by decide), hx 5 (by decide), hx 6 (by decide), hx 7 (by decide)⟩

private theorem shortPlane_of_mk_mem (x : TraceZero (ZMod 2))
    (hn : Atlas.SplitOctonion.norm x.val = 0)
    (hx : mk (ZMod 2) x ∈ standardPlane) : x.val ∈ shortPlane := by
  have h := (mem_standardPlane_iff _).mp hx
  have h2 : x.val 2 = 0 := h.1
  have h5 : x.val 5 = 0 := h.2.1
  have h6 : x.val 6 = 0 := h.2.2.1
  have h7 : x.val 7 = 0 := h.2.2.2
  have hd : x.val 3 = x.val 4 := by
    have ht : x.val 3 + x.val 4 = 0 := x.property
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left ht
  have h4 : x.val 4 = 0 := mul_self_eq_zero.mp (by
    simpa [Atlas.SplitOctonion.norm, h2,h5,h6,h7,hd] using hn)
  intro i hi
  fin_cases i <;> simp_all

private theorem shortPlane_trace {x : Carrier (ZMod 2)} (hx : x ∈ shortPlane) : trace x = 0 := by
  change x 3 + x 4 = 0
  rw [hx 3 (by decide), hx 4 (by decide), add_zero]

private theorem shortPlane_norm {x : Carrier (ZMod 2)} (hx : x ∈ shortPlane) :
    Atlas.SplitOctonion.norm x = 0 := by
  simp [Atlas.SplitOctonion.norm, hx 7 (by decide), hx 6 (by decide),
    hx 5 (by decide), hx 4 (by decide)]

private theorem shortPlane_preserved (g : Actor) (hg : g ∈ subspaceStabilizer action standardPlane)
    (x : Carrier (ZMod 2)) (hx : x ∈ shortPlane) : g.val.val x ∈ shortPlane := by
  let y : TraceZero (ZMod 2) := ⟨x, shortPlane_trace hx⟩
  have hy : mk (ZMod 2) y ∈ standardPlane := mk_mem_standardPlane y hx
  have hgy := (hg (mk (ZMod 2) y)).mpr hy
  change mk (ZMod 2) (traceZeroAction (ZMod 2) g.val y) ∈ standardPlane at hgy
  apply shortPlane_of_mk_mem _ _ hgy
  change Atlas.SplitOctonion.norm (g.val.val x) = 0
  rw [automorphism_norm, shortPlane_norm hx]

private theorem quotientPlane_preserved (g : Actor)
    (hg : g.val ∈ shortPlaneStabilizer) :
    ∀ v ∈ standardPlane, action g v ∈ standardPlane := by
  have h : standardPlane ≤ standardPlane.comap (action g) := by
    apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · change mk (ZMod 2) (traceZeroAction (ZMod 2) g.val firstRepresentative) ∈ standardPlane
      apply mk_mem_standardPlane
      exact hg.1 _ (by intro i hi; fin_cases i <;> simp_all [firstRepresentative])
    · rw [Set.mem_singleton_iff.mp hv]
      change mk (ZMod 2) (traceZeroAction (ZMod 2) g.val secondRepresentative) ∈ standardPlane
      apply mk_mem_standardPlane
      exact hg.1 _ (by intro i hi; fin_cases i <;> simp_all [secondRepresentative])
  exact fun _ hv => h hv

/-- The quotient-plane stabilizer is exactly the derived null-plane parabolic. -/
theorem standardPlane_stabilizer :
    subspaceStabilizer action standardPlane = BinaryParabolicPair.derivedFirst := by
  rw [BinaryParabolicPair.derivedFirst_eq_planeStabilizer]
  apply le_antisymm
  · intro g hg
    exact ⟨shortPlane_preserved g hg,
      shortPlane_preserved g⁻¹ ((subspaceStabilizer action standardPlane).inv_mem hg)⟩
  · apply le_subspaceStabilizer
    exact quotientPlane_preserved

theorem card_standardPlane_stabilizer :
    Nat.card (subspaceStabilizer action standardPlane) = 96 := by
  rw [standardPlane_stabilizer]
  exact BinaryParabolicPair.card_derivedFirst
end Atlas.G2.Natural.BinaryPlane
