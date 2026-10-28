module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Seed
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Simplicity

/-!
# Binary SL₄ endpoint recognition

An intertwiner from the trace-zero conjugation module to an irreducible
endpoint module annihilates the scalar identity: its image would otherwise
span a fixed invariant line, contradicting the active endpoint relation.
Consequently the map descends through the literal `mkAdjoint` quotient.
The incident-flag construction supplies this map, taking E₀₃ to the supplied
nonzero highest vector. Simplicity of the concrete adjoint quotient and
Schur's lemma then give an actual representation equivalence, normalized on
these specified vectors and retaining the original SL₄ marking.

`exists_equiv_of_endpoint` proves the normalized comparison, and `recognition`
supplies the `hrecognition` input in `endpoint_displacement_of_adjoint`.
The proof uses only irreducibility and the nonzero local highest vector;
finite dimension and faithfulness need not be assumed. The conditional
descent and assembly APIs are retained for other applications.

Source: Aschbacher–Smith K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section

open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) Group V} {v : V}

/-- Irreducibility and the active endpoint relation exclude globally fixed vectors. -/
theorem fixed_eq_zero_of_endpoint [IsIrreducible σ]
    (h : LocalHighestVector σ {0, 2} v) (hv : v ≠ 0)
    {x : V} (hx : ∀ g, σ g x = x) : x = 0 := by
  by_contra hx0
  let W : Subrepresentation σ :=
    { toSubmodule := Submodule.span (ZMod 2) {x}
      apply_mem_toSubmodule := by
        intro g y hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [map_smul, hx]
        exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩ }
  have hxW : x ∈ W := Submodule.subset_span (Set.mem_singleton x)
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left (by
    intro he
    rw [he] at hxW
    exact hx0 hxW)
  have hvW : v ∈ W := by rw [hW]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvW
  apply h.swap_ne_self hv (show (0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) by decide)
  rw [← hc, map_smul, hx]

/-- A trace-zero intertwiner into an irreducible endpoint module kills the identity. -/
theorem scalarVector_killed [IsIrreducible σ]
    (h : LocalHighestVector σ {0, 2} v) (hv : v ≠ 0)
    (f : IntertwiningMap traceAction σ) : f scalarVector = 0 := by
  apply fixed_eq_zero_of_endpoint h hv
  intro g
  rw [← f.isIntertwining, traceAction_scalarVector]

/-- Descend through the literal scalar quotient, retaining the same SL₄ action. -/
def descendTraceMap (f : IntertwiningMap traceAction σ)
    (hscalar : f scalarVector = 0) : IntertwiningMap adjoint σ where
  toLinearMap := scalarLine.toSubmodule.liftQ f.toLinearMap (by
    change Submodule.span (ZMod 2) {scalarVector} ≤ LinearMap.ker f.toLinearMap
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    exact hscalar)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := mkAdjoint_surjective x
    change f (traceAction g y) = σ g (f y)
    exact LinearMap.congr_fun (f.isIntertwining' g) y

/-- The descended map agrees with the original map on every quotient representative. -/
@[simp] theorem descendTraceMap_mk (f : IntertwiningMap traceAction σ)
    (hscalar : f scalarVector = 0) (x : TraceZero) :
    descendTraceMap f hscalar (mkAdjoint x) = f x := by rfl

/-- A cyclic trace-zero map and simplicity of the actual quotient give a marked
equivalence taking the supplied highest vector to the canonical root class. -/
theorem exists_equiv_of_traceMap [IsIrreducible σ]
    (h : LocalHighestVector σ {0, 2} v) (hv : v ≠ 0)
    (hsimple : IsIrreducible adjoint)
    (f : IntertwiningMap traceAction σ) (hf : f highestRoot = v) :
    ∃ e : σ.Equiv adjoint, e v = mkAdjoint highestRoot := by
  let := hsimple
  let F := descendTraceMap f (scalarVector_killed h hv f)
  have hF : F ≠ 0 := by
    intro hz
    have he := congrArg (fun t : IntertwiningMap adjoint σ => t (mkAdjoint highestRoot)) hz
    change f highestRoot = 0 at he
    exact hv (hf.symm.trans he)
  let e := F.ofBijective ((IsIrreducible.bijective_or_eq_zero F).resolve_right hF)
  refine ⟨e.symm, ?_⟩
  rw [← hf]
  exact e.symm_apply_apply (mkAdjoint highestRoot)

/-- The concrete cyclic construction supplies exactly the `hrecognition` input
of `endpoint_displacement_of_adjoint`. Both mathematical premises remain
explicit here; the source recognition theorem must discharge them. -/
theorem recognition_of_trace_maps
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ)
    (hcyclic : ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 2} v →
      ∃ f : IntertwiningMap traceAction σ, f highestRoot = v)
    (hsimple : IsIrreducible adjoint) :
    ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 2} v →
      Nonempty (σ.Equiv adjoint) := by
  let := hi
  intro v hv h
  obtain ⟨f, hf⟩ := hcyclic v hv h
  obtain ⟨e, _⟩ := exists_equiv_of_traceMap h hv hsimple f hf
  exact ⟨e⟩

/-- An irreducible module with a nonzero endpoint highest vector is the literal
adjoint quotient, with the original SL₄ marking and the specified normalization.
The cyclic map and adjoint simplicity are both discharged. -/
theorem exists_equiv_of_endpoint [IsIrreducible σ]
    (h : LocalHighestVector σ {0, 2} v) (hv : v ≠ 0) :
    ∃ e : σ.Equiv adjoint, e v = mkAdjoint highestRoot := by
  obtain ⟨f, hf⟩ := exists_traceMap_of_endpoint h
  exact exists_equiv_of_traceMap h hv adjoint_isIrreducible f hf

/-- The endpoint module comparison in the exact form consumed by
`endpoint_displacement_of_adjoint`. No extra recognition premise remains. -/
theorem recognition
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ) :
    ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 2} v →
      Nonempty (σ.Equiv adjoint) := by
  let := hi
  intro v hv h
  obtain ⟨e, _⟩ := exists_equiv_of_endpoint h hv
  exact ⟨e⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint
