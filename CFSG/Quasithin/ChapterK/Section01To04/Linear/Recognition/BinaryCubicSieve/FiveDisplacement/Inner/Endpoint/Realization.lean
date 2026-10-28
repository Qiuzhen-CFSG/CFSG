module

public import Theory.Representation.SL5Adjoint.Simplicity
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Realization.Cyclic
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Contracts
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Assembly for the binary SL₅ endpoint adjoint realization

The endpoint highest-vector relations construct a map from the literal
trace-zero matrix representation taking E₀₄ to the given nonzero vector.
Simplicity of both representations makes this map an isomorphism. The cyclic
map and source simplicity are proved in `Realization.Cyclic` and
`SL5Adjoint.Simplicity`; neither is an extra assumption. In particular, this
proves recognition for every faithful finite-dimensional irreducible source
module, without needing faithfulness or finite dimension for the construction.

The equivalence preserves the actual SL₅ marking, sends the given vector
exactly to E₀₄, and gives dimension 24 as a conclusion. It preserves the
given subgroup, its cubic action, and its common fixed codimension. The final
consumer discharges the recognition premise of `Inner.EndpointEstimate`,
leaving only the independently produced common-centralizer bound on the
concrete adjoint module. The older conditional interfaces remain available.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript,
Lemma 4.5 step 2, pp.23–24; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL5TenDimensional.Classification
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) SL5TenDimensional.Group V} {v : V}

/-- A nonzero marked cyclic map is an actual equivalence with the trace-zero model. -/
theorem exists_equiv_of_cyclicMap [IsIrreducible σ] (hv : v ≠ 0)
    (f : IntertwiningMap SL5Adjoint.action σ) (hf : f SL5Adjoint.highestRoot = v) :
    ∃ e : σ.Equiv SL5Adjoint.action, e v = SL5Adjoint.highestRoot := by
  have hn : f ≠ 0 := by
    intro hz
    have he := congrArg (fun t : IntertwiningMap SL5Adjoint.action σ =>
      t SL5Adjoint.highestRoot) hz
    exact hv (hf.symm.trans he)
  let e := f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hn)
  refine ⟨e.symm, ?_⟩
  rw [← hf]
  exact e.symm_apply_apply SL5Adjoint.highestRoot

/-- A nonzero endpoint highest vector in an irreducible representation identifies
the original marked SL₅ action with conjugation on the literal trace kernel.
The equivalence takes the specified vector to E₀₄ without rescaling. -/
theorem exists_equiv_of_localHighestVector [IsIrreducible σ] (hv : v ≠ 0)
    (h : LocalHighestVector σ {0, 3} v) :
    ∃ e : σ.Equiv SL5Adjoint.action, e v = SL5Adjoint.highestRoot :=
  exists_equiv_of_cyclicMap hv (Cyclic.cyclicMap h) (Cyclic.cyclicMap_highestRoot h)

/-- The endpoint dimension is a consequence of the marked realization. -/
theorem finrank_eq_twentyfour [IsIrreducible σ] (hv : v ≠ 0)
    (h : LocalHighestVector σ {0, 3} v) : Module.finrank (ZMod 2) V = 24 := by
  obtain ⟨e, _⟩ := exists_equiv_of_localHighestVector hv h
  exact e.toLinearEquiv.finrank_eq.trans SL5Adjoint.finrank_space

/-- The literal subgroup has the same common-fixed-space codimension on both modules. -/
theorem fixedCodim_eq_of_equiv (e : σ.Equiv SL5Adjoint.action)
    (B : Subgroup SL5TenDimensional.Group) :
    fixedCodim σ B = fixedCodim SL5Adjoint.action B := by
  simpa only [Subgroup.map_id] using
    fixedCodim_map_equivariant σ SL5Adjoint.action (MonoidHom.id _) e.toLinearEquiv
      (fun g x => LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x) B

/-- Cubicity transports through the same marked equivalence and the same subgroup. -/
theorem cubic_of_equiv (e : σ.Equiv SL5Adjoint.action)
    {B : Subgroup SL5TenDimensional.Group} (hB : IsCubic σ B) :
    IsCubic SL5Adjoint.action B := by
  have he (g : SL5TenDimensional.Group) (x : V) :
      e (displacement σ g x) = displacement SL5Adjoint.action g (e x) := by
    change e (σ g x - x) = SL5Adjoint.action g (e x) - e x
    rw [map_sub]
    exact congrArg (fun z => z - e x)
      (LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x)
  intro a ha b hb c hc y
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
  change displacement SL5Adjoint.action a
    (displacement SL5Adjoint.action b (displacement SL5Adjoint.action c (e x))) = 0
  rw [← he, ← he, ← he, hB a ha b hb c hc x, map_zero]

/-- A cyclic-map producer and the concrete adjoint bound supply the exact endpoint
consumer. Both remaining source inputs are explicit and must be discharged. -/
theorem endpoint_estimate_of_cyclicMaps [IsIrreducible σ]
    (hcyclic : ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 3} v →
      ∃ f : IntertwiningMap SL5Adjoint.action σ, f SL5Adjoint.highestRoot = v)
    (hmodel : ∀ B : Subgroup SL5TenDimensional.Group,
      IsElementaryTwo B → IsCubic SL5Adjoint.action B → rank B ≤ 6 →
      2 * rank B < fixedCodim SL5Adjoint.action B) : EndpointEstimate σ := by
  intro v hv h B hB hc hr
  obtain ⟨f, hf⟩ := hcyclic v hv h
  obtain ⟨e, _⟩ := exists_equiv_of_cyclicMap hv f hf
  rw [fixedCodim_eq_of_equiv e]
  exact hmodel B hB (cubic_of_equiv e hc) hr

/-- Application to the exact endpoint consumer: the highest-vector recognition
premise is now discharged. The endpoint assembly owner supplies the independent
common-centralizer estimate for the literal adjoint action. -/
theorem endpoint_estimate_of_adjoint [IsIrreducible σ]
    (hmodel : ∀ B : Subgroup SL5TenDimensional.Group,
      IsElementaryTwo B → IsCubic SL5Adjoint.action B → rank B ≤ 6 →
      2 * rank B < fixedCodim SL5Adjoint.action B) : EndpointEstimate σ := by
  intro v hv h B hB hc hr
  obtain ⟨e, _⟩ := exists_equiv_of_localHighestVector hv h
  rw [fixedCodim_eq_of_equiv e]
  exact hmodel B hB (cubic_of_equiv e hc) hr

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint
