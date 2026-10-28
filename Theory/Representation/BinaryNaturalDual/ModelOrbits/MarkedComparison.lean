module

public import Theory.Representation.BinaryNaturalDual.ModelOrbits.Coordinate

/-!
# Marked comparison with the binary natural-plus-dual module

Let the actual automorphism group of GLₙ(2), for n = 4 or 5, act on a binary
vector space V = U ⊕ W. A specified natural-module equivalence on U and one
outer automorphism taking U onto W determine a comparison with the coordinate
natural-plus-dual action. No action formula on W is assumed.

Inner/graph coverage first shows that the graph involution takes U onto W.
Its restriction identifies W with U; composing with the given natural marking
and the dot-product equivalence defines the dual coordinates. The inverse
transpose pairing identity proves the contragredient action on W. The resulting
whole-space equivalence intertwines both inner and graph elements, hence every
actual automorphism, and retains both marked summands.

`exists_equiv` takes the coordinate action explicitly. Its construction and
the identification of the source layer with the inner group remain separate
inputs to the source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the setup of H.9
and H.9.1(1–2), printed pp.389–390. This module does not use the incompatible
fixed-Sylow marking in H.9.1(4).
-/

public section

open BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.ModelOrbits.MarkedComparison
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) (MulAut (LinearGroup n)) V)
variable {U W : Submodule (ZMod 2) V} (eU : U ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n)

/-- A natural marking makes the marked summand invariant under every inner automorphism. -/
theorem inner_map_natural
    (hU : ∀ (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n),
      ρ (MulAut.conj g) (eU.symm x : V) = (eU.symm (g x) : V))
    (g : LinearGroup n) : U.map (ρ (MulAut.conj g)) = U := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have he := hU g (eU ⟨u, hu⟩)
    simp only [LinearEquiv.symm_apply_apply] at he
    rw [he]
    exact Subtype.coe_prop _
  · intro hv
    refine ⟨eU.symm (g.symm (eU ⟨v, hv⟩)), Subtype.coe_prop _, ?_⟩
    rw [hU, g.apply_symm_apply, eU.symm_apply_apply]

/-- An outer image of the natural summand is its image under the graph involution. -/
theorem graph_map_natural (hn : n = 4 ∨ n = 5)
    (hU : ∀ (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n),
      ρ (MulAut.conj g) (eU.symm x : V) = (eU.symm (g x) : V))
    (hout : ∃ t : MulAut (LinearGroup n), t ∉ MulAut.innerSubgroup (LinearGroup n) ∧
      U.map (ρ t) = W) : U.map (ρ (graphLinear n)) = W := by
  obtain ⟨t, ht, hW⟩ := hout
  obtain ⟨g, rfl | rfl⟩ := inner_graph hn t
  · exact (ht ⟨g, rfl⟩).elim
  · rw [map_mul] at hW
    change U.map ((ρ (graphLinear n)).comp (ρ (MulAut.conj g))) = W at hW
    rwa [Submodule.map_comp, inner_map_natural ρ eU hU] at hW

private theorem graph_sq (v : V) : ρ (graphLinear n) (ρ (graphLinear n) v) = v := by
  change (ρ (graphLinear n) * ρ (graphLinear n)) v = v
  rw [← map_mul, ← pow_two, graphLinear_sq, map_one]
  rfl

private theorem graph_mem_natural (hW : U.map (ρ (graphLinear n)) = W) (w : W) :
    ρ (graphLinear n) w ∈ U := by
  have hw : (w : V) ∈ U.map (ρ (graphLinear n)) := by rw [hW]; exact w.property
  obtain ⟨u, hu, he⟩ := Submodule.mem_map.mp hw
  rw [← he, graph_sq]
  exact hu

private noncomputable def swapEquiv (hW : U.map (ρ (graphLinear n)) = W) : U ≃ₗ[ZMod 2] W where
  toFun u := ⟨ρ (graphLinear n) u, hW ▸ Submodule.mem_map_of_mem u.property⟩
  invFun w := ⟨ρ (graphLinear n) w, graph_mem_natural ρ hW w⟩
  left_inv u := Subtype.ext (graph_sq ρ u)
  right_inv w := Subtype.ext (graph_sq ρ w)
  map_add' u v := Subtype.ext (map_add _ (u : V) (v : V))
  map_smul' a u := Subtype.ext (map_smul _ a (u : V))

/-- The second marking is forced by the graph involution and the dot-product pairing. -/
noncomputable def dualEquiv (hW : U.map (ρ (graphLinear n)) = W) :
    W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n) :=
  ((swapEquiv ρ hW).symm.trans eU).trans (dotProductEquiv (ZMod 2) (Fin n))

/-- The whole-space comparison retains the supplied natural marking. -/
noncomputable def equiv (hUW : IsCompl U W) (hW : U.map (ρ (graphLinear n)) = W) :
    V ≃ₗ[ZMod 2] CoordinateSpace n :=
  (U.prodEquivOfIsCompl W hUW).symm.trans (eU.prodCongr (dualEquiv ρ eU hW))

/-- On the natural summand the comparison agrees with the original marking. -/
theorem equiv_natural (hUW : IsCompl U W) (hW : U.map (ρ (graphLinear n)) = W) (u : U) :
    equiv ρ eU hUW hW u = (eU u, 0) := by
  simp [equiv]

/-- The complementary summand is the pure dual coordinate space. -/
theorem equiv_dual (hUW : IsCompl U W) (hW : U.map (ρ (graphLinear n)) = W) (w : W) :
    equiv ρ eU hUW hW w = (0, dualEquiv ρ eU hW w) := by
  simp [equiv]

/-- The inverse comparison is the sum of the marked natural vector and a graph image. -/
theorem equiv_symm_apply (hUW : IsCompl U W) (hW : U.map (ρ (graphLinear n)) = W)
    (v : CoordinateSpace n) :
    (equiv ρ eU hUW hW).symm v = (eU.symm v.1 : V) +
      ρ (graphLinear n) (eU.symm ((dotProductEquiv (ZMod 2) (Fin n)).symm v.2) : V) := by rfl

private theorem graph_conj (g : LinearGroup n) :
    MulAut.conj g * graphLinear n = graphLinear n * MulAut.conj (graphLinear n g) := by
  have hh (g : LinearGroup n) : graphLinear n (graphLinear n g) = g := by
    change (graphLinear n * graphLinear n) g = g
    rw [← pow_two, graphLinear_sq]
    rfl
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hh]

private theorem inner_graph_apply (g : LinearGroup n) (v : V) :
    ρ (MulAut.conj g) (ρ (graphLinear n) v) =
      ρ (graphLinear n) (ρ (MulAut.conj (graphLinear n g)) v) := by
  change (ρ (MulAut.conj g) * ρ (graphLinear n)) v =
    (ρ (graphLinear n) * ρ (MulAut.conj (graphLinear n g))) v
  rw [← map_mul, ← map_mul, graph_conj]

private theorem dotProduct_graph (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n) :
    dotProductEquiv (ZMod 2) (Fin n) (graphLinear n g x) =
      g.symm.dualMap (dotProductEquiv (ZMod 2) (Fin n) x) := by
  apply LinearMap.ext
  intro y
  change dotProduct (graphLinear n g x) y = dotProduct x (g.symm y)
  simpa only [g.apply_symm_apply] using graphLinear_dotProduct g x (g.symm y)

/-- The inverse comparison intertwines the entire inner action. -/
theorem equiv_symm_inner (hUW : IsCompl U W) (hW : U.map (ρ (graphLinear n)) = W)
    (hU : ∀ (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n),
      ρ (MulAut.conj g) (eU.symm x : V) = (eU.symm (g x) : V))
    (g : LinearGroup n) (v : CoordinateSpace n) :
    ρ (MulAut.conj g) ((equiv ρ eU hUW hW).symm v) =
      (equiv ρ eU hUW hW).symm (naturalDualRepresentation g v) := by
  rw [equiv_symm_apply, map_add, hU, inner_graph_apply, hU,
    naturalDualRepresentation_apply, equiv_symm_apply]
  congr 2
  apply congrArg (fun x => (eU.symm x : V))
  apply (dotProductEquiv (ZMod 2) (Fin n)).injective
  rw [dotProduct_graph, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The graph involution exchanges the marked natural and dual coordinates. -/
theorem equiv_symm_graph (hUW : IsCompl U W) (hW : U.map (ρ (graphLinear n)) = W)
    (v : CoordinateSpace n) :
    ρ (graphLinear n) ((equiv ρ eU hUW hW).symm v) =
      (equiv ρ eU hUW hW).symm (coordinateSwap n v) := by
  rw [equiv_symm_apply, map_add, graph_sq, equiv_symm_apply, coordinateSwap_apply]
  simp only [LinearEquiv.symm_apply_apply]
  exact add_comm _ _

/-- The marked comparison intertwines every actual automorphism. -/
theorem equivariant (hn : n = 4 ∨ n = 5) (A : CoordinateAction n)
    (hUW : IsCompl U W) (hW : U.map (ρ (graphLinear n)) = W)
    (hU : ∀ (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n),
      ρ (MulAut.conj g) (eU.symm x : V) = (eU.symm (g x) : V))
    (a : MulAut (LinearGroup n)) (v : V) :
    equiv ρ eU hUW hW (ρ a v) = A.representation a (equiv ρ eU hUW hW v) := by
  suffices hs : ∀ (a : MulAut (LinearGroup n)) (x : CoordinateSpace n),
      ρ a ((equiv ρ eU hUW hW).symm x) =
        (equiv ρ eU hUW hW).symm (A.representation a x) by
    apply (equiv ρ eU hUW hW).symm.injective
    simpa only [LinearEquiv.symm_apply_apply] using hs a (equiv ρ eU hUW hW v)
  intro a x
  obtain ⟨g, rfl | rfl⟩ := inner_graph hn a
  · rw [A.on_inner]
    exact equiv_symm_inner ρ eU hUW hW hU g x
  · simp only [map_mul, Module.End.mul_apply, A.on_inner, A.on_graph,
      equiv_symm_inner ρ eU hUW hW hU, equiv_symm_graph]

/-- Membership in the natural summand is exactly vanishing of the dual coordinate. -/
theorem equiv_mem_natural_iff (hUW : IsCompl U W)
    (hW : U.map (ρ (graphLinear n)) = W) (v : V) :
    v ∈ U ↔ (equiv ρ eU hUW hW v).2 = 0 := by
  simp [equiv]

/-- Membership in the complementary summand is exactly vanishing of the natural coordinate. -/
theorem equiv_mem_dual_iff (hUW : IsCompl U W)
    (hW : U.map (ρ (graphLinear n)) = W) (v : V) :
    v ∈ W ↔ (equiv ρ eU hUW hW v).1 = 0 := by
  simp [equiv]

/-- A pure dual vector is reconstructed using the actual graph operator. -/
theorem dualEquiv_symm_apply (hW : U.map (ρ (graphLinear n)) = W)
    (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    ((dualEquiv ρ eU hW).symm f : V) =
      ρ (graphLinear n) (eU.symm ((dotProductEquiv (ZMod 2) (Fin n)).symm f) : V) := by rfl

/-- The action on the second summand is contragredient, derived from the natural action. -/
theorem dualEquiv_symm_inner (hW : U.map (ρ (graphLinear n)) = W)
    (hU : ∀ (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n),
      ρ (MulAut.conj g) (eU.symm x : V) = (eU.symm (g x) : V))
    (g : LinearGroup n) (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    ρ (MulAut.conj g) ((dualEquiv ρ eU hW).symm f : V) =
      ((dualEquiv ρ eU hW).symm (g.symm.dualMap f) : V) := by
  rw [dualEquiv_symm_apply, inner_graph_apply, hU, dualEquiv_symm_apply]
  congr 1
  apply congrArg (fun x => (eU.symm x : V))
  apply (dotProductEquiv (ZMod 2) (Fin n)).injective
  rw [dotProduct_graph, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Graph compatibility on the second summand follows from the graph square relation. -/
theorem dualEquiv_symm_graph (hW : U.map (ρ (graphLinear n)) = W)
    (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    ρ (graphLinear n) ((dualEquiv ρ eU hW).symm f : V) =
      (eU.symm ((dotProductEquiv (ZMod 2) (Fin n)).symm f) : V) := by
  rw [dualEquiv_symm_apply, graph_sq]

/-- The source outer-image condition and the natural marking give a fully equivariant,
marked natural-plus-dual comparison. No dual or off-diagonal compatibility is an input. -/
theorem exists_equiv (hn : n = 4 ∨ n = 5) (A : CoordinateAction n)
    (hUW : IsCompl U W)
    (hU : ∀ (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n),
      ρ (MulAut.conj g) (eU.symm x : V) = (eU.symm (g x) : V))
    (hout : ∃ t : MulAut (LinearGroup n), t ∉ MulAut.innerSubgroup (LinearGroup n) ∧
      U.map (ρ t) = W) :
    ∃ (eW : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
      (eV : V ≃ₗ[ZMod 2] CoordinateSpace n),
      (∀ u : U, eV u = (eU u, 0)) ∧
      (∀ w : W, eV w = (0, eW w)) ∧
      (∀ a v, eV (ρ a v) = A.representation a (eV v)) := by
  have hW := graph_map_natural ρ eU hn hU hout
  exact ⟨dualEquiv ρ eU hW, equiv ρ eU hUW hW,
    equiv_natural ρ eU hUW hW, equiv_dual ρ eU hUW hW,
    equivariant ρ eU hn A hUW hW hU⟩

end BinaryNaturalDual.ModelOrbits.MarkedComparison
