module

public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleBase
public import Theory.GroupTheory.GraphUniquenessSystem.Recognition

/-!
# Recognition from a simply connected triangle model

A uniqueness system retains the faithful graph action, the distinguished edge,
the local subgroup and all three generation identities of condition (U).
A similarity consists of compatible vertex and local stabilizer isomorphisms;
its equivalence condition retains conjugation by an edge reversal. These are
the genuine interfaces re-exported from `GraphUniquenessSystem`.

The triangle base theorem feeds the universal-completion recognition theorem.
The completion is constructed from the three stabilizer groups and their
intersection relations, and the cycle base proves that its canonical map is
an isomorphism. Simplicity then makes the induced surjection onto the other
acting group injective. No global homomorphism or isomorphism is assumed.

Only the simple model requires a cycle base. We prove symmetry of the local
comparison and its conjugation identity, so the resulting multiplicative
equivalence extends the given local maps in either comparison direction. In
particular `recognitionEquivOfSourceTriangleOrbit` has the model-to-source
direction used by F.5.7. Apply it with `D.simplyConnected` when the model
geometry is supplied as `TriangleContractionData`.

Sources: Aschbacher, *Sporadic Groups* (1994), §§36–37, especially 37.5–37.6
and Exercise 13.1(b), p.210; Aschbacher–Smith, *The Classification of Quasithin
Groups*, Lemmas F.5.7–F.5.8 and the final paragraph of §F.5, pp.303–304.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem
universe u v u' v'
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable {G' : Type u'} {V' : Type v'} [Group G'] [MulAction G' V']

namespace Similarity
variable {U : System G V} {U' : System G' V'} (s : Similarity U U')

/-- Invert both local comparisons, retaining all intersection compatibilities. -/
def symm : Similarity U' U where
  vertexIso := s.vertexIso.symm
  localIso := s.localIso.symm
  agree g hgH hgx := by
    let h := s.localIso.symm ⟨g, hgH⟩
    have hh : (h : G) ∈ U.vertexGroup := (s.local_vertex h).mpr (by
      simpa only [h, MulEquiv.apply_symm_apply] using hgx)
    have he : s.vertexIso ⟨h, hh⟩ = ⟨g, hgx⟩ := by
      apply Subtype.ext
      exact (s.agree h h.property hh).trans
        (congrArg (fun a : U'.H => (a : G')) (s.localIso.apply_symm_apply ⟨g, hgH⟩))
    exact congrArg (fun a : U.vertexGroup => (a : G))
      ((congrArg s.vertexIso.symm he).symm.trans (s.vertexIso.symm_apply_apply _))
  local_vertex h := by simpa using (s.local_vertex (s.localIso.symm h)).symm
  edge a := by simpa using (s.edge (s.vertexIso.symm a)).symm
  local_edge h := by simpa using (s.local_edge (s.localIso.symm h)).symm

/-- The inverse similarity satisfies the edge-reversing conjugation identity. -/
theorem isEquivalence_symm (hs : s.IsEquivalence) : s.symm.IsEquivalence := by
  obtain ⟨t, htx, hty, ht⟩ := hs
  obtain ⟨htx', hty'⟩ := s.map_swap t htx hty
  refine ⟨s.localIso t, htx', hty', ?_⟩
  intro b
  let a := s.edgeIso.symm b
  have he : (s.edgeIso a : G') = (b : G') :=
    congrArg (fun c : U'.edgeGroup => (c : G')) (s.edgeIso.apply_symm_apply b)
  have hv : s.vertexIso ⟨a, a.property.1⟩ = ⟨b, b.property.1⟩ := Subtype.ext he
  have hc : s.vertexIso ⟨(t : G) * a * (t : G)⁻¹,
      (U.conj_mem_edgeGroup htx hty a.property).1⟩ =
      ⟨(s.localIso t : G') * b * (s.localIso t : G')⁻¹,
        (U'.conj_mem_edgeGroup htx' hty' b.property).1⟩ := by
    apply Subtype.ext
    exact (ht a).trans (by rw [show (s.vertexIso ⟨a, a.property.1⟩ : G') = (b : G') from he])
  have hinv := congrArg s.vertexIso.symm hc
  have hvinv := congrArg s.vertexIso.symm hv
  simp only [MulEquiv.symm_apply_apply] at hinv hvinv
  change (s.vertexIso.symm _ : G) =
    (s.localIso.symm (s.localIso t) : G) * (s.vertexIso.symm ⟨b, b.property.1⟩ : G) *
      (s.localIso.symm (s.localIso t) : G)⁻¹
  rw [MulEquiv.symm_apply_apply, ← hinv, ← hvinv]


/-- Recognition when the simple model and its cycle base are the source of the similarity. -/
noncomputable def recognitionEquivOfSourceBase [IsSimpleGroup G]
    (hs : s.IsEquivalence) (hb : U.IsBase) : G ≃* G' :=
  (s.symm.recognitionEquiv (s.isEquivalence_symm hs) hb).symm

/-- Recognition from a source base extends the given vertex-stabilizer isomorphism. -/
@[simp] theorem recognitionEquivOfSourceBase_onVertex [IsSimpleGroup G]
    (hs : s.IsEquivalence) (hb : U.IsBase) (a : U.vertexGroup) :
    s.recognitionEquivOfSourceBase hs hb a = (s.vertexIso a : G') := by
  change (s.symm.recognitionEquiv (s.isEquivalence_symm hs) hb).symm (a : G) = _
  apply (s.symm.recognitionEquiv (s.isEquivalence_symm hs) hb).injective
  rw [MulEquiv.apply_symm_apply]
  simpa only [symm, MulEquiv.symm_apply_apply] using
    (s.symm.recognitionEquiv_onVertex (s.isEquivalence_symm hs) hb (s.vertexIso a)).symm

/-- Recognition from a source base extends the given local-group isomorphism. -/
@[simp] theorem recognitionEquivOfSourceBase_onLocal [IsSimpleGroup G]
    (hs : s.IsEquivalence) (hb : U.IsBase) (a : U.H) :
    s.recognitionEquivOfSourceBase hs hb a = (s.localIso a : G') := by
  change (s.symm.recognitionEquiv (s.isEquivalence_symm hs) hb).symm (a : G) = _
  apply (s.symm.recognitionEquiv (s.isEquivalence_symm hs) hb).injective
  rw [MulEquiv.apply_symm_apply]
  simpa only [symm, MulEquiv.symm_apply_apply] using
    (s.symm.recognitionEquiv_onLocal (s.isEquivalence_symm hs) hb (s.localIso a)).symm

/-- The isomorphism extending the local comparisons is unique when the source is simple and has a base. -/
theorem existsUnique_mulEquiv_of_isEquivalence_of_sourceBase [IsSimpleGroup G]
    (hs : s.IsEquivalence) (hb : U.IsBase) :
    ∃! e : G ≃* G',
      (∀ a : U.vertexGroup, e a = (s.vertexIso a : G')) ∧
      (∀ a : U.H, e a = (s.localIso a : G')) := by
  refine ⟨s.recognitionEquivOfSourceBase hs hb,
    ⟨s.recognitionEquivOfSourceBase_onVertex hs hb,
      s.recognitionEquivOfSourceBase_onLocal hs hb⟩, ?_⟩
  intro e he
  apply MulEquiv.toMonoidHom_injective
  exact U.hom_ext _ _
    (fun a => (he.2 a).trans (s.recognitionEquivOfSourceBase_onLocal hs hb a).symm)
    (fun a => (he.1 a).trans (s.recognitionEquivOfSourceBase_onVertex hs hb a).symm)

/-- Recognition from a simple target with a simply connected graph and one local triangle orbit. -/
noncomputable def recognitionEquivOfTriangleOrbit [IsSimpleGroup G']
    (hs : s.IsEquivalence) (T : U'.LocalTriangle)
    (hsc : U'.graph.TriangleSimplyConnected) (ht : T.IsTriangleOrbit) : G ≃* G' :=
  s.recognitionEquiv hs (T.isBase hsc ht)

/-- Triangle-orbit recognition extends the vertex comparison. -/
@[simp] theorem recognitionEquivOfTriangleOrbit_onVertex [IsSimpleGroup G']
    (hs : s.IsEquivalence) (T : U'.LocalTriangle)
    (hsc : U'.graph.TriangleSimplyConnected) (ht : T.IsTriangleOrbit)
    (a : U.vertexGroup) :
    s.recognitionEquivOfTriangleOrbit hs T hsc ht a = (s.vertexIso a : G') :=
  s.recognitionEquiv_onVertex hs (T.isBase hsc ht) a

/-- Triangle-orbit recognition extends the local comparison. -/
@[simp] theorem recognitionEquivOfTriangleOrbit_onLocal [IsSimpleGroup G']
    (hs : s.IsEquivalence) (T : U'.LocalTriangle)
    (hsc : U'.graph.TriangleSimplyConnected) (ht : T.IsTriangleOrbit) (a : U.H) :
    s.recognitionEquivOfTriangleOrbit hs T hsc ht a = (s.localIso a : G') :=
  s.recognitionEquiv_onLocal hs (T.isBase hsc ht) a

/-- The F.5 comparison direction: a simple source model with a triangle base identifies the target group. -/
noncomputable def recognitionEquivOfSourceTriangleOrbit [IsSimpleGroup G]
    (hs : s.IsEquivalence) (T : U.LocalTriangle)
    (hsc : U.graph.TriangleSimplyConnected) (ht : T.IsTriangleOrbit) : G ≃* G' :=
  s.recognitionEquivOfSourceBase hs (T.isBase hsc ht)

/-- Recognition in the model-to-source direction extends the prescribed vertex comparison. -/
@[simp] theorem recognitionEquivOfSourceTriangleOrbit_onVertex [IsSimpleGroup G]
    (hs : s.IsEquivalence) (T : U.LocalTriangle)
    (hsc : U.graph.TriangleSimplyConnected) (ht : T.IsTriangleOrbit)
    (a : U.vertexGroup) :
    s.recognitionEquivOfSourceTriangleOrbit hs T hsc ht a = (s.vertexIso a : G') :=
  s.recognitionEquivOfSourceBase_onVertex hs (T.isBase hsc ht) a

/-- Recognition in the model-to-source direction extends the prescribed local comparison. -/
@[simp] theorem recognitionEquivOfSourceTriangleOrbit_onLocal [IsSimpleGroup G]
    (hs : s.IsEquivalence) (T : U.LocalTriangle)
    (hsc : U.graph.TriangleSimplyConnected) (ht : T.IsTriangleOrbit) (a : U.H) :
    s.recognitionEquivOfSourceTriangleOrbit hs T hsc ht a = (s.localIso a : G') :=
  s.recognitionEquivOfSourceBase_onLocal hs (T.isBase hsc ht) a

end Similarity
end Theory.GroupTheory.GraphUniquenessSystem
