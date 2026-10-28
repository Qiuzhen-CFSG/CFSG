module

public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion

/-!+# Recognition from a simple target uniqueness system

An equivalence with a simple target whose local graph is a cycle base identifies
the acting groups. The target base supplies a homomorphism from the target to
the source extending the inverse local comparisons. Condition (U) makes it
surjective, and simplicity makes it injective because an edge reversal has
nontrivial image. Its inverse is the unique isomorphism extending the original
vertex and local comparisons.

Only the target needs a base. In particular the source graph need not be known
to be simply connected. The rigidity variant discharges equivalence by the
pointwise automorphism centralizer criterion of Theorem 37.9. The generation
hypotheses are the three fields `System.generate`, `System.vertex_generate`,
and `System.local_generate`; the local comparison hypotheses are the fields of
`Similarity`.

Source: Aschbacher, *Sporadic Groups* (1994), 37.5–37.6, 37.9, and Exercise
13.1(b); Aschbacher–Smith, §5.2, proof of Theorem 5.2.10, printed pp.657–658.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem.Similarity

universe u v u' v'
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable {G' : Type u'} {V' : Type v'} [Group G'] [MulAction G' V']
variable {U : System G V} {U' : System G' V'} (s : Similarity U U')
variable [IsSimpleGroup G']

/-- Recognition by an equivalent simple target with a cycle base. -/
noncomputable def recognitionEquiv (hs : s.IsEquivalence) (hb : U'.IsBase) : G ≃* G' :=
  (Classical.choice (s.nonempty_extension_of_isEquivalence_of_isBase hs hb)).mulEquiv.symm

/-- Recognition extends the prescribed vertex-stabilizer comparison. -/
@[simp] theorem recognitionEquiv_onVertex (hs : s.IsEquivalence) (hb : U'.IsBase)
    (a : U.vertexGroup) : s.recognitionEquiv hs hb a = (s.vertexIso a : G') := by
  let f := Classical.choice (s.nonempty_extension_of_isEquivalence_of_isBase hs hb)
  change f.mulEquiv.symm (a : G) = (s.vertexIso a : G')
  apply f.mulEquiv.injective
  exact (f.mulEquiv.apply_symm_apply _).trans (f.onVertex a).symm

/-- Recognition extends the prescribed local-group comparison. -/
@[simp] theorem recognitionEquiv_onLocal (hs : s.IsEquivalence) (hb : U'.IsBase)
    (a : U.H) : s.recognitionEquiv hs hb a = (s.localIso a : G') := by
  let f := Classical.choice (s.nonempty_extension_of_isEquivalence_of_isBase hs hb)
  change f.mulEquiv.symm (a : G) = (s.localIso a : G')
  apply f.mulEquiv.injective
  exact (f.mulEquiv.apply_symm_apply _).trans (f.onLocal a).symm

/-- The group isomorphism extending an equivalence is unique when the target is
simple and its local graph is a base. No source base is assumed. -/
theorem existsUnique_mulEquiv_of_isEquivalence_of_isBase
    (hs : s.IsEquivalence) (hb : U'.IsBase) :
    ∃! e : G ≃* G',
      (∀ a : U.vertexGroup, e a = (s.vertexIso a : G')) ∧
      (∀ a : U.H, e a = (s.localIso a : G')) := by
  refine ⟨s.recognitionEquiv hs hb,
    ⟨s.recognitionEquiv_onVertex hs hb, s.recognitionEquiv_onLocal hs hb⟩, ?_⟩
  intro e he
  apply MulEquiv.toMonoidHom_injective
  exact U.hom_ext _ _
    (fun a => (he.2 a).trans (s.recognitionEquiv_onLocal hs hb a).symm)
    (fun a => (he.1 a).trans (s.recognitionEquiv_onVertex hs hb a).symm)

/-- The specialized 37.9 recognition criterion: compatible local isomorphisms,
rigidity of the edge fixer, and a base for the simple target suffice. -/
theorem existsUnique_mulEquiv_of_rigid_of_isBase
    (hRigid : AutomorphismRigid (U.H.subgroupOf U.edgeGroup)) (hb : U'.IsBase) :
    ∃! e : G ≃* G',
      (∀ a : U.vertexGroup, e a = (s.vertexIso a : G')) ∧
      (∀ a : U.H, e a = (s.localIso a : G')) :=
  s.existsUnique_mulEquiv_of_isEquivalence_of_isBase (s.isEquivalence_of_rigid hRigid) hb

end Theory.GroupTheory.GraphUniquenessSystem.Similarity
