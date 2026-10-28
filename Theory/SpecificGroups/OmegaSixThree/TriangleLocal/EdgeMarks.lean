module
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.Marks

/-!
# The marked F.5 edge and its local reversal

The graph involution has a negative two-space with exactly the two chosen
norm-minus-one projective points. Inside the first vertex stabilizer, commuting
with that involution is therefore equivalent to fixing the other endpoint.
The converse follows by writing the involution as the product of the two
orthogonal reflections. A first-factor four-cycle in the literal local
coordinates supplies an edge reversal whose square is the graph involution.

Only the nine vectors in the negative two-space are inspected; no centralizer
classification or full group enumeration is used.
Source: Aschbacher--Smith F.5.7, printed p.303.
-/

@[expose] public section

namespace OmegaSixThree.TriangleLocal
open SixTernaryCoordinates OrthogonalityGraph
open Theory.GroupTheory.GraphUniquenessSystem

private theorem graph_negative_vectors (v : Space) (h : graphInvolution v = -v)
    (hq : quadratic v = -1) : signed v (e 5) ∨ signed v (e 0-e 1) := by
  obtain ⟨h0,hv2,hv3,hv4⟩ := (graphInvolution_neg_coordinates v).mp h
  have hv : v = ![v 0,-v 0,0,0,0,v 5] := by
    ext i
    fin_cases i <;> simp [h0,hv2,hv3,hv4]
  rw [hv] at hq ⊢
  exact (show ∀ a b : ZMod 3, quadratic ![a,-a,0,0,0,b] = -1 →
    signed ![a,-a,0,0,0,b] (e 5) ∨ signed ![a,-a,0,0,0,b] (e 0-e 1) by
      unfold signed; decide +kernel) _ _ hq

private theorem reflection_signed {v w : Space} (h : signed v w)
    (hv : quadratic v = -1) (hw : quadratic w = -1) :
    reflection (-1) (by decide) v hv = reflection (-1) (by decide) w hw := by
  rcases h with rfl | rfl
  · rfl
  · ext x i
    change (reflect (-1) (-w) x) i = (reflect (-1) w x) i
    simp only [reflect,Pi.add_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul,pairing]
    ring

private theorem graph_reflections : graphInvolution =
    reflection (-1) (by decide) (e 5) (by decide +kernel) *
      reflection (-1) (by decide) (e 0-e 1) (by decide +kernel) := by
  ext v i
  (fin_cases i <;> simp [reflection,reflect,pairing,e,LinearEquiv.mul_apply])
  ring_nf
  simp [show (2 : ZMod 3) = -1 by decide]

private theorem fixes_edge_commutes (g : omegaPlusSixThree)
    (hx : g • standardFirst = standardFirst) (hy : g • standardSecond = standardSecond) :
    g * vertexGraphInvolution = vertexGraphInvolution * g := by
  have hx' := (point_eq_iff _ _ _ _).mp hx
  have hy' := (point_eq_iff _ _ _ _).mp hy
  have ho : g.val ∈ orthogonalGroup := omegaPlusSixThree_le_orthogonalGroup g.property
  have hc (v : Space) (hv : quadratic v = -1) (hs : signed (g.val v) v) :
      g.val * reflection (-1) (by decide) v hv * g.val⁻¹ =
        reflection (-1) (by decide) v hv := by
    rw [reflection_conjugate (-1) (by decide) v hv ⟨g.val,ho⟩]
    exact reflection_signed hs _ _
  apply Subtype.ext
  change g.val * graphInvolution = graphInvolution * g.val
  apply (mul_inv_eq_iff_eq_mul).mp
  rw [graph_reflections]
  rw [show ∀ a b : LinearGroup, g.val * (a*b) * g.val⁻¹ =
    (g.val*a*g.val⁻¹)*(g.val*b*g.val⁻¹) by intro a b; group]
  rw [hc _ _ hx', hc _ _ hy']

private theorem commutes_graph_edge_orbit (g : omegaPlusSixThree)
    (h : g * vertexGraphInvolution = vertexGraphInvolution * g) :
    g • standardFirst = standardFirst ∨ g • standardFirst = standardSecond := by
  have hv : graphInvolution (g.val (e 5)) = -(g.val (e 5)) := by
    have hh := congrArg (fun x : omegaPlusSixThree => x.val (e 5)) h
    change g.val (graphInvolution (e 5)) = graphInvolution (g.val (e 5)) at hh
    have he : graphInvolution (e 5) = -(e 5) := by decide +kernel
    rw [he,map_neg] at hh
    exact hh.symm
  have hq : quadratic (g.val (e 5)) = -1 :=
    (omegaPlusSixThree_le_orthogonalGroup g.property (e 5)).trans (by decide +kernel)
  rcases graph_negative_vectors _ hv hq with hx | hy
  · exact Or.inl ((point_eq_iff _ _ _ _).mpr hx)
  · exact Or.inr ((point_eq_iff _ _ _ _).mpr hy)

private theorem fixes_first_commutes_fixes_second (g : omegaPlusSixThree)
    (hx : g • standardFirst = standardFirst)
    (h : g * vertexGraphInvolution = vertexGraphInvolution * g) :
    g • standardSecond = standardSecond := by
  have hv : graphInvolution (g.val (e 0-e 1)) = -(g.val (e 0-e 1)) := by
    have hh := congrArg (fun x : omegaPlusSixThree => x.val (e 0-e 1)) h
    change g.val (graphInvolution (e 0-e 1)) = graphInvolution (g.val (e 0-e 1)) at hh
    have he : graphInvolution (e 0-e 1) = -(e 0-e 1) := by decide +kernel
    rw [he,map_neg] at hh
    exact hh.symm
  have hq : quadratic (g.val (e 0-e 1)) = -1 :=
    (omegaPlusSixThree_le_orthogonalGroup g.property (e 0-e 1)).trans (by decide +kernel)
  rcases graph_negative_vectors _ hv hq with hy | hy
  · have he : g • standardSecond = g • standardFirst :=
      ((point_eq_iff _ _ _ _).mpr hy).trans hx.symm
    exact (standard_adjacent.1.ne ((MulAction.injective g) he).symm).elim
  · exact (point_eq_iff _ _ _ _).mpr hy

/-- The edge fixer is the graph-involution centralizer inside the first vertex. -/
theorem edgeFixer_eq_vertex_inf_graph_centralizer :
    edgeFixer omegaPlusSixThree standardFirst standardSecond =
      MulAction.stabilizer omegaPlusSixThree standardFirst ⊓
        Subgroup.centralizer ({vertexGraphInvolution} : Set omegaPlusSixThree) := by
  ext g
  change (g • standardFirst = standardFirst ∧ g • standardSecond = standardSecond) ↔ _
  constructor
  · rintro ⟨hx,hy⟩
    exact ⟨hx,Subgroup.mem_centralizer_singleton_iff.mpr (fixes_edge_commutes g hx hy)⟩
  · rintro ⟨hx,hc⟩
    exact ⟨hx,fixes_first_commutes_fixes_second g hx
      (Subgroup.mem_centralizer_singleton_iff.mp hc)⟩

/-- The four-cycle `(0 1 3 2)` with square the marked graph involution. -/
def reversalPermutation : Four := Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 2

/-- A literal local element, selected through its faithful four-line actions. -/
noncomputable def edgeReversal : H := productEquiv.symm (reversalPermutation,1)

theorem edgeReversal_image : productEquiv edgeReversal = (reversalPermutation,1) :=
  productEquiv.apply_symm_apply _

theorem edgeReversal_sq : edgeReversal^2 = graphElement := by
  apply productEquiv.injective
  rw [map_pow,edgeReversal_image,graphElement_image]
  decide +kernel

theorem edgeReversal_not_mem_vertexLocal : edgeReversal ∉ vertexLocal := by
  rw [vertexLocal_eq]
  change ¬ productEquiv edgeReversal ∈ square.prod ⊤
  rw [edgeReversal_image]
  intro hh
  exact (show reversalPermutation ∉ square by decide +kernel) hh.1

theorem edgeReversal_first : (edgeReversal : omegaPlusSixThree) • standardFirst = standardSecond := by
  have hc : (edgeReversal : omegaPlusSixThree) * vertexGraphInvolution =
      vertexGraphInvolution * edgeReversal := by
    have hh : edgeReversal * graphElement = graphElement * edgeReversal := by
      rw [←edgeReversal_sq,pow_two]
      exact (mul_assoc _ _ _).symm
    exact congrArg Subtype.val hh
  rcases commutes_graph_edge_orbit edgeReversal hc with hx | hx
  · exact (edgeReversal_not_mem_vertexLocal hx).elim
  · exact hx

theorem edgeReversal_second : (edgeReversal : omegaPlusSixThree) • standardSecond = standardFirst := by
  rw [←edgeReversal_first,←mul_smul]
  have hh : (edgeReversal : omegaPlusSixThree) * edgeReversal = vertexGraphInvolution :=
    congrArg Subtype.val (by simpa only [pow_two] using edgeReversal_sq)
  rw [hh]
  apply (point_eq_iff _ _ _ _).mpr
  exact Or.inr (by decide +kernel)

/-- The chosen reversal centralizes the independently marked second factor. -/
theorem edgeReversal_commutes_complement (g : H) (hg : g ∈ complementFactor) :
    edgeReversal * g = g * edgeReversal := by
  have hg1 : (productEquiv g).1 = 1 := hg.1
  apply productEquiv.injective
  rw [map_mul,map_mul,edgeReversal_image]
  apply Prod.ext <;> simp [hg1]

end OmegaSixThree.TriangleLocal
