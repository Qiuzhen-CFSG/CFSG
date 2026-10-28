module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.KernelActions
/-!
# The full original edge-reversal equation

The edge fixer is B=K(S∩B), with S∩B contained in H. KernelActions proves
the required conjugation equation on K; overlap agreement proves it on
S∩B. The two homomorphisms therefore agree on all B. Conjugation uses the
literal original t, its square in M, and the left-coset convention t⁻¹.

Combining this with the constructed Section 8 comparisons gives local maps
and the full reversal equation as outputs. The scalar cubic, central
involution, six-cover projection, M24 conjugator and both flags are retained.

Source: Aschbacher--Segev (1991), section 8, pp.605--607, and (5.1)(2).
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry SourceCycleBase GraphUniquenessSystem
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsTypeJ4 z'}
variable (a' : SourceIncidence.LocalData h')
/-- Conjugation by the actual reversal preserves its pointwise edge fixer.
The inverse in the definition of the edge is required by left cosets. -/
theorem lineEdge_conj_mem (t : G) (hsq : t*t ∈ a.P.M)
    (b : G) (hb : b ∈ lineEdgeGroup a t) : t*b*t⁻¹ ∈ lineEdgeGroup a t := by
  refine ⟨?_,?_⟩
  · have hh := a.P.M.mul_mem (a.P.M.mul_mem hsq hb.2) (a.P.M.inv_mem hsq)
    change (t*t)*(t⁻¹*b*(t⁻¹)⁻¹)*(t*t)⁻¹ ∈ a.P.M at hh
    have he : (t*t)*(t⁻¹*b*(t⁻¹)⁻¹)*(t*t)⁻¹=t*b*t⁻¹ := by group
    rwa [he] at hh
  · change t⁻¹*(t*b*t⁻¹)*(t⁻¹)⁻¹ ∈ a.P.M
    have he : t⁻¹*(t*b*t⁻¹)*(t⁻¹)⁻¹=b := by group
    rw [he]
    exact hb.1

private def edgeConjugationHom (t : G) (hsq : t*t ∈ a.P.M) : lineEdgeGroup a t →* a.P.M where
  toFun b := ⟨t*b*t⁻¹,(lineEdge_conj_mem a t hsq b b.property).1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' b c := Subtype.ext (by simp [mul_assoc])

/-- The complete edge-reversal equation, obtained from the constructed
central-residual calculation on K and the source factorization of B. -/
theorem compatible_edge_conjugation
    (M : a.P.M ≃* a'.P.M) (H : centralizer z ≃* centralizer z')
    (hK : (a.d.K.subgroupOf a.P.M).map M.toMonoidHom=a'.d.K.subgroupOf a'.P.M)
    (hL : (a.L.G₂.subgroupOf (centralizer z)).map H.toMonoidHom=
      a'.L.G₂.subgroupOf (centralizer z'))
    (agree : ∀ (k : G) (hkM : k ∈ a.P.M) (hkH : k ∈ centralizer z),
      (M ⟨k,hkM⟩ : G')=(H ⟨k,hkH⟩ : G'))
    (t : centralizer z) (ht : (t : G) ∈ a.L.G₂) (hnt : (t : G) ∉ a.P.M)
    (hsq : (t : G)*(t : G) ∈ a.P.M) (b : lineEdgeGroup a t) :
    (M ⟨(t : G)*b*(t : G)⁻¹,(lineEdge_conj_mem a t hsq b b.property).1⟩ : G') =
      (H t : G')*(M ⟨b,b.property.1⟩ : G')*(H t : G')⁻¹ := by
  let B := lineEdgeGroup a t
  let f : B →* G' := a'.P.M.subtype.comp (M.toMonoidHom.comp (edgeConjugationHom a t hsq))
  let g : B →* G' := (MulAut.conj (H t : G')).toMonoidHom.comp
    (a'.P.M.subtype.comp (M.toMonoidHom.comp (inclusion inf_le_left)))
  have hgen : B ≤ (f.eqLocus g).map B.subtype := by
    conv_lhs => rw [show B=a.d.K ⊔ (a.d.S ⊓ B) from lineEdgeGroup_factorization a t ht hnt]
    apply sup_le
    · intro k hk
      have hkB := K_le_lineEdgeGroup a t ht hk
      refine ⟨⟨k,hkB⟩,?_,rfl⟩
      exact compatible_kernel_conjugation a a' M H hK hL agree ⟨t,ht,t.property⟩ ⟨k,hk⟩
    · rintro k ⟨hkS,hkB⟩
      refine ⟨⟨k,hkB⟩,?_,rfl⟩
      have hkH : k ∈ centralizer z := a.d.S_le_point_centralizer (a.d.markedPoint 0).property hkS
      have htkH : (t : G)*k*(t : G)⁻¹ ∈ centralizer z :=
        (centralizer z).mul_mem ((centralizer z).mul_mem t.property hkH)
          ((centralizer z).inv_mem t.property)
      change (M ⟨(t : G)*k*(t : G)⁻¹,_⟩ : G')=(H t : G')*(M ⟨k,_⟩ : G')*(H t : G')⁻¹
      rw [agree _ _ hkH,agree _ _ htkH]
      change (H (t*⟨k,hkH⟩*t⁻¹) : G')=_
      simp only [map_mul,map_inv,coe_mul,coe_inv]
  obtain ⟨u,hu,he⟩ := hgen b.property
  have hub : u=b := Subtype.ext he
  subst u
  exact hu


/-- Construct local isomorphisms that agree on the literal overlap and
simultaneously preserve the entire original edge fixer. The full conjugation
equation is proved for every element of the edge fixer.
The target edge uses the image of the original reversal element. -/
theorem exists_compatible_edge_reversal (d : CubicNormalizerData a) (d' : CubicNormalizerData a')
    (t : centralizer z) (ht : (t : G) ∈ a.L.G₂) (hnt : (t : G) ∉ a.P.M)
    (hsq : (t : G)*(t : G) ∈ a.P.M) :
    ∃ (C : cubicCentralizerInH a.e a.X ≃* cubicCentralizerInH a'.e a'.X)
      (n : cubicNormalizerInH a'.e a'.X) (g : Sporadic.Mathieu.M24)
      (φM : a.P.M ≃* a'.P.M) (φH : centralizer z ≃* centralizer z'),
      (∀ c, cubicNativeProjection h' a'.e a'.X (C c)=cubicNativeProjection h a.e a.X c) ∧
      φH planeMarker=planeMarker ∧
      (∀ c : cubicCentralizerInH a.e a.X,
        φH c.val=(cubicNormalizerAction a'.e a'.X n (C c)).val) ∧
      (core z).map φH.toMonoidHom=core z' ∧
      (cubicSylowImage a.e a.X).map φH.toMonoidHom=cubicSylowImage a'.e a'.X ∧
      (φM ⟨z,marker_mem_point a⟩ : G')=z' ∧
      (a.L.G₂.subgroupOf (centralizer z)).map φH.toMonoidHom=a'.L.G₂.subgroupOf (centralizer z') ∧
      (a.L.G₂.subgroupOf a.P.M).map φM.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M ∧
      (a.d.K.subgroupOf a.P.M).map φM.toMonoidHom=a'.d.K.subgroupOf a'.P.M ∧
      (∀ m, a'.P.projection (φM m)=g*a.P.projection m*g⁻¹) ∧
      (∀ (k : G) (hkM : k ∈ a.P.M) (hkH : k ∈ centralizer z),
        (φM ⟨k,hkM⟩ : G')=(φH ⟨k,hkH⟩ : G')) ∧
      ((lineEdgeGroup a t).subgroupOf a.P.M).map φM.toMonoidHom =
        (lineEdgeGroup a' (φH t)).subgroupOf a'.P.M ∧
      ∀ b : lineEdgeGroup a t,
        (φM ⟨(t : G)*b*(t : G)⁻¹,(lineEdge_conj_mem a t hsq b b.property).1⟩ : G') =
          (φH t : G')*(φM ⟨b,b.property.1⟩ : G')*(φH t : G')⁻¹ := by
  obtain ⟨C,n,g,M,H,hC,hz,hHC,hQ,hA,hMz,hHL,hML,hK,hproj,hagree,hB⟩ :=
    exists_compatible_edge_equivs a a' d d' t ht hnt
  exact ⟨C,n,g,M,H,hC,hz,hHC,hQ,hA,hMz,hHL,hML,hK,hproj,hagree,hB,
    compatible_edge_conjugation a a' M H hK hHL hagree t ht hnt hsq⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
