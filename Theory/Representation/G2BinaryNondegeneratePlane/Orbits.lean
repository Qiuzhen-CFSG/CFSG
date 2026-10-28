module

public import Theory.Representation.G2BinaryNondegeneratePlane.Stabilizer
public import Theory.Representation.G2NaturalTransitivity
public import Theory.AtlasPort.LinearGroups.G2.VectorStabilizer

/-!
# Transitivity on the nondegenerate binary planes

First move one vector to a fixed null vector. A singular representative of its
partner has polar pairing one; the literal octonion partner reducer fixes the
first vector and moves the partner to its opposite. Thus the full G₂(2) group
is transitive on ordered symplectic pairs and on nondegenerate planes in the
actual six-dimensional quotient. No orbit census is assumed.

Source: Aschbacher–Smith, Lemma 13.3.12, printed p.889 (citing Asc87, 5.1).
The imported octonion coordinate conventions retain the ATLAS attribution.
-/

@[expose] public noncomputable section
open Atlas.SplitOctonion Module Submodule
namespace Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Restricted.NaturalCoordinates Representation.BinaryOffender

private theorem rho_projection (g : Model K) (x : TraceZero K) :
    rho g (Atlas.G2.Restricted.NaturalCoordinates.projection K x)=
      Atlas.G2.Restricted.NaturalCoordinates.projection K (traceZeroAction K g x) := by
  change rho g (equiv K (mk K x))=equiv K (Natural.action K g (mk K x))
  change equiv K (Natural.action K g ((equiv K).symm (equiv K (mk K x))))=_
  rw [LinearEquiv.symm_apply_apply]

private theorem rho_first (g : Model K)
    (h : g.val (basisVector 0)=basisVector 0) : rho g firstVector=firstVector := by
  let x : TraceZero K := ⟨basisVector 0,by simp [mem_traceZero,SplitOctonion.trace,basisVector]⟩
  change rho g (Atlas.G2.Restricted.NaturalCoordinates.projection K x)=_
  rw [rho_projection]
  have he : traceZeroAction K g x=x := Subtype.ext h
  rw [he]
  rfl

theorem ordered_pair_transitive (v w : W) (hvw : form v w=1) :
    ∃g : Model K,rho g v=firstVector ∧ rho g w=secondVector := by
  have hv : v≠0 := by intro he;simp [he] at hvw
  have hv' : (equiv K).symm v≠0 := fun he => hv ((equiv K).symm.map_eq_zero_iff.mp he)
  have hfirst : (equiv K).symm firstVector≠0 := by
    intro he
    have hz := (equiv K).symm.map_eq_zero_iff.mp he
    have hi := congrFun hz 0
    exact one_ne_zero hi
  obtain ⟨g,hg⟩ := Natural.action_transitive hv' hfirst
  have hg0 : rho g v=firstVector := by
    have he := congrArg (equiv K) hg
    change rho g v=(equiv K) ((equiv K).symm firstVector) at he
    simpa only [LinearEquiv.apply_symm_apply] using he
  have hg5 : (rho g w) 5=1 := by
    have hh := (form_invariant g v w).trans hvw
    rw [hg0,form_apply] at hh
    simpa [firstVector] using hh
  obtain ⟨y,hy,he⟩ := Natural.exists_singular_representative ((equiv K).symm (rho g w))
  have hcoord : Atlas.G2.Restricted.NaturalCoordinates.projection K y=rho g w := by
    have hh := congrArg (equiv K) he
    simpa only [equiv_apply,coordinates_mk,LinearEquiv.apply_symm_apply] using hh
  have hy7 : y.val 7=1 := (congrFun hcoord 5).trans hg5
  let c := chartReducer y.val
  have hc0 : rho c firstVector=firstVector := rho_first c (chartReducer_fixes_first _)
  have hcy : c.val y.val=basisVector 7 := by
    have hh := chartReducer_eq y.val y.property hy (hy7 ▸ one_ne_zero)
    simpa [c,hy7,basisVector] using hh
  have hc5 : rho c (rho g w)=secondVector := by
    rw [←hcoord,rho_projection]
    have hh : traceZeroAction K c y=⟨basisVector 7,by simp [mem_traceZero,SplitOctonion.trace,basisVector]⟩ :=
      Subtype.ext hcy
    rw [hh]
    rfl
  refine ⟨c*g,?_,?_⟩
  · rw [map_mul,Module.End.mul_apply,hg0,hc0]
  · rw [map_mul,Module.End.mul_apply,hc5]

theorem nondegenerate_plane_transitive (P : Submodule K W)
    (hd : finrank K P=2) (hn : (form.restrict P).Nondegenerate) :
    ∃g : Model K,P.map (rho g)=plane := by
  have hP : P≠⊥ := by intro he;rw [he,finrank_bot] at hd;omega
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hex : ∃y∈P,form x y≠0 := by
    by_contra! hh
    have he : (⟨x,hx⟩ : P)=0 := hn.1 _ (fun y => hh y y.property)
    exact hx0 (congrArg Subtype.val he)
  obtain ⟨y,hy,hxy⟩ := hex
  have hp : form x y=1 := (by decide : ∀a:K,a≠0→a=1) _ hxy
  obtain ⟨g,hg0,hg5⟩ := ordered_pair_transitive x y hp
  have hspan : span K {x,y}=P := by
    apply Submodule.eq_of_le_of_finrank_eq
      (span_le.mpr (by intro z hz;rcases (show z=x∨z=y by simpa using hz) with rfl|rfl <;> assumption))
    rw [(form.span_pair_nondegenerate_of_pairing_ne_zero form_alternating x y hxy).1,hd]
  refine ⟨g,?_⟩
  rw [←hspan,Submodule.map_span]
  simp only [Set.image_pair,hg0,hg5]
  rfl
end Atlas.G2.Natural.BinaryNondegeneratePlane
