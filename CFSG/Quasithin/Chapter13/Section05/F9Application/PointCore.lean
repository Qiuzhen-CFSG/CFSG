module

public import CFSG.Quasithin.Chapter13.Section05.F9Application.CommutatorImage
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.Conjugation
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# The original conjugate action in the point core

The 13.5.7 seed-displacement hypothesis puts the literal action of Vᵍ
inside the two-core of its actual point stabilizer. The proof uses the
three-step natural flag and faithful unipotence, retaining ordinary and
covered A₆ cases. The commutator-in-intersection hypothesis then bounds
this action by four and, at equality, marks its moved plane together
with the original point. No point-core or moved-plane premise is added.

Source: Aschbacher--Smith, proof of 13.5.7, printed pp.917--918. The
separate 13.5.6 fusion argument must exclude the order-four alternative.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.QuadraticSource
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing PointAction PointCoreKernel
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem conjugate_pointCore_placement (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hs:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁) :
    ∃a:alternatingGroup (Fin 6),
      image d V₁=canonicalLine.map (naturalRepresentation (Fin 6) a.val) ∧
      (conjugateAction d g (conjugate_le_local d g hg hc hs)).range ≤
        pointCore.map (MulAut.conj a.val).toMonoidHom := by
  have hline : V₁≤V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hdim:=image_dim d V₁ hline 1 d.line_card
  have hP : image d V₁≠⊥ := by intro he;rw [he,finrank_bot] at hdim;contradiction
  obtain ⟨v,hv,hvn⟩:= (Submodule.ne_bot_iff _).mp hP
  have hp : image d V₁=Submodule.span (ZMod 2) {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hv hvn
  obtain ⟨a,ha⟩:=NaturalTransport.exists_even_image v hvn
  have hpa : image d V₁=canonicalLine.map (naturalRepresentation (Fin 6) a.val) := by
    rw [canonicalLine,Submodule.map_span,Set.image_singleton,ha,hp]
  refine ⟨a,hpa,?_⟩
  let A:=V.map (MulAut.conj g).toMonoidHom
  let hA:=conjugate_le_local d g hg hc hs
  have hAG : A≤G₁ := by
    rintro _ ⟨y,hy,rfl⟩
    have hyG : y∈G₁ := by
      rw [d.first_normalizer]
      exact d.line_stable (d.chosen.le_sylow hy)
    exact G₁.mul_mem (G₁.mul_mem hg hyG) (G₁.inv_mem hg)
  rintro _ ⟨x,rfl⟩
  apply mem_conjugate_pointCore_of_seed_displacement a.val _ v ha
  · obtain ⟨y,hy,hyv⟩ := (mem_image d V₁ v).mp hv
    rw [←hyv]
    change naturalRepresentation (Fin 6) (permutation d (inclusion hA x)) (d.coordinate y).toAdd = _
    rw [←conjugation d]
    apply congrArg (fun y:V=>(d.coordinate y).toAdd)
    apply Subtype.ext
    have hxC : x.val∈centralizer (V₁:Set G) :=
      normalizer_le_centralizer_of_card_two V₁ d.line_card (d.first_normalizer ▸ hAG x.property)
    change x.val*y.val*x.val⁻¹=y.val
    rw [←mem_centralizer_iff.mp hxC y.val hy,mul_inv_cancel_right]
  · intro w hw
    have hDw : w∈image d V₃ := by
      rw [seed_perpendicular d,hp]
      exact hw
    obtain ⟨y,hy,rfl⟩ := (mem_image d V₃ w).mp hDw
    let c : V := V.normalizerMonoidHom ⟨x.val,(hA x.property).2⟩ y * y⁻¹
    have he : naturalRepresentation (Fin 6) (conjugateAction d g hA x) (d.coordinate y).toAdd -
        (d.coordinate y).toAdd = (d.coordinate c).toAdd := by
      change naturalRepresentation (Fin 6) (permutation d (inclusion hA x)) (d.coordinate y).toAdd -
        (d.coordinate y).toAdd = _
      rw [←conjugation d]
      change _=(d.coordinate (V.normalizerMonoidHom _ y*y⁻¹)).toAdd
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,sub_eq_add_neg]
      rfl
    rw [he,←hp]
    apply (mem_image d V₁ _).mpr
    refine ⟨c,?_,rfl⟩
    apply hs
    rw [commutator_comm]
    exact commutator_mem_commutator x.property hy

theorem conjugate_action_card_le_four (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hs:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁) :
    Nat.card (conjugateAction d g (conjugate_le_local d g hg hc hs)).range≤4 := by
  obtain ⟨a,_,ha⟩:=conjugate_pointCore_placement d g hg hc hs
  exact QuadraticPointCore.conjugate_core_bound _ a.val ha
    (conjugate_quadratic_source d g hg hc hcomm hs)

theorem conjugate_action_four_plane (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hs:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁)
    (hcard:Nat.card (conjugateAction d g (conjugate_le_local d g hg hc hs)).range=4) :
    ∃a:alternatingGroup (Fin 6),
      image d V₁=canonicalLine.map (naturalRepresentation (Fin 6) a.val) ∧
      Representation.BinaryOffender.subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
        (conjugateAction d g (conjugate_le_local d g hg hc hs)).range=
      canonicalPlane.map (naturalRepresentation (Fin 6) a.val) := by
  obtain ⟨a,hline,ha⟩:=conjugate_pointCore_placement d g hg hc hs
  obtain ⟨b,hline',hplane⟩:=QuadraticPointCore.conjugate_core_four_flag _ a ha
    (conjugate_quadratic_source d g hg hc hcomm hs) hcard
  exact ⟨b,hline.trans hline',hplane⟩
/-- The plane in the quadratic alternative is the image of the literal
ambient commutator, with the same marking of its original point. -/
theorem conjugate_commutator_four_plane (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hs:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁)
    (hcard:Nat.card (conjugateAction d g (conjugate_le_local d g hg hc hs)).range=4) :
    ∃a:alternatingGroup (Fin 6),
      image d V₁=canonicalLine.map (naturalRepresentation (Fin 6) a.val) ∧
      image d ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=
        canonicalPlane.map (naturalRepresentation (Fin 6) a.val) := by
  rw [image_commutator_self d _ (conjugate_le_local d g hg hc hs)]
  exact conjugate_action_four_plane d g hg hc hcomm hs hcard

end CFSG.Quasithin.Chapter13.Section05.QuadraticSource
