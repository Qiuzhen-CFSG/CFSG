module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperBorel
public import CFSG.Quasithin.ChapterG.Section01.SL2FourRecognition

/-!
# Natural coordinates for the original A₅ upper quotient

The exact root marking and its Borel give a projective orbit from the W
image. Complementarity, displacement bounds and Borel invariance prove
every clause of the projective criterion. The proved G.1.3 theorem then
constructs equivariant coordinates as a sum of natural SL₂(4) planes.
There is no recognition input or fixed-T marking in this implication.

Source: Aschbacher–Smith,G.1.3,G.1.5(3), and G.2.4(6), printed pp.327–334,
as applied in13.5.15 on printed p.920.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperNatural
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceFiveModule SourceUpperStructure SourceUpperAction SourceUpperBorel
open ChapterG.Section02.AlternatingFive.Recognition
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
open ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

theorem natural_coordinates (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L) (hgn : g.val∉D.Gz)
    (hg : g.val∈NormalBranch.K D g.val)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) E)
    (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
      ((NormalBranch.K D g.val).pCoreIn 2) D.V (σ.comp (restrictedActor d hK a hi))) :
    let := (ZMod.algebra F4 2).toModule
    ∃ (m : alternatingGroup (Fin 5)≃*SL(2,F4)) (s : ℕ)
      (q : E≃ₗ[ZMod 2](Fin s→Fin 2→F4)),
      ∀x v j,q (σ x v) j=Matrix.mulVec (m x).val (q v j) := by
  let := (ZMod.algebra F4 2).toModule
  let f := restrictedActor d hK a hi
  let W := D.UH⊓(NormalBranch.K D g.val).pCoreIn 2
  let U := (D.UH.subgroupOf (NormalBranch.K D g.val)).map f
  let k : NormalBranch.K D g.val := ⟨g.val,hg⟩
  obtain ⟨m,hm⟩ := upper_marked_model d h e hseed hn hU g hK a hi
  let τ := σ.comp m.symm.toMonoidHom
  let t := m (f k⁻¹)
  have hne : standardPoint.val≠standardPoint.val.map (Representation.specialLinearNatural 2 t) := by
    intro he
    have ht := mem_root_normalizer_of_map_eq standardPoint.val t he.symm
    change t∈normalizer (RootGroup F4 standardPoint.val:Set SL(2,F4)) at ht
    rw [←hm,←map_normalizer_eq_of_bijective _ m.bijective] at ht
    have hi' := mem_map_equiv.mp ht
    change m.symm (m (f k⁻¹))∈normalizer (U:Set (alternatingGroup (Fin 5))) at hi'
    rw [m.symm_apply_apply,map_inv] at hi'
    exact mover_not_borel d h e hseed hn hU g hgn hg hK hL a hi
      (by simpa only [inv_inv] using (normalizer (U:Set (alternatingGroup (Fin 5)))).inv_mem hi')
  obtain ⟨hcompl,hmove⟩ := upper_marked_complement d h e hseed hn hU g hgn hg hK hL hp a hi
    (σ.comp f) c
  have ht : τ t=σ (f k⁻¹) := by
    change σ (m.symm (m (f k⁻¹)))=σ (f k⁻¹)
    rw [m.symm_apply_apply]
  have hcompl' : IsCompl (c.imageSpace W) ((c.imageSpace W).map (τ t)) := by
    rw [ht]
    exact hmove ▸ hcompl
  have hroot : ∀x∈RootGroup F4 standardPoint.val,
      LinearMap.range (τ x-1)≤c.imageSpace W ∧ ∀v∈c.imageSpace W,τ x v=v := by
    intro x hx
    rw [←hm] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    obtain ⟨u,hu,rfl⟩ := hy
    have hh := upper_root_bounds d h e g hK a hi (σ.comp f) c u hu
    simpa only [τ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,m.symm_apply_apply] using hh
  have hN : ∀x∈normalizer (RootGroup F4 standardPoint.val:Set SL(2,F4)),
      (c.imageSpace W).map (τ x)=c.imageSpace W := by
    intro x hx
    rw [←hm,←map_normalizer_eq_of_bijective _ m.bijective] at hx
    exact upper_borel_invariant d h e hseed hn hU g hK hL a hi σ c (m.symm x)
      (mem_map_equiv.mp hx)
  obtain ⟨φ,_,_,hcriterion⟩ := exists_orbit_criterion τ standardPoint (c.imageSpace W) t
    hne hcompl' hN hroot
  obtain ⟨s,q,hq⟩ := ChapterG.Section01.SL2FourRecognition.naturalCopies hcriterion
  refine ⟨m,s,q,?_⟩
  intro x v j
  simpa only [τ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,m.symm_apply_apply] using hq (m x) v j

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperNatural
end
