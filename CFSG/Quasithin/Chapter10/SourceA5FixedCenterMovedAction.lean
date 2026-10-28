module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterClassifiedAction
public import Theory.Representation.CentralizerQuotientMovedCoordinates
/-!
# The original moved subgroup in the classified fixed-center action

The previously constructed G.6.4 subrepresentation is exactly the binary
submodule of the original ambient commutator [W,H]. The comparison uses the
source equality [W,H]=[W,normalClosure(g)] and the literal centralizer quotient
conjugation. Its subgroup image under the original inclusions is also [W,H].
The selected H, orbit W, quotient, actor, and all classification conclusions
are retained, with no new source assumption.

Source: Aschbacher–Smith 10.2.1 and G.6.2(1), printed pp.743 and345.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The classified action together with its exact original commutator submodule
and ambient subgroup image. -/
@[expose] def SourceFixedCenterClassifiedMovedAction
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal ∧
    H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
    (let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
     W ≤ omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) ∧
     ∃ hred : IsPReduced 2 (W.subgroupOf H),
       letI := hred.normal
       letI := hred.elementary
       let q := QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H))
       let ρ := centralizerQuotient (W.subgroupOf H)
       ∃ g : H, (g:G)∈(T : Subgroup G) ⊓ localOrbit T L ∧
         pResidual 2 (H ⧸ centralizer (W.subgroupOf H : Set H)) ≤ normalClosure ({q g} : Set _) ∧
         ∃ S : Subrepresentation ρ,
           S.toSubmodule = conjugateDisplacementSpan ρ (q g) ⊤ ∧
           S.toSubmodule = AddSubgroup.toZModSubmodule 2
             (((⁅W,H⁆ : Subgroup G).subgroupOf H).subgroupOf (W.subgroupOf H)).toAddSubgroup ∧
           S.toSubmodule.toAddSubgroup.toSubgroup'.map
             (H.subtype.comp (W.subgroupOf H).subtype) = ⁅W,H⁆ ∧
           ChapterG.Section06.Hypotheses KnownSimple.IsKnownSimple S.toRepresentation (q g) q ∧
           Module.finrank (ZMod 2) (LinearMap.range (S.toRepresentation (q g)-(LinearMap.id : S.toSubmodule →ₗ[ZMod 2] S.toSubmodule)))=1 ∧
           ChapterG.Section06.Conclusion S.toRepresentation (q g))

theorem source_exists_fixed_center_classified_moved_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourceFixedCenterClassifiedMovedAction D := by
  classical
  obtain ⟨H,hH,hHN,hWE,hred,g,hg,hresq,S,hS,hG6,hr,hclass⟩ :=
    source_exists_fixed_center_classified_action D e hn hne hout
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  have hWH : W ≤ H := fun x hx => hH.1.1.2
    (((mem_omegaOneCenterAmbient_iff _ _).mp (hWE hx)).1.1)
  let := hred.normal
  let := hred.elementary
  have hmove : ∃ x∈W, ⁅(g:G),x⁆≠1 := by
    by_contra hh
    apply hG6.nonidentity
    apply (QuotientGroup.eq_one_iff g).mpr
    intro x hx
    have he : ⁅(g:G),(x:G)⁆=1 := by
      by_contra hnx
      exact hh ⟨x,hx,hnx⟩
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  have hgen := (source_a5_moving_actor_residual_generation D e hn H hH W rfl hred g hg.1 hmove).2
  refine ⟨H,hH,hHN,hWE,hred,g,hg,hresq,S,hS,?_,?_,hG6,hr,hclass⟩
  · exact hS.trans (centralizerQuotient_conjugateDisplacementSpan_ambient hWH g hgen)
  · rw [hS]
    exact centralizerQuotient_conjugateDisplacementSpan_ambient_image hWH g hgen

end CFSG.Quasithin.Chapter10
