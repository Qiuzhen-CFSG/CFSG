module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.LocalNormalCore

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.NormalizedCore
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.MathieuTwentyFourStabilizer

/-!
# Inner action on normalized local A₈ sections of J₄

The join of the local section with a full normalizing Sylow subgroup has
nontrivial two-core. Its central closure either has order at most eight,
which forces the perfect section to centralize the Sylow center, or places
the join inside an actual Mathieu overgroup. The former case contradicts
the involution-centralizer exclusion. In the latter, uniqueness makes this
Mathieu overgroup invariant under every automorphism preserving the section.
The proved Mathieu action theorem then lifts inner action to the original
section, with the same intrinsic two-core quotient.

The full Sylow normalization is retained because it is supplied by the
original fixed-line component argument; no general maximal-overgroup
classification is assumed.

Source: Aschbacher–Smith15.3.32(3), printed p.1133, and A.3.12(17).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open Janko4
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem center_le_closure_image
    (S : Sylow 2 Model) (M : Subgroup Model) (hSM : S.toSubgroup ≤ M) :
    (center S).map S.toSubgroup.subtype ≤ (centralClosure S M hSM).map M.subtype := by
  rintro _ ⟨s, hs, rfl⟩
  let t : S.subtype hSM := ⟨⟨s, hSM s.property⟩, s.property⟩
  have ht : t ∈ center (S.subtype hSM) := by
    apply mem_center_iff.mpr
    intro u
    apply Subtype.ext
    apply Subtype.ext
    change (u : M).val * (s : Model) = (s : Model) * (u : M).val
    exact congrArg (fun z : S => (z : Model)) ((mem_center_iff.mp hs) ⟨(u : M), u.property⟩)
  have hm : (t : M) ∈ centralClosure S M hSM :=
    le_normalClosure (mem_map_of_mem (S.subtype hSM).toSubgroup.subtype ht)
  exact mem_map_of_mem M.subtype hm

private theorem centralizes_image_of_trivial_action
    {A M : Subgroup Model} (hAM : A ≤ M) (E : Subgroup M) [E.Normal]
    (hact : (MulAut.conjNormal : M →* MulAut E).comp (inclusion hAM) = 1) :
    A ≤ centralizer (E.map M.subtype : Set Model) := by
  intro a ha
  rintro x ⟨m, hm, rfl⟩
  have hf : ((MulAut.conjNormal : M →* MulAut E).comp (inclusion hAM)) ⟨a, ha⟩ = 1 :=
    congrArg (fun f : A →* MulAut E => f ⟨a, ha⟩) hact
  have he := congrArg (fun φ : MulAut E => (((φ ⟨m, hm⟩ : E) : M) : Model)) hf
  change a * (m : Model) * a⁻¹ = (m : Model) at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm


private theorem candidate_of_join_core_of_small_action
    (A : Subgroup Model) (S : Sylow 2 Model)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hcore : pCore 2 ↥(A ⊔ S.toSubgroup) ≠ ⊥)
    (hnotcenter : ¬ (center S).map S.toSubgroup.subtype ≤ centralizer (A : Set Model))
    (hsmall : ∀ (E : Subgroup ↥(A ⊔ S.toSubgroup)) [E.Normal]
      [IsElementaryAbelian 2 E], Nat.card E ≤ 8 →
      (MulAut.conjNormal : ↥(A ⊔ S.toSubgroup) →* MulAut E).comp
        (inclusion (show A ≤ A ⊔ S.toSubgroup from le_sup_left)) = 1) :
    (candidates A).Nonempty := by
  let M : Subgroup Model := A ⊔ S.toSubgroup
  have hSM : S.toSubgroup ≤ M := le_sup_right
  rcases local_overgroup_of_twoCore_ne_bot S M hSM hcore with hs | hM
  · let E := centralClosure S M hSM
    let := centralClosure_elementary_of_twoCore_ne_bot S M hSM hcore
    have hact := hsmall E hs
    have hcent := centralizes_image_of_trivial_action
      (show A ≤ M from le_sup_left) E hact
    exact (hnotcenter ((center_le_closure_image S M hSM).trans
      (le_centralizer_iff.mp hcent))).elim
  · obtain ⟨H, hMH, ⟨eH⟩⟩ := hM
    exact ⟨H, mem_candidates_of_sylow_le S hlocal
      (le_sup_left.trans hMH) (le_sup_right.trans hMH) eH⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
open Max1Placement
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- A normalized local binary-four section lies in an actual Mathieu candidate. -/
theorem candidate_of_normalized_local
    (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hn : S.toSubgroup ≤ normalizer (A : Set Janko4.Model)) :
    (candidates A).Nonempty := by
  apply SylowCover.candidate_of_join_core_of_small_action A S hlocal
    (normalized_join_twoCore_ne_bot A S hA hlocal hn)
    (not_center_sylow_le_centralizer A S hA hlocal)
  intro E _ _ hE
  exact local_small_elementary_action_eq_one A S hA hlocal hE _

private theorem concrete_inner_of_normalized_local
    (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hn : S.toSubgroup ≤ normalizer (A : Set Janko4.Model)) :
    TwoStabilizerActsInner A := by
  obtain ⟨H, hH⟩ := candidate_of_normalized_local A S hA hlocal hn
  intro α htwo hfix
  let D := placementOfFixedCandidate hH (candidate_invariant A S hA hlocal hH α hfix)
  exact isInnerOnTwoQuotient_of_mathieuOvergroup
    (fun B _ _ hext _ => MathieuTwentyFourStabilizer.twoStabilizerActsInner (MulEquiv.refl _) B hext)
    hA α htwo hfix (D.toInvariantMathieuOvergroup mathieuLocalFourExtension hA)

/-- On a source-local binary-four section normalized by the full ambient Sylow,
every two-power automorphism preserving the section acts inner on its quotient. -/
theorem twoStabilizerActsInner_of_normalized_local
    {Q : Type*} [Group Q] [Finite Q] (e : Q ≃* Janko4.Model)
    (A : Subgroup Q) (S : Sylow 2 Q)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hn : S.toSubgroup ≤ normalizer (A : Set Q)) :
    TwoStabilizerActsInner A := by
  apply TwoStabilizerActsInner.of_map e
  have hA' : ClassicalGroup.IsPSL (XiQuotient (A.map e.toMonoidHom)) 4 2 := by
    let f := e.subgroupMap A
    exact hA.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hlocal' : A.map e.toMonoidHom ∈ ChapterA.Section03.localCComponents T := by
    let : Group.IsSolvable e.toMonoidHom.ker := by
      rw [e.toMonoidHom.ker_eq_bot e.injective]
      infer_instance
    exact Section02.localCComponents_map_of_solvable_ker hlocal e.toMonoidHom
  exact concrete_inner_of_normalized_local _ T hA' hlocal'
    ((map_mono hn).trans (le_normalizer_map e.toMonoidHom))

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
