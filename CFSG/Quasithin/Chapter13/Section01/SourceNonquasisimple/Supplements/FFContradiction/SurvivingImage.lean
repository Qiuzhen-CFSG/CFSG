module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.OddExclusion
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The surviving simple hat image and zero rank loss

After the odd-prime exclusion the original quotient Y/O₂(Y) is A₅, L₃(2),
or cyclic of order three. Each is simple. Since K = Y and O₂(Y) centralizes
the actual omega closure, its hat action factors through that quotient.
The nontrivial image makes the factor map an isomorphism. This identifies
the actual K-image, rather than attaching an unrelated simple-group model.

Its simplicity and the already proved faithful radical action give zero
rank loss on the constructed common chief section. The candidate theorem
retains the original quotient models, full commutator identity, Thompson
actor and B.2.4 bound. The controlled-index factorization, tensor identification
and final generation contradiction remain with qt-d-1319-ff-contradiction.
Earlier canonical-star and source premises remain with qt-d-1317-supplements
and qt-d-1317-source in their final assembly.

Source: Aschbacher--Smith, proof of 13.1.9, printed pp.870--871, through (*).
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open Representation Representation.BinaryOffender
open CFSG.Quasithin ChapterB
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

private theorem small_quotient_simple {Q : Type*} [Group Q]
    (h : Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL Q 3 2 ∨ Nonempty (Q ≃* Multiplicative (ZMod 3))) :
    IsSimpleGroup Q := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · rcases h with h | h
    · obtain ⟨F,hF,hfin,_,⟨e⟩⟩ := h
      let := hF
      let := hfin
      let := Atlas.psl_simple_high_rank (F := F) 3 (by decide)
      exact e.isSimpleGroup
    · obtain ⟨e⟩ := h
      have hc : Nat.card Q = 3 := (Nat.card_congr e.toEquiv).trans (by simp)
      exact isSimpleGroup_of_prime_card hc

/-- In a surviving branch, the literal centralizer quotient has exactly the
original simple two-core quotient of Y as its K-image. -/
theorem common_hat_commutator_equiv_quotient (h : Hypothesis1311 T)
    {L H C Y : Subgroup G} (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement (T : Subgroup G) L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer (T : Subgroup G) L) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (XiQuotient Y)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (he : thompsonCommutator (T : Subgroup G) L Y j = Y) :
    Nonempty (XiQuotient Y ≃*
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) := by
  let F := commonGroup (T : Subgroup G) L Y j
  have hYF : Y ≤ F := he ▸ (show thompsonCommutator (T : Subgroup G) L Y j ≤ F from
    le_sup_left.trans le_sup_right)
  let e := (subgroupOfEquivOfLe hYF).symm
  let f := ((hatMap (T : Subgroup G) L Y j).subgroupMap (Y.subgroupOf F)).comp e.toMonoidHom
  have hf : Function.Surjective f :=
    ((hatMap (T : Subgroup G) L Y j).subgroupMap_surjective (Y.subgroupOf F)).comp e.surjective
  have hc := escaping_core_centralizes_omegaClosure h w hH hTH hAH hTL hcore j
  have hk : pCore 2 Y ≤ f.ker := by
    intro y hy
    apply Subtype.ext
    change hatMap (T : Subgroup G) L Y j ⟨y.val,hYF y.property⟩ = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    intro x hx
    exact Subtype.ext (hc (mem_map_of_mem Y.subtype hy) x hx)
  let q := QuotientGroup.lift (pCore 2 Y) f hk
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective (pCore 2 Y) f hf hk
  have hn : hatImage (T : Subgroup G) L Y j Y ≠ ⊥ := by
    simpa only [he] using ha.commutator_nontrivial
  let : Nontrivial ((Y.subgroupOf F).map (hatMap (T : Subgroup G) L Y j)) :=
    (nontrivial_iff_ne_bot _).mpr hn
  rw [he]
  exact ⟨MulEquiv.ofBijective q ⟨q.injective_of_surjective_of_simple hq,hq⟩⟩

/-- The original outside candidate has a simple K-image, its actual quotient
identification, and a common chief section with zero rank loss. -/
theorem candidate_common_chief_simple (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    {j : ℕ} (hj : j ≤ 1)
    (hN : normalizer (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j : Set G) ≤
      normalizer (L : Set G)) :
    ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ∃ n : (commonModule (T : Subgroup G) L Y j).Normal,
        let := n
        ∃ e : IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j),
          let := e
          CommonActionProperties (T : Subgroup G) L Y j ∧
          thompsonCommutator (T : Subgroup G) L Y j = Y ∧
          thompsonCommutator (T : Subgroup G) L Y j =
            ⁅thompsonCommutator (T : Subgroup G) L Y j,
              thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j⁆ ∧
          (Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
            ClassicalGroup.IsPSL (XiQuotient Y) 3 2 ∨
            Nonempty (XiQuotient Y ≃* Multiplicative (ZMod 3))) ∧
          Nonempty (XiQuotient Y ≃*
            hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) ∧
          IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) ∧
          ∃ A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j,
            hatImage (T : Subgroup G) L Y j A ≠ ⊥ ∧ HatActorBound (T : Subgroup G) L Y A j ∧
            ∃ c : CommonHatChief (T : Subgroup G) L Y A j, c.movedSection.rankLoss = 0 := by
  obtain ⟨Y,w,n,e,ha,hKY,hgen,hmodel,A,hA,hAn,hAb,⟨c⟩⟩ :=
    candidate_common_chief_nonodd h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN
  let := n
  let := e
  let := small_quotient_simple hmodel
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hcore := (canonical_frattini_geometry h hmany hL hn).2.1
  obtain ⟨eqv⟩ := common_hat_commutator_equiv_quotient h w hH hTH (hAC.trans hC.1)
    hTL hcore ha hKY
  let hsimple := eqv.symm.isSimpleGroup
  exact ⟨Y,w,n,e,ha,hKY,hgen,hmodel,⟨eqv⟩,hsimple,A,hA,hAn,hAb,c,
    common_chief_section_epsilon w hTH (hAC.trans hC.1) hTL ha hA c⟩
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
