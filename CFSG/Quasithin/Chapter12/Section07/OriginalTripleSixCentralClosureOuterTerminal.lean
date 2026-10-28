module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterBlock
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAffineModel

/-!
# The original outer central-closure local conclusion

The actual source proves the exceptional block, every core and centralizer
identity, and the full marked affine normalizer. The statement keeps its
entire original module and scalar kernels, including the actual scalar cubic
complement. This completes the local conclusion12.7.20 in the outer branch;
the later central-closure group recognition is separate.

Source: Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original outer central-closure branch supplies the exceptional block
and its whole marked local structure from the genuine original inputs. -/
theorem original_tripleSix_central_closure_outer_terminal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let M := normalizer (K : Set G)
    let X := tripleSixScalarResidual K
    ChapterC.IsExceptionalAhat6Block K ∧ (ChapterC.blockU K).map K.subtype = U ∧
      K.pCoreIn 2 = U ∧ (K ⊔ (T : Subgroup G)).pCoreIn 2 = U ∧ M.pCoreIn 2 = U ∧
      normalizer (U : Set G) = M ∧ centralizer (U : Set G) = U ∧
      M = K ⊔ (T : Subgroup G) ∧ Nat.card T = 1024 ∧ Nat.card M = 138240 ∧
      ∃ Y : Subgroup M, Nat.card Y = 3 ∧ Y.map M.subtype ≤ X ∧
        ∃ E : M ≃* Multiplicative hexacode ⋊[hexAffineAction] HexAutomorphisms,
          (∀ u : U, E (inclusion (D.le_component.trans K.le_normalizer) u) =
            SemidirectProduct.inl (tripleSixPointCoordinates D a u)) ∧
          (∀ k : K, (E (inclusion K.le_normalizer k)).right =
            (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
          (normalizer (Y : Set M)).map E.toMonoidHom =
            (SemidirectProduct.inr : HexAutomorphisms →*
              Multiplicative hexacode ⋊[hexAffineAction] HexAutomorphisms).range ∧
          (let f := SemidirectProduct.rightHom.comp E.toMonoidHom
           f.ker = pCore 2 M ∧ f.ker = U.subgroupOf M ∧
             (hexCoordinateSixHom.comp f).ker = X.subgroupOf M) := by
  obtain ⟨hblock,hU⟩ := original_tripleSix_central_closure_outer_exceptional_block
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  obtain ⟨hK,hQ,hM,hN,hC,hjoin⟩ := original_tripleSix_central_closure_core_recovery
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  exact ⟨hblock,hU,hK,hQ,hM,hN,hC,hjoin,
    original_tripleSix_central_closure_affine_model
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter⟩

end CFSG.Quasithin.Chapter12.Section07
