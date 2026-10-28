module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureLocalModel
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalarComplement
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetStabilizer
import Theory.GroupTheory.SplitExtensionGivenComplement

/-!
# Marked affine coordinates for the full original central-closure normalizer

The actual cubic normalizer complement and the faithful whole local action
identify N_G(K) with the full affine hexacode group. Every original U vector,
the prescribed K-action, and the whole chosen cubic normalizer retain their
coordinates. The full U kernel and full scalar residual kernel are explicit.
The same identification determines the order of the original Sylow subgroup.

Source: Aschbacher--Smith12.7.20 and its following paragraph, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The entire original maximal local group is the full affine hexacode
model with unchanged vector and component charts and both complete kernels. -/
theorem original_tripleSix_central_closure_affine_model
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
    Nat.card T = 1024 ∧ Nat.card M = 138240 ∧
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
  obtain ⟨_,f,hf,hcore,hk,hmark,hact,_,hscalar,_⟩ :=
    original_tripleSix_central_closure_local_model
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  obtain ⟨Y,hY,hYX,hcomp⟩ := original_tripleSix_central_closure_scalar_complement
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let M := normalizer (K : Set G)
  have hUM : U ≤ M := D.le_component.trans K.le_normalizer
  let c := tripleSixPointCoordinates D a
  let v : f.ker ≃* U :=
    (MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe hUM)
  let w := v.trans c
  have hw (m : M) (u : f.ker) :
      w (MulAut.conjNormal m u) = hexAffineAction (f m) (w u) := by
    have hv : v (MulAut.conjNormal m u) = c.symm
        (Multiplicative.ofAdd (Hexacode.action (f m) (c (v u)).toAdd)) := by
      apply Subtype.ext
      exact (hact m (v u)).symm
    change c (v (MulAut.conjNormal m u)) = _
    rw [hv,c.apply_symm_apply]
    rfl
  obtain ⟨E,hEq,hEu,_,hEY⟩ := exists_marked_semidirect_equiv_of_given_complement
    f hf w hexAffineAction hw (normalizer (Y : Set M)) (hk.symm ▸ hcomp)
  have hMc : Nat.card M = 138240 := by
    rw [Nat.card_congr E.toEquiv,SemidirectProduct.card,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative hexacode ≃ hexacode),
      hexacode_card,hexAutomorphisms_card]
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hTc : Nat.card T = 1024 := by
    have hh := (T.subtype hTM).card_eq_multiplicity
    change Nat.card ((T : Subgroup G).subgroupOf M) = 2^(Nat.card M).factorization 2 at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv,hMc] at hh
    exact hh.trans (by decide +kernel)
  have hEf : SemidirectProduct.rightHom.comp E.toMonoidHom = f :=
    MonoidHom.ext hEq
  refine ⟨hTc,hMc,Y,hY,hYX,E,?_,?_,hEY,?_⟩
  · intro u
    let u' : f.ker := ⟨inclusion hUM u,hk.symm ▸ u.property⟩
    exact hEu u'
  · intro k
    exact (hEq (inclusion K.le_normalizer k)).trans (hmark k)
  · rw [hEf]
    exact ⟨hcore,hk,hscalar⟩

end CFSG.Quasithin.Chapter12.Section07
