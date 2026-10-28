module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalOrdinaryComponent
public import Theory.GroupTheory.CComponent.CharacteristicTwo

/-!
# The actual ordinary overcomponent has a nontrivial core obstruction

The original singular centralizer has characteristic two by the original
full Sylow and even-characteristic hypotheses. Its actual C-component
cannot itself be quasisimple, while the preceding native residual argument
proves its intrinsic two-core quotient is quasisimple. The selected group
and its movement are retained in one original-source conclusion.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original contrary HS branch supplies a nonquasisimple normal
C-component whose unchanged intrinsic two-core quotient is quasisimple. -/
theorem SourceHypothesis.exists_original_hs_nonquasisimple_overcomponent
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ z : V, z ≠ 1 ∧ ¬ D.Nonsingular z ∧
      (T : Subgroup G) ≤ Gv (z : G) ∧ ¬ Gv (z : G) ≤ M L ∧
      Gv (z : G) ∈ (D.fullSetup hZ T z).Hz ∧
      ∃ K : Subgroup G, K ≤ Gv (z : G) ∧
        (K.subgroupOf (Gv (z : G))).IsCComponent ∧
        Gv (z : G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (K ⧸ pCore 2 K) ∧ ¬ IsQuasisimple K ∧
        ¬ ⁅V,K⁆ ≤ (Gv (z : G)).pCoreIn 2 := by
  obtain ⟨hZ,u,w,_,_,_,P,t,_,_,_,hz,hsz,hTz,_,hout,hHz,
    _,_,_,_,_,K,hKG,hK,hordinary,_,hKN,_,_,hmove⟩ :=
    H.exists_original_hs_ordinary_normal_overcomponent D hTV hTI v hv he
  let z := u*w
  have hHz' : Gv (z : G) ∈ (D.fullSetup hZ T z).Hz := by
    rwa [(D.fullSetup hZ T z).Gz_eq] at hHz
  refine ⟨hZ,z,hz,hsz,hTz,hout,hHz',K,hKG,hK,hKN,hordinary,?_,hmove⟩
  intro hquasi
  have hchar := H.point_local_characteristic D hZ z hHz'
  have hself : centralizer (pCore 2 (Gv (z : G)) : Set (Gv (z : G))) ≤
      pCore 2 (Gv (z : G)) := by
    rw [←hchar]
    exact centralizer_generalizedFitting_le _
  exact hK.not_isQuasisimple_of_characteristic_two hself
    (hquasi.of_mulEquiv (subgroupOfEquivOfLe hKG).symm)

end CFSG.Quasithin.Chapter12.Section06
