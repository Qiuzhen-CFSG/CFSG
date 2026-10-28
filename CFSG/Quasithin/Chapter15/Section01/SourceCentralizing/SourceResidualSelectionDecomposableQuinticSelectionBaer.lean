module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionDisplacement
public import Theory.GroupTheory.QuadraticCoreActor
public import Theory.GroupTheory.BaerSuzukiLocal

/-!
# The order-four partner branch puts E in the actual partner two-core

The partner-kernel core displaces the original Thompson fixed group E inside
U=V(Mc). Every conjugate of E by C_G(U) still centralizes this displacement.
The quadratic-core actor lemma makes every such crossed join a two-group;
relative Baer--Suzuki puts E in O₂(C_G(U))=O₂(Mc).
This containment does not assert that E is normal in Mc.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The actual order-four partner module forces the original fixed subgroup
into the original partner's two-core. -/
theorem PreparedChosenModule.decomposable_five_partner_four_fixed_le_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc)=4 →
      thompsonFixed T V≤Mc.pCoreIn 2 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let Q := C.pCoreIn 2
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨_,hcore,_,_,hself,hEC,_,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,_,_,_,hdisp⟩ := h.decomposable_five_partner_four_diagonal_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hCnorm : C≤normalizer (Q : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hEQ : E≤Q := by
    apply le_pCoreIn_of_conjugate_sup_isPGroup C E hEC
      (IsElementaryAbelian.isPGroup 2 E)
    intro g hg
    let Eg := E.map (MulAut.conj g).toMonoidHom
    let : IsElementaryAbelian 2 Eg := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
    have hEgC : Eg≤C := by
      rintro _ ⟨e,he,rfl⟩
      exact C.mul_mem (C.mul_mem hg (hEC he)) (C.inv_mem hg)
    exact Subgroup.isPGroup_sup_of_centralized_displacement Q E Eg Uc
      (isPGroup_pCoreIn 2 C) (IsElementaryAbelian.isPGroup 2 Eg)
      (hEC.trans hCnorm) (hEgC.trans hCnorm)
      ((inf_le_inf_right _ (sup_le hEC hEgC)).trans hself) hdisp hEC hEgC
  exact hEQ.trans_eq hcore

end CFSG.Quasithin.Chapter15.Section01
