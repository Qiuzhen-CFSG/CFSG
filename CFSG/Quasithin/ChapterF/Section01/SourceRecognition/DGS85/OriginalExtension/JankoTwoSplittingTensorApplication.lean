module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoSplitting
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoTensorApplication

/-!
# Simultaneous original splittings in the mixed cubic-factor pair

One involution in the full BT generates both original endpoints H and AT
above their literal reduced subgroups. Its cyclic subgroup meets all three
reduced groups trivially. Together with the actual reduced Cartan cubic,
it also generates an S₃ complement to O₂(BT). The reduction throughout is
the actual O₂(BT); no conjugate Sylow or smaller odd Borel is substituted.

The reduced J₂ comparison remains an explicit input. The source's remaining
endpoint action relations and order-twelve product are still needed for
Aut(J₂) parabolic recognition.
Source: Aschbacher–Smith 9.3.1 via F.1.11–12;
DGS, Groups and Graphs (1985), (15.3), printed pp.229–231.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The literal original tensor pair splits over its reduced pair with one
common involution, and its full BT has the constructed S₃ core complement. -/
theorem mixed_cubic_factor_simultaneous_splittings_of_reduced_j2
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv
      (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : (T : Subgroup G) ≠ SuzukiContainment.reducedSylow
      ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) :
    ∃ k x : (B ⊔ (T : Subgroup G) : Subgroup G),
      orderOf k=3 ∧ (k:G)∈commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧
      x^2=1 ∧ (x:G)∉commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧ x*k*x⁻¹=k⁻¹ ∧
      IsComplement' (zpowers k ⊔ zpowers x) (pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)) ∧
      Nonempty ((zpowers k ⊔ zpowers x : Subgroup (B ⊔ (T : Subgroup G) : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) ∧
      (commonBorel ![(pResidual 2 H).map H.subtype,U]
          (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ⊔ zpowers (x:G)=B ⊔ (T : Subgroup G) ∧
        Disjoint (commonBorel ![(pResidual 2 H).map H.subtype,U]
          (twoCore (B ⊔ (T : Subgroup G) : Subgroup G))) (zpowers (x:G))) ∧
      (parabolic ![(pResidual 2 H).map H.subtype,U]
          (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 0 ⊔ zpowers (x:G)=H ∧
        Disjoint (parabolic ![(pResidual 2 H).map H.subtype,U]
          (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 0) (zpowers (x:G))) ∧
      (parabolic ![(pResidual 2 H).map H.subtype,U]
          (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 1 ⊔ zpowers (x:G)=A ⊔ (T : Subgroup G) ∧
        Disjoint (parabolic ![(pResidual 2 H).map H.subtype,U]
          (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 1) (zpowers (x:G))) := by
  obtain ⟨hf,_,_,_,hb,hp,hq⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hh := JankoTwo.exists_original_simultaneous_generators hf 0 1 e.left e.right e.middle hne
  rw [SuzukiContainment.reducedSylow,hb] at hh
  obtain ⟨k,x,hk,hkB,hx,hxB,hinv,hC,he,hB,hP⟩ := hh
  refine ⟨k,x,hk,hkB,hx,hxB,hinv,hC,he,hB,?_,?_⟩
  · simpa only [hp] using hP 0
  · simpa only [hq] using hP 1

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
