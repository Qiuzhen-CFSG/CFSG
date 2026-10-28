module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoQuaternionAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoTensorApplication

/-!
# The outer quaternion relation in the literal mixed tensor pair

The same involution in the full BT complements both reduced endpoints H₀
and (AT)₀ and the whole reduced Borel. The original H-core supplies an
order-four q in its actual commutator subgroup with the chosen cubic k,
and xq has order eight. All reductions use the literal O₂(BT).

This discharges the quaternion-word relation of DGS (15.3), p.230, in the
original F.1.11–12 tensor application. Reduced J₂ recognition remains
explicit. The separate order-twelve relation and Aut(J₂) parabolic
identification are not asserted.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The common original outer involution has the source order-eight
product with an element of the literal H-core commutator factor. -/
theorem mixed_cubic_factor_quaternion_generators_of_reduced_j2
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
    ∃ k x : (B ⊔ (T : Subgroup G) : Subgroup G), ∃ q : G,
      orderOf k=3 ∧ (k:G)∈commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧
      x^2=1 ∧ (x:G)∉commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧ x*k*x⁻¹=k⁻¹ ∧
      q∈⁅twoCore H,zpowers (k:G)⁆ ∧ orderOf q=4 ∧ orderOf ((x:G)*q)=8 ∧
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
  obtain ⟨hf,_,_,_,hb,hp,hAT⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hh := JankoTwo.exists_original_quaternion_generators hf 0 1 e.left e.right e.middle hne
  rw [SuzukiContainment.reducedSylow,hb,hp] at hh
  obtain ⟨k,x,q,hk,hkB,hx,hxB,hinv,hq,hqo,hxq,hB,hP⟩ := hh
  refine ⟨k,x,q,hk,hkB,hx,hxB,hinv,hq,hqo,hxq,hB,?_,?_⟩
  · simpa only [hp] using hP 0
  · simpa only [hAT] using hP 1

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
