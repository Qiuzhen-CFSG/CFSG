module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoInvertingGenerator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoTensorApplication

/-!
# Both source inverters in the literal mixed tensor pair

The original full BT contains the common outer involution x. For the same
Cartan cubic k, an involution t in the reduced H endpoint lies outside BT
and generates H together with BT. It also generates the reduced endpoint
with the full reduced Borel. The order-eight quaternion word and all
original/reduced supplements remain unchanged.

This supplies DGS (15.3), printed pp.229–230, clause (iv), to the literal
mixed cubic-factor consumer. The product xt has order six in the literal quotient H/O₂(H), after
choosing the reduced inverter. Its order-twelve lift and the Aut(J₂)
parabolic identification remain to be proved; reduced recognition stays explicit.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- Both source inverters for the same cubic, with the full BT and the
literal reduced H and AT inclusions. -/
theorem mixed_cubic_factor_inverting_generators_of_reduced_j2
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
    ∃ k x : (B ⊔ (T : Subgroup G) : Subgroup G), ∃ q t : G,
      orderOf k=3 ∧ (k:G)∈commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧
      x^2=1 ∧ (x:G)∉commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧ x*k*x⁻¹=k⁻¹ ∧
      q∈⁅twoCore H,zpowers (k:G)⁆ ∧ orderOf q=4 ∧ orderOf ((x:G)*q)=8 ∧
      t∈parabolic ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 0 ∧ t^2=1 ∧
      t∉B ⊔ (T : Subgroup G) ∧ t*(k:G)*t⁻¹=(k:G)⁻¹ ∧
      commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ⊔ zpowers t=
        parabolic ![(pResidual 2 H).map H.subtype,U]
          (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 0 ∧
      (B ⊔ (T : Subgroup G)) ⊔ zpowers t=H ∧
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
  have hh := JankoTwo.exists_original_inverting_generators hf 0 1 e.left e.right e.middle hne
  rw [SuzukiContainment.reducedSylow,hb,hp] at hh
  obtain ⟨k,x,q,t,hk,hkB,hx,hxB,hinv,hq,hqo,hxq,ht,ht2,htB,htk,htgen,htgen',hB,hP⟩ := hh
  refine ⟨k,x,q,t,hk,hkB,hx,hxB,hinv,hq,hqo,hxq,ht,ht2,htB,htk,htgen,htgen',hB,?_,?_⟩
  · simpa only [hp] using hP 0
  · simpa only [hAT] using hP 1

/-- The source product has order six in the literal quotient H/O₂(H),
with its reduced generator outside the full original BT. -/
theorem mixed_cubic_factor_inverter_product_six_of_reduced_j2
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
    ∃ k x t : H,
      orderOf k=3 ∧ (k:G)∈commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧
      x^2=1 ∧ (x:G)∈B ⊔ (T : Subgroup G) ∧
      (x:G)∉commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧ x*k*x⁻¹=k⁻¹ ∧
      (t:G)∈parabolic ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 0 ∧ t^2=1 ∧
      (t:G)∉B ⊔ (T : Subgroup G) ∧ t*k*t⁻¹=k⁻¹ ∧
      orderOf (QuotientGroup.mk' (pCore 2 H) (x*t))=6 ∧
      commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ⊔ zpowers (t:G)=
        parabolic ![(pResidual 2 H).map H.subtype,U]
          (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 0 ∧
      (B ⊔ (T : Subgroup G)) ⊔ zpowers (t:G)=H := by
  obtain ⟨hf,_,_,_,hb,hp,_⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hh := JankoTwo.exists_original_product_six_actors hf 0 1 e.left e.right e.middle hne
  rw [hp,SuzukiContainment.reducedSylow,hb] at hh
  exact hh

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
