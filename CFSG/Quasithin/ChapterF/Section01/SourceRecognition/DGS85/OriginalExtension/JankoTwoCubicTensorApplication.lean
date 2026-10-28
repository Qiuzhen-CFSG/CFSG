module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoCartanActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoTensorApplication

/-!
# Cubic-normalizer splitting in the literal tensor pair

A genuinely recognized reduced J₂ pair in the mixed cubic-factor setup gives
an actual S₃ × S₃ complement to O₂(AT). The exact cubic and involution
relations also transport to AT, retaining the inclusion of the reduced
endpoint and the actual O₂(BT) reduction. Both actors fix every central
element of the original O₂(AT). An actual reduced Cartan complement and
its inverting outer involution are also placed in the literal whole BT.

The reduced parabolic comparison remains explicit. These results supply
local splitting and generator relations in the original endpoints; full
Aut(J₂) parabolic recognition still requires the remaining endpoint-generator
relations, compatible model maps, and the order-12 product.
Source: Aschbacher–Smith 9.3.1, pp.732–733, via F.1.11–12;
DGS (15.3), printed pp.229–231.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The same original AT has an actual complement to its unchanged two-core. -/
theorem mixed_cubic_factor_core_complement_of_reduced_j2
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
    ∃ N : Subgroup (A ⊔ (T : Subgroup G) : Subgroup G),
      IsComplement' N (pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G)) ∧
      Nonempty (N ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨hf,_,_,_,_,_,hq⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hh : ∃ N : Subgroup (parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) 1),
      IsComplement' N (pCore 2 (parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) 1)) ∧
      Nonempty (N ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
    ⟨JankoTwo.originalCubicNormalizer hf 1 e.right,
      JankoTwo.originalCubicNormalizer_complement hf 0 1 e.left e.right hne,
      JankoTwo.originalCubicNormalizer_equiv hf 0 1 e.left e.right hne⟩
  rwa [hq] at hh

/-- Exact element relations on AT, with the actual reduced endpoint retained.
Every element of the center of O₂(AT) is fixed by both chosen actors. -/
theorem mixed_cubic_factor_outer_relations_of_reduced_j2
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
    ∃ d k x : (A ⊔ (T : Subgroup G) : Subgroup G),
      orderOf d=3 ∧ orderOf k=3 ∧
      (k : G) ∈ parabolic ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 1 ∧
      x^2=1 ∧ (x : G) ∉ parabolic ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 1 ∧
      d*k=k*d ∧ d*x=x*d ∧ x*k*x⁻¹=k⁻¹ ∧
      ∀ z ∈ (center (pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G))).map
        (pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G)).subtype,
        x*z=z*x ∧ k*z=z*k := by
  obtain ⟨hf,_,_,_,hb,_,hq⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨k,x,hk,hkR,hx,hxR,hdk,hdx,hxk,hfix⟩ :=
    JankoTwo.exists_original_outer_cubic_relations_fixing_core_center hf 0 1 e.left e.right hne
  have hh : ∃ d k x : parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) 1,
      orderOf d=3 ∧ orderOf k=3 ∧
      (k : G) ∈ parabolic ![(pResidual 2 H).map H.subtype,U]
        (SuzukiContainment.reducedSylow ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) 1 ∧
      x^2=1 ∧ (x : G) ∉ parabolic ![(pResidual 2 H).map H.subtype,U]
        (SuzukiContainment.reducedSylow ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) 1 ∧
      d*k=k*d ∧ d*x=x*d ∧ x*k*x⁻¹=k⁻¹ ∧
      ∀ z ∈ (center (pCore 2 (parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) 1))).map
        (pCore 2 (parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) 1)).subtype,
        x*z=z*x ∧ k*z=z*k :=
    ⟨JankoTwo.originalCubic hf 1 e.right,k,x,JankoTwo.originalCubic_order hf 1 e.right,
      hk,hkR,hx,hxR,hdk,hdx,hxk,hfix⟩
  rw [←hq]
  simpa only [SuzukiContainment.reducedSylow,hb] using hh

private theorem transport_borel_actors
    {Y : Type*} [Group Y] (P B₀ B R : Subgroup Y)
    (hcomp : ∀ k : B₀, orderOf k=3 → IsComplement' (zpowers k) (R.subgroupOf B₀))
    (hs : ∃ k x : P, orderOf k=3 ∧ (k : Y) ∈ B₀ ∧ x^2=1 ∧
      (x : Y) ∈ B ∧ (x : Y) ∉ B₀ ∧ x*k*x⁻¹=k⁻¹) :
    ∃ k : B₀, ∃ x : B, orderOf k=3 ∧ IsComplement' (zpowers k) (R.subgroupOf B₀) ∧
      x^2=1 ∧ (x : Y) ∉ B₀ ∧ (x : Y)*(k : Y)*(x : Y)⁻¹=(k : Y)⁻¹ := by
  obtain ⟨k,x,hk,hkB,hx,hxB,hxR,hxk⟩ := hs
  let kB : B₀ := ⟨k,hkB⟩
  let xB : B := ⟨x,hxB⟩
  have hk3 : orderOf kB=3 :=
    (Subgroup.orderOf_coe kB).symm.trans ((Subgroup.orderOf_coe k).trans hk)
  have hx2 : xB^2=1 := Subtype.ext (congrArg (fun z : P => (z : Y)) hx)
  exact ⟨kB,xB,hk3,hcomp kB hk3,hx2,hxR,congrArg Subtype.val hxk⟩

/-- An actual reduced Cartan complement and its inverting involution in
BT, including the whole odd Borel and the original O₂(BT) reduction. -/
theorem mixed_cubic_factor_cartan_actors_of_reduced_j2
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
    ∃ k : commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)),
      ∃ x : (B ⊔ (T : Subgroup G) : Subgroup G),
        orderOf k=3 ∧ IsComplement' (zpowers k)
          ((twoCore (B ⊔ (T : Subgroup G) : Subgroup G)).subgroupOf
            (commonBorel ![(pResidual 2 H).map H.subtype,U]
              (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)))) ∧
        x^2=1 ∧ (x : G) ∉ commonBorel ![(pResidual 2 H).map H.subtype,U]
          (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧
        (x : G)*(k : G)*(x : G)⁻¹=(k : G)⁻¹ := by
  obtain ⟨hf,_,_,_,hb,_,_⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hs : ∃ k x : parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) 1,
      orderOf k=3 ∧ (k : G) ∈ commonBorel ![(pResidual 2 H).map H.subtype,U]
        (SuzukiContainment.reducedSylow ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) ∧
      x^2=1 ∧ (x : G) ∈ commonBorel ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) ∧
      (x : G) ∉ commonBorel ![(pResidual 2 H).map H.subtype,U]
        (SuzukiContainment.reducedSylow ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) ∧
      x*k*x⁻¹=k⁻¹ := by
    obtain ⟨k,x,hk,hkB,hx,hxB,hxR,_,_,hxk,_⟩ :=
      JankoTwo.exists_original_borel_outer_cubic_relations hf 0 1 e.left e.right hne
    exact ⟨k,x,hk,hkB,hx,hxB,hxR,hxk⟩
  have hh := transport_borel_actors _ _ _ _
    (JankoTwo.reduced_borel_cubic_complement hf 0 e.left e.middle) hs
  rwa [SuzukiContainment.reducedSylow,hb] at hh

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
