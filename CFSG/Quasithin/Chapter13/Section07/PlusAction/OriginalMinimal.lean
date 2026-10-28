module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalMixedGeometry
public import Theory.GroupTheory.ReducedNormal.MinimalMoved
public import Theory.GroupTheory.CentralPChiefFactors.Coprime

/-!
# The original minimal mixed module

The actual cubic normal kernel actor has a nonzero mixed displacement in the
fixed layer. Restricting to its join with the point residual and T preserves
normality and elementary abelianness. Its cubic quotient has central two-chief
factors, and its two-core fixes this displacement. The minimal reduced subgroup
lemma therefore gives an actual minimal normal module fully moved by the actor.

Source: Aschbacher--Smith 13.7.4(1), printed p.937, using A.4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_primitive_cubic_minimal_mixed_module
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hp : IsPPerfect 2 (J.map H.subtype)) (hout : ¬ J.map H.subtype ≤ M)
    (hcard : Nat.card (J ⧸ pCore 2 J) = 3) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let K := J.map H.subtype
    let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
    let U₂ := ⁅⁅fixedLayer F,F.L₁⁆,K⁆
    ∃ U : Subgroup X, U ≤ U₂.subgroupOf X ∧ IsPReduced 2 U ∧ U ≠ ⊥ ∧
      ⁅U,K.subgroupOf X⁆ = U ∧
      ∀ A : Subgroup X, A ≤ U → A.Normal → ⁅A,K.subgroupOf X⁆ ≠ ⊥ → A = U := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
  let U₂ := ⁅⁅fixedLayer F,F.L₁⁆,K⁆
  let KX := K.subgroupOf X
  have hKX : K ≤ X := le_sup_left
  have hXH : X ≤ H := sup_le (hJC.trans (kernel_le_H (D := F))) h.local_le
  let : KX.Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hJn)
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hJn
  obtain ⟨hU₂U,hU₂X,hLn,hUn,hE,hUne,hgen⟩ :=
    source_primitive_cubic_mixed_module d h1221 h hU eL hm J hJC hJn hp hout hcard
  let := hUn
  let := hE
  let eK : KX ≃* K := subgroupOfEquivOfLe hKX
  let eJ : J ≃* K := J.equivMapOfInjective H.subtype H.subtype_injective
  let e : KX ≃* J := eK.trans eJ.symm
  have hpX : IsPPerfect 2 KX := hp.of_surjective eK.symm.toMonoidHom eK.symm.surjective
  have hcardX : Nat.card (KX ⧸ pCore 2 KX) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact hcard
  have hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 KX) :=
    (hasCentralPChiefFactorsAbove_iff_quotient _).mpr
      (HasCentralPChiefFactors.of_isPGroup_of_ne (by decide : 2 ≠ 3)
        (IsPGroup.of_card (n := 1) (by rw [hcardX,pow_one])))
  have hKne : K ≠ ⊥ := by
    intro he
    apply hout
    change K ≤ M
    rw [he]
    exact bot_le
  have hkillK : K.pCoreIn 2 ≤ centralizer (fixedLayer F : Set G) :=
    (subnormal_kernel_structure h hJC (inferInstance : (K.subgroupOf H).Normal).isSubnormal
      hp hKne).2.2.2.2
  have hcoremap : (KX.pCoreIn 2).map X.subtype = K.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup X.subtype
      (by rw [X.ker_subtype]; exact IsPGroup.of_bot),
      map_subgroupOf_eq_of_le hKX]
  have hkillX : KX.pCoreIn 2 ≤ centralizer (U₂.subgroupOf X : Set X) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro u hu
    apply Subtype.ext
    have hxK : (x : G) ∈ K.pCoreIn 2 := hcoremap ▸ mem_map_of_mem X.subtype hx
    exact (mem_centralizer_iff.mp (hkillK hxK)) u.val (hU₂U hu)
  have hmove : ⁅U₂.subgroupOf X,KX⁆ ≠ ⊥ := by rwa [hgen]
  exact exists_minimal_isPReduced_le_of_normal_moved KX (U₂.subgroupOf X) hpX hchief hkillX hmove

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
