module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.ResidualModuleCore
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.CoreNormalizer
public import Theory.GroupTheory.CentralizingCoverIndex

/-!
# Excluding the remaining Mathieu compared-residual branch

Retain the full original component K, its marked involution z and V. The
preceding reduction identifies V with the full order-2048 core of C_K(z).
Normalizer control for V makes the original fixed residual L_A normal in
N_K(V). The native M₂₄ quotient therefore forces L_A to equal that whole
normalizer, where the centralizer of z has index 276.

On the other hand, L = L_A O₂(L), and O₂(L) fixes V. Thus the same index
is the centralizer index in L. The original Sylow fixes z and normalizes L,
so that index is odd. This contradiction excludes the entire compared
residual branch without replacing K, V, z or any quotient map.

The literal Hall consumer retains only the M₁₂/M₂₂ pushing-up alternatives.
Consequently Hall faithfulness is proved for the M₂₃/M₂₄ central quotients;
the two small-Mathieu pushing-up cases remain needed for the full source input.

Source: Aschbacher–Smith 4.4.3 and 4.4.14, printed pp.623–625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original fixed residual and Sylow exclude the entire compared-core case. -/
theorem sourceOrbit_no_core_compared_residual
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (ho : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (hc : MathieuJankoCoreComparedResidualCase (T : Subgroup G) L V A) : False := by
  obtain ⟨K,hK,hn,hout,hVK,hFK,a,hseed,z,hzV,hz,hTz,hRM,he,hcore,hsize⟩ := hc
  let := hK.2
  let N := normalizer (A : Set G)
  let j := N.subtype.comp K.subtype
  have hj : Function.Injective j := N.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map N.subtype := by rw [MonoidHom.range_comp,range_subtype]
  let F := oddActorResidual L A
  let Fk := F.comap j
  let C := centralizer ({z} : Set K)
  let W := C.pCoreIn 2
  have hW : W.map j = V := hcore.symm
  have hFc : Fk.map j = F := map_comap_eq_self (hFK.trans_eq hjr.symm)
  obtain ⟨hcover,hmove,hVFcore,hFcore⟩ := chosen_oddActorResidual_cover h D A hAN hcomm ho hAV
  have hVF : V ≤ F := hVFcore.trans (pCoreIn_le 2 F)
  have hEF : W ≤ Fk := by
    intro x hx
    exact hVF (hW ▸ mem_map_of_mem j hx)
  have hFN : Fk ≤ normalizer (W : Set K) := by
    have hv : Fk ≤ (normalizer (V : Set G)).comap j :=
      comap_mono (((oddActorResidual_le L A).trans inf_le_left).trans D.normalizes)
    have hw : V.comap j = W := by rw [←hW,comap_map_eq_self_of_injective hj]
    exact hw ▸ hv.trans (V.le_normalizer_comap j)
  have hNV : normalizer (V : Set G) ≤ normalizer (L : Set G) := by
    rw [hV]
    exact D.sourceOrbit_normalizer_le h
  have hnF : normalizer (W : Set K) ≤ normalizer (Fk : Set K) := by
    apply le_trans _ (F.le_normalizer_comap j)
    intro x hx
    apply normalizes_oddActorResidual L A
    refine ⟨?_,(x : N).property⟩
    apply hNV
    rw [←hW]
    exact W.le_normalizer_map j (mem_map_of_mem j hx)
  have hnot : ¬ IsPGroup 2 Fk := by
    intro hp
    have hFp : IsPGroup 2 F := hFc ▸ hp.map j
    let : Group.IsNilpotent F := hFp.isNilpotent
    let : Group.IsPerfect F := oddActorResidual_isPerfect L A
    let : Nontrivial F := (nontrivial_iff_ne_bot _).mpr
      (fun hb => D.ne_bot (bot_unique (hb ▸ hVF)))
    exact Group.IsPerfect.not_isSolvable F inferInstance
  have hcard : Nat.card (pCore 2 C) = 2048 := by
    have hh := congrArg (fun U : Subgroup G => Nat.card U) hW
    rw [card_map_of_injective hj,show W = (pCore 2 C).map C.subtype from rfl,
      card_map_of_injective C.subtype_injective,hsize] at hh
    exact hh
  let e : K ≃* Janko4.Model := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq a.component_center_eq_bot.symm).trans a.quotientEquiv)
  have hindex := Janko4.InvolutionCentralizers.core_normalizer_overgroup_index_of_equiv
    e z hz hcard Fk hEF hFN hnF hnot
  have hcent : C = (centralizer ({j z} : Set G)).comap j := by
    ext x
    simp only [C,mem_centralizer_singleton_iff,mem_comap,←map_mul,hj.eq_iff]
  have hindexG : (centralizer ({j z} : Set G)).relIndex F = 276 := by
    change C.relIndex Fk = 276 at hindex
    rw [hcent,relIndex_comap,hFc] at hindex
    exact hindex
  have hQ : L.pCoreIn 2 ≤ centralizer ({j z} : Set G) := by
    have hv : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
      (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
        (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
    intro q hq
    exact mem_centralizer_singleton_iff.mpr ((hv hq) (j z) hzV).symm
  let : ((L.pCoreIn 2).subgroupOf L).Normal := by
    have he : (L.pCoreIn 2).subgroupOf L = pCore 2 L :=
      comap_map_eq_self_of_injective L.subtype_injective (pCore 2 L)
    rw [he]
    infer_instance
  have heq := centralizer_relIndex_cover L F (L.pCoreIn 2)
    ((oddActorResidual_le L A).trans inf_le_left) (pCoreIn_le 2 L) hcover (j z) hQ
  have hodd := sylow_fixed_centralizer_odd_index T L D.sylow_normalizes_component (j z) hTz
  rw [←heq,hindexG] at hodd
  exact hodd (by decide)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every nonfaithful literal Hall subgroup now forces a small-Mathieu pushing-up case. -/
theorem sourceOrbit_mathieu_hall_pushingUp_only
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
        Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
        MathieuPushingUpFactoredCase T L V A ∧ MathieuPushingUpFactorGap T L V A := by
  have hsource := @sourceOrbit_mathieu_hall_residual_core G instG finG T L V D
    h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hcases⟩ := hA
  refine ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,?_⟩
  apply hcases.resolve_right
  intro hc
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  have hsect := (le_sectionCentralizer_iff A L).mp hAL
  exact D.sourceOrbit_no_core_compared_residual h.toHypothesis1221 hV
    hsect.1 hsect.2 hodd hAV hc.2.2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open Sporadic.Mathieu
open scoped IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original Hall subgroup is faithful in the M₂₃ and M₂₄ source cases. -/
theorem sourceOrbit_inner_mathieu_hall_faithful
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer L = ⊥ := by
  by_contra hker
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hsmall,hpush⟩ :=
    @sourceOrbit_mathieu_hall_pushingUp_only G instG finG T L V D
      h hmany hV (.inr (.inr hm)) hnon H hH hlarge B hBN hHall hker
  have hs : Nat.card (D.orbitComponent ⧸ center D.orbitComponent) = 95040 ∨
      Nat.card (D.orbitComponent ⧸ center D.orbitComponent) = 443520 :=
    hsmall.imp (fun e => (Nat.card_congr e.some.toEquiv).trans m12_order)
      (fun e => (Nat.card_congr e.some.toEquiv).trans m22_order)
  have hi : Nat.card (D.orbitComponent ⧸ center D.orbitComponent) = 10200960 ∨
      Nat.card (D.orbitComponent ⧸ center D.orbitComponent) = 244823040 :=
    hm.imp (fun e => (Nat.card_congr e.some.toEquiv).trans m23_order)
      (fun e => (Nat.card_congr e.some.toEquiv).trans m24_order)
  omega
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
