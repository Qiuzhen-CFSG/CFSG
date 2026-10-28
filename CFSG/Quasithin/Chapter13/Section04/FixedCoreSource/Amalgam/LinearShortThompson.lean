module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixThompsonImage
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearBlockSource

/-!
# The original linear short branch without a supplied maximum family

If J₁(T) stays in the actual second-parabolic core, the simultaneous
six-letter marking makes every maximum elementary image on LT have order
at most two. Cardinal replacement then gives A(O₂(LT)) ⊆ A(T), transported
through the literal LT subtype. The five-dimensional marking supplies the
rank bound, and the action retains its entire centralizer kernel.

Applying the proved short-block exclusion to this derived family forces
[O²(B),J₁(T)]=O²(B). This supplies the residual premise of the full linear
overgroup conclusion and excludes J₁-normality in the same original join.
The literal second-residual equality K₂=L₂ is preserved. Shortness and the
simultaneous Sylow/second-radical marking are explicit here; this does not
construct the source trichotomy, select the linear model, or prove either
universal 13.4.7 interface.
Source: Aschbacher–Smith 13.2.2(10), p.878, and 13.4.7(4), pp.902–903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V B : Subgroup G}

/-- The original LT core has the full maximum family when J₁ stays in
an actually marked second-parabolic radical. -/
theorem original_core_maximum_family_of_thompson_one_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hk : q.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    (hker : q.ker = centralizer (V.subgroupOf (L ⊔ (T : Subgroup G)) :
      Set (L ⊔ (T : Subgroup G) : Subgroup G)))
    (hY : alternatingGroup (Fin 6) ≤ q.range)
    (hT : ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map q =
      ChapterB.Offenders.Six.sylowCarrier ⊓ q.range)
    (hB : ((B.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map q ≤
      ChapterB.Offenders.D 6)
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2) :
    elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊆
      elementaryAbelianMaxSubgroups (T : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  let S : Sylow 2 H := T.subtype le_sup_right
  let U := V.subgroupOf H
  have hVH : V ≤ H := D.le_sylow.trans le_sup_right
  have hHV : H ≤ normalizer (V : Set G) :=
    sup_le D.normalizes (((structural G T L h).2.2 V D).1)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hHV
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVH
  have hUS : U ≤ (S : Subgroup H) := comap_mono D.le_sylow
  have hu : Nat.card U = 32 := (Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv).trans m.card_module
  have hr : 1 < ChapterB.twoRank (S : Subgroup H) := by
    have hb := elementary_card_le_maxOrder (S : Subgroup H) U hUS inferInstance
    rw [hu,ChapterB.maxOrder_eq_two_pow_rank] at hb
    by_contra! hn
    have hh : 2 ^ ChapterB.twoRank (S : Subgroup H) ≤ 2 ^ 1 :=
      Nat.pow_le_pow_right (by decide) hn
    omega
  have hjmap : (ChapterB.thompsonJ (S : Subgroup H) 1).map H.subtype =
      ChapterB.thompsonJ (T : Subgroup G) 1 := by
    rw [←ChapterB.thompsonJ_map_injective H.subtype H.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
  have hj : (ChapterB.thompsonJ (S : Subgroup H) 1).map q ≤ ChapterB.Offenders.D 6 := by
    apply (map_mono (show ChapterB.thompsonJ (S : Subgroup H) 1 ≤
        (B.pCoreIn 2).subgroupOf H from ?_)).trans hB
    intro x hx
    exact hJ (hjmap ▸ mem_map_of_mem H.subtype hx)
  obtain ⟨E,hE⟩ := elementaryAbelianMaxSubgroups_nonempty (S : Subgroup H)
  have hc := ChapterB.maximum_image_le_two_of_thompson_one_image_le_D S q hr hY hT hj E hE
  have hf := max_family_centralizer_of_small_image (S : Subgroup H) U E hUS hE q hker hc
  have hcore : (S : Subgroup H) ⊓ centralizer (U : Set H) = pCore 2 H := by
    rw [←hker,hk,inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal S)]
  rw [hcore] at hf
  intro A hA
  let A0 := A.subgroupOf H
  have haH : A ≤ H := hA.1.trans (H.pCoreIn_le 2)
  have ha : A0.map H.subtype = A := map_subgroupOf_eq_of_le haH
  have hA0 : A0 ∈ elementaryAbelianMaxSubgroups (pCore 2 H) := by
    rw [←ChapterB.thompsonFamily_zero]
    apply (ChapterB.thompsonFamily_map_iff_of_injective H.subtype H.subtype_injective
      (pCore 2 H) A0 0).mp
    rw [ChapterB.thompsonFamily_zero,ha]
    exact hA
  have hAS := hf hA0
  have hh := (ChapterB.thompsonFamily_map_iff_of_injective H.subtype H.subtype_injective
    (S : Subgroup H) A0 0).mpr (by rwa [ChapterB.thompsonFamily_zero])
  have hsmap : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)
  simpa only [ChapterB.thompsonFamily_zero,ha,hsmap] using hh

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres eK

/-- In the original short branch, the genuine action marking suffices for
residual movement and the full linear conclusion. The source maximum-family
premise is proved by the half-order conjugation argument. -/
theorem original_pair_linear_short_conclusion_of_marked_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hb : ChapterC.IsShort L)
    (J : Subgroup G) (hJL : J ≤ L)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      Theory.SpecificGroups.SymmetricSix.synthemeStabilizer ⊓ alternatingGroup (Fin 6))
    (hK₂ : (pResidual 2 B).map B.subtype = (pResidual 2 J).map J.subtype)
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hk : q.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    (hker : q.ker = centralizer (V.subgroupOf (L ⊔ (T : Subgroup G)) :
      Set (L ⊔ (T : Subgroup G) : Subgroup G)))
    (hY : alternatingGroup (Fin 6) ≤ q.range)
    (hT : ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map q =
      ChapterB.Offenders.Six.sylowCarrier ⊓ q.range)
    (hB : ((B.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map q ≤
      ChapterB.Offenders.D 6)
    : ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
        (pResidual 2 B).map B.subtype ∧
      Solvable.LinearAmalgamConclusion T (A ⊔ B) ∧
      ¬ A ⊔ B ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
  have hc : ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
      (pResidual 2 B).map B.subtype := by
    apply (original_residual_thompson_one_iff hTB eB).mpr
    intro hn
    have hf := original_core_maximum_family_of_thompson_one_bound
      h structural D m q hk hker hY hT hB hn
    exact original_pair_linear_short_block_impossible h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
      hb hf J hJL hTJ himage hK₂
  exact ⟨hc,original_pair_linear_amalgam_conclusion h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL hc,
    not_thompson_one_normalizer_of_residual_movement hTB eB le_sup_right hc⟩
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
