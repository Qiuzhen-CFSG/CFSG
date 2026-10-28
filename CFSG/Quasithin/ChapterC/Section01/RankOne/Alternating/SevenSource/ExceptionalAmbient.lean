module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalPreimage
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalSelection
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalResidual
/-!
# C.1.24(a) from the original exceptional A₇ four-space

B.2.10 retains the original action kernel and its Sylow two-subgroup. The
actual four-space chooses an A₅ through the common Thompson and Baumann
image. Lift its perfect residual in the quasisimple quotient G/O₂(G), then
take the inverse image in G. The resulting local Sylow has the original
Baumann subgroup and a two-group action kernel. The natural A₅ source
constructs the local class, while perfectness lifts normalizer generation
through the possible central cubic kernel. C.1.21 then yields a block on L.

No selected-subgroup, local-class or shortness premise remains. The separate
B.5 classification supplies the actual four-space used here. The original
centralizing case returns a nontrivial characteristic normal subgroup.

Source: Aschbacher–Smith C.1.24(a), printed pp.130–131, with R=T.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource
variable {G : Type*} [Group G] [Finite G]
local notation "A7" => alternatingGroup (Fin 7)

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hn hp
  let := hn
  let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
  apply top_unique
  rw [←solvableResidual_eq_top (G := A)]
  exact solvableResidual_le_of_solvable_quotient N

private theorem alternating_seven_twoCore_eq_bot : pCore 2 (alternatingGroup (Fin 7)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (pCore 2 (alternatingGroup (Fin 7))) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 2 (alternatingGroup (Fin 7)) := by
      have ht : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 7))) :=
        h ▸ pCore_isPGroup
      exact ht.of_surjective
        (Subgroup.topEquiv (G := alternatingGroup (Fin 7))).toMonoidHom
        (Subgroup.topEquiv (G := alternatingGroup (Fin 7))).surjective
    obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
    have hc : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [hc] at hn
    have h3 : 3 ∣ 2 ^ n := dvd_trans (by norm_num : 3 ∣ 2520) hn
    exact False.elim (by simpa using (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h3))


/-- C.1.24(a), exceptional four-dimensional branch, on the original Sylow. -/
theorem normal_characteristic_or_block_of_exceptional_seven
    (L U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G = pCore 2 G)
    (hfL : generalizedFitting L = pCore 2 L) (T : Sylow 2 G)
    (hprod : ∀ g:G, ∃ l∈L, ∃ t∈(T : Subgroup G), l*t=g)
    (q : G →* A7) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hLq : L.map q = ⊤)
    (hd : Module.finrank (ZMod 2) (Additive U) = 4)
    (hm : ⁅U,L⁆ ≠ ⊥) :
    (∃ C : Subgroup (ChapterB.baumann (T : Subgroup G)), C.Characteristic ∧ C≠⊥ ∧
      (C.map (ChapterB.baumann (T : Subgroup G)).subtype).Normal) ∨ IsBlock L := by
  let := hL.perfect
  have hpL : IsPPerfect 2 L := perfect_twoPerfect
  have hres : pResidual 2 G = L := pResidual_eq_of_subnormal_product L (T : Subgroup G)
    hL.subnormal hpL T.isPGroup' hprod
  let : L.Normal := hres ▸ (inferInstance : (pResidual 2 G).Normal)
  have hgen : L ⊔ (T : Subgroup G) = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨l,hl,t,ht,rfl⟩ := hprod g
    exact mul_mem (mem_sup_left hl) (mem_sup_right ht)
  have hQT : pCore 2 G ≤ T := pCore_isPGroup.le_sylow_of_normal T
  have hUQ : U ≤ pCore 2 G := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  have hUT := hUQ.trans hQT
  have hdata := ChapterB.lemma_B_2_10_two U (T : Subgroup G) q hq hk T hQT le_rfl
    alternating_seven_twoCore_eq_bot L (Or.inl ⟨hL,inferInstance⟩) hm hprod
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker
  · have hn := (ChapterB.lemma_B_2_10_centralizing U (T : Subgroup G) hUT hQT
      hdata.2.1 (by simpa only [ChapterB.thompsonJ_zero,hk] using hJ)).2.2.2
    have hTne : (T : Subgroup G) ≠ ⊥ := by
      intro ht
      have hu : U=⊥ := le_bot_iff.mp (hUT.trans_eq ht)
      exact hm (by rw [hu,commutator_bot_left])
    let : Nontrivial (ChapterB.baumann (T : Subgroup G)) :=
      (nontrivial_iff_ne_bot _).mpr (SymmetricSix.baumann_ne_bot (T : Subgroup G) T.isPGroup' hTne)
    exact Or.inl ⟨⊤,inferInstance,top_ne_bot,by
      simpa only [←MonoidHom.range_eq_map,range_subtype] using hn⟩
  obtain ⟨Pker,_,hPker⟩ : ∃ P : Sylow 2 q.ker, (P : Subgroup q.ker).Normal ∧
      (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G := by
    rw [hk]
    exact hdata.1
  have hQ := Exceptional.core_le_kernel q Pker hPker
  let := Exceptional.quotient_isQuasisimple L (T : Subgroup G) q hLq T.isPGroup' hgen Pker hPker
  have hcentral := Exceptional.quotient_lift_ker_eq_center L (T : Subgroup G)
    q hq hLq T.isPGroup' hgen Pker hPker hQ
  obtain ⟨A,B,_,_,hSA,⟨eB⟩,hBN,hAB,⟨PB,hPB⟩,hNB⟩ :=
    Alternating.SevenSource.exceptional_five_quotient_seed U q hq hk hd T hUT hJ
  obtain ⟨H,hQH,hHq,hk2,P,hBaum⟩ := exceptional_five_preimage q hQ hq
    hcentral.le T A B hSA hAB eB PB hPB
  have hHgen : H ⊔ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) = ⊤ := by
    apply Exceptional.eq_top_of_full_alternating_image L (T : Subgroup G) q hq hLq
      T.isPGroup' hgen Pker hPker _ (hQH.trans le_sup_left)
    rw [Subgroup.map_sup,hHq,sup_comm]
    exact hNB
  have hYL : (pResidual 2 H).map H.subtype ≤ L :=
    (map_pResidual_le 2 H.subtype).trans_eq hres
  have hne := Alternating.SevenSource.exceptional_selected_residual_not_central
    q H L B eB hHq hL.subnormal hLq hQ hYL
  exact Alternating.SevenSource.exceptional_four_space_seed_block_alternative
    T L U H q hq hk hd B eB hBN hHq (hUQ.trans hQH) hk2 hf hQH P hBaum
    (by simpa only [←hk] using hJ) hHgen hYL hL.subnormal hpL hfL hne
end CFSG.Quasithin.ChapterC.RankOne.SevenSource
