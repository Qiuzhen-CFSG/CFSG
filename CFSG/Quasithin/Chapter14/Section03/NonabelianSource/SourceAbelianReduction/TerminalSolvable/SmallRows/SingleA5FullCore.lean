module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5ComponentCore
public import CFSG.Quasithin.Chapter14.Section06.SourceResidualCentralizer
public import Theory.SpecificGroups.SymmetricFive.CubicNormalizedFour
public import Theory.GroupTheory.FixedPointFreeContainment
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupAction.MaximalCosetOrbit
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.SylowClasses

/-!
# The full two-core in the original normalized degree-four A₅ branch

A cubic in the original Borel normalizes the order-four opposite-core
image. The S₅ centralizer calculation puts this image in A₅ and makes
the cubic action fixed-point-free. Lifting its commutator map proves
R≤K on the same selected component, with the actual terminal quotient.

Perfection of K makes D=C_{O₂(H)}(U) centralize K, hence R. Inside
O₂(YT), the cyclic complement of R in Y and C_T(Y)=1 then force D≤R.
The checked intersection R∩O₂(H)=W≤U eliminates D/V₁ and proves
U=O₂(H). The original point is an involution z with H=C_G(z). Its
minus core and returning conjugate give the exact I.4.7 local type in
the A₅ quotient case. Sylow containment gives the exact J₂/J₃ type
alternatives, with the S₅ quotient retained for the transfer argument.
Neither this local type nor the full-core identity asserts ambient recognition.
Source: Aschbacher–Smith 14.2.16–17 and 14.3.6,15, pp.986–987,991,994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)

variable (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hnot hgP hgH hyp hK


include hG hempty hM hu hmany hcard e hne

/-- The opposite core belongs to the same selected A₅ component. -/
theorem source_single_a5_opposite_core_le_component_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ≤ K := by
  have hcore := source_single_a5_component_core_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,_,hker⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨hRT,_,hRQ,_,hRdot,_,_,hRc⟩ := source_single_a5_core_pair_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,hYR,_,_⟩ := source_single_a5_opposite_residual_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,_,_,_,_,hBM⟩ := source_terminal_single_a5_parabolic_of_large_actor_degrees
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hK e5
    (fun _ => Or.inl hd) hnot hspan
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  have hRH : R ≤ F.H := hRT.trans (F.invariant 1)
  have hHNK : F.H ≤ normalizer (K : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hK.le_pointNormalizer).mp
    have hh := hK.normal_span
    rwa [←hspan] at hh
  have hMR : M ≤ normalizer (R : Set G) := by
    change M ≤ normalizer ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 : Set G)
    rw [←hYR]
    exact ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le _ _)).mp
      (residualY_normal M Mc)).trans
      (normalizer_le_normalizer_characteristic_image (sourceResidual M Mc) (pCore 2 (sourceResidual M Mc)))
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let a := (subgroupOfEquivOfLe hK.le_pointNormalizer).symm
  let j := q.subgroupMap (K.subgroupOf F.H)
  let π : K →* F.terminalDot K := j.comp a.toMonoidHom
  let f : K →* alternatingGroup (Fin 5) := e5.toMonoidHom.comp π
  have hf : Function.Surjective f := e5.surjective.comp
    ((q.subgroupMap_surjective (K.subgroupOf F.H)).comp a.surjective)
  have hTN : (T : Subgroup G) ≤ normalizer (K : Set G) := (F.invariant 1).trans hHNK
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTN
  let S : Sylow 2 (alternatingGroup (Fin 5)) := P.mapSurjective hf
  obtain ⟨z,hzord⟩ := exists_prime_orderOf_dvd_card'
    (G := normalizer (S : Set (alternatingGroup (Fin 5)))) 3 (by
      rw [Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_card]
      decide)
  have hzmap : (z : alternatingGroup (Fin 5)) ∈ (normalizer (P : Set K)).map f := by
    rw [P.normalizer_map_surjective f hf]
    exact z.property
  obtain ⟨b,hb,hbz⟩ := hzmap
  have hbM : (b : G) ∈ M := hBM (by
    apply mem_map.mpr
    refine ⟨b,?_,rfl⟩
    rwa [←hP])
  let bH : F.H := ⟨b,hK.le_pointNormalizer b.property⟩
  obtain ⟨c,p,hp,hm,he⟩ := source_single_a5_whole_action_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hbp : p (q bH) = (f b : Equiv.Perm (Fin 5)) := hm (π b)
  have hb3 : orderOf (p (q bH)) = 3 := by
    rw [hbp,hbz,Subgroup.orderOf_coe,Subgroup.orderOf_coe,hzord]
  let fH := p.comp q
  let R₀ := R.subgroupOf F.H
  let A := R₀.map fH
  have hAc : Nat.card A = 4 := by
    change Nat.card ((R.subgroupOf F.H).map (p.comp q)) = 4
    rw [←Subgroup.map_map,card_map_of_injective hp]
    exact hRc
  have hbN : bH ∈ normalizer (R₀ : Set F.H) := by
    apply mem_normalizer_iff.mpr
    intro r
    exact (mem_normalizer_iff.mp (hMR hbM)) (r:G)
  have hAe : A ≤ alternatingGroup (Fin 5) :=
    Theory.SpecificGroups.SymmetricFive.four_le_alternating_of_normalized_by_three
      A hAc (fH bH) hb3 (R₀.le_normalizer_map fH (mem_map_of_mem fH hbN))
  have hfixed : ∀ x ∈ R₀, fH (bH*x*bH⁻¹) = fH x → fH x = 1 := by
    intro x hx hfix
    by_contra hne1
    have hxR : q x ∈ F.terminalDot R := mem_map_of_mem q hx
    rw [hRdot] at hxR
    have hs := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (F.terminalDot (F.X g)))
      (⟨q x,hxR⟩ : F.terminalDot (F.X g))
    have hsq : fH x ^ 2 = 1 := by
      have hh := congrArg (fun t : F.terminalDot (F.X g) => p t.val) hs
      change p (q x)^2 = 1
      simpa only [coe_pow,coe_one,map_pow,map_one] using hh
    have ho : orderOf (fH x) = 2 := (orderOf_eq_prime_iff (p:=2)).mpr ⟨hsq,hne1⟩
    have hcomm : Commute (fH x) (fH bH) := by
      apply Commute.symm
      exact mul_inv_eq_iff_eq_mul.mp (by simpa only [map_mul,map_inv] using hfix)
    exact Equiv.Perm.three_not_commute_even_involution_five _ _ ho
      (hAe (mem_map_of_mem fH hx)) hb3 hcomm
  have hk : R₀ ⊓ fH.ker ≤ K.subgroupOf F.H := by
    intro x hx
    have hxQ : (x:G) ∈ F.H.pCoreIn 2 := by
      have hxk : x ∈ pCore 2 F.H := by
        have hh := hx.2
        rw [MonoidHom.ker_comp_of_injective _ _ hp,QuotientGroup.ker_mk',hker] at hh
        exact hh
      exact mem_map_of_mem F.H.subtype hxk
    have hxW : (x:G) ∈ F.W := hRQ ▸ (show (x:G) ∈ R ⊓ F.H.pCoreIn 2 from ⟨hx.1,hxQ⟩)
    exact (hcore.le.trans (pCoreIn_le 2 K)) ((show F.W ≤ F.U from inf_le_left) hxW)
  have hh : R₀ ≤ K.subgroupOf F.H := le_of_fixedPointFree_image fH R₀
    (K.subgroupOf F.H) bH hbN b.property
    (by
      intro r hr
      apply mem_normalizer_iff.mpr
      intro k
      exact (mem_normalizer_iff.mp (hHNK r.property)) (k:G)) hk hfixed
  intro r hr
  exact hh (show (⟨r,hRH hr⟩ : F.H) ∈ R₀ from hr)

/-- The centralizing supplement vanishes modulo the original point:
the opposite core lies in K and the residual has trivial Sylow centralizer. -/
theorem source_single_a5_full_core_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) : F.U = F.H.pCoreIn 2 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let Y := sourceResidual M Mc
  let R := (F.I₂ Y).pCoreIn 2
  let Q := F.H.pCoreIn 2
  let D := Q ⊓ centralizer (F.U : Set G)
  have hUK := source_single_a5_component_core_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hRK := source_single_a5_opposite_core_le_component_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨hUD,hDU,hHD,_,_⟩ := source_single_a5_core_supplement_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,hYR,hYc,c,hcY,hc3,_⟩ := source_single_a5_opposite_residual_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,hRc,_⟩ := source_single_a5_opposite_orders_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,hRQ,_⟩ := source_single_a5_core_pair_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  change Y.pCoreIn 2 = R at hYR
  change Nat.card Y = 192 at hYc
  change Nat.card R = 64 at hRc
  change R ⊓ Q = F.W at hRQ
  have hHNK : F.H ≤ normalizer (K : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hK.le_pointNormalizer).mp
    have hh := hK.normal_span
    rwa [←hspan] at hh
  have hQH : Q ≤ F.H := pCoreIn_le 2 F.H
  have hDH : D ≤ F.H := inf_le_left.trans hQH
  let a := subgroupOfEquivOfLe hK.le_pointNormalizer
  let : Group.IsPerfect (K.subgroupOf F.H) := hK.component.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f:=a.toMonoidHom) a.surjective
  have hcomm : ⁅D,K⁆ ≤ F.Vi 1 := by
    have hD : ⁅D,K⁆ ≤ D := le_normalizer_iff_commutator_le_left.mp
      (hK.le_pointNormalizer.trans hHD)
    have hK' : ⁅D,K⁆ ≤ K := le_normalizer_iff_commutator_le_right.mp (hDH.trans hHNK)
    have hU : ⁅D,K⁆ ≤ F.U := by
      rw [hUK]
      exact (le_inf hK' (hD.trans inf_le_left)).trans
        (inf_pCoreIn_le_of_le 2 hK.le_pointNormalizer)
    rw [←hDU]
    exact le_inf hU hD
  have hZK : F.Vi 1 ≤ centralizer (K : Set G) := by
    apply le_centralizer_iff.mp
    exact hK.le_pointNormalizer.trans
      (normalizer_le_centralizer_of_card_two (F.Vi 1) (by simpa using F.card 1 (by decide)))
  have hDK : D ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_iterated_eq_bot D K
      (commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hZK)))
  let P := (Y ⊔ (T : Subgroup G)).pCoreIn 2
  have hPT : P ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G) from le_sup_right)]
      using pCoreIn_le_sylow (Y ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hDP : D ≤ P := by
    change D ≤ (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2
    rw [←h.centralizer]
    have hQT : Q ≤ (T : Subgroup G) := by
      have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
      have hh := pCoreIn_le_sylow F.H (T.subtype hTH)
      change Q ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
      rwa [map_subgroupOf_eq_of_le hTH] at hh
    exact le_inf ((inf_le_left.trans hQT).trans le_sup_right)
      (inf_le_right.trans (centralizer_le (le_conjugateSpanBy _ _)))
  have hYnorm : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp (residualY_normal M Mc)
  have hYP : Y ≤ normalizer (P : Set G) :=
    (show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left).trans
      ((Y ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G))))
  have hRY : R ≤ Y := hYR ▸ pCoreIn_le 2 Y
  have hRN : Y ≤ normalizer (R : Set G) := by
    rw [←hYR]
    exact Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hcR : c ∉ R := by
    intro hc
    have hh := orderOf_dvd_natCard (⟨c,hc⟩ : R)
    rw [←orderOf_coe,hc3,hRc] at hh
    norm_num at hh
  have hindex : R.relIndex Y = 3 := by
    have hh := relIndex_mul_card_of_le hRY
    rw [hRc,hYc] at hh
    omega
  have hgen : R ⊔ zpowers c = Y := sup_zpowers_eq_of_relIndex_prime hRY
    Nat.prime_three hindex hcY hcR
  have hCY : P ⊓ centralizer (Y : Set G) = ⊥ := by
    apply bot_unique
    rw [←Chapter14.Section06.source_residual_sylow_centralizer_eq_bot
      hG T hempty hM hu hmany hcard e]
    exact inf_le_inf_right _ hPT
  have hPR : P ⊓ centralizer (R : Set G) ≤ R :=
    centralizer_le_of_fixedPointFree_residual_complement P Y R c hYP hRN
      ((hPT.trans hM.1.2).trans hYnorm) hcY hgen hCY (by
        rw [←hYR,inf_comm]
        exact inf_pCoreIn_le_of_le 2 le_sup_left)
  have hDR : D ≤ R := (le_inf hDP (hDK.trans (centralizer_le hRK))).trans hPR
  have hDU' : D ≤ F.U := by
    have hh := le_inf hDR (show D ≤ Q from inf_le_left)
    rw [hRQ] at hh
    exact hh.trans inf_le_left
  exact (hUD.symm.trans (sup_eq_left.mpr hDU')).symm

/-- The actual point centralizer has the minus core, returning involution
fusion, and either the exact I.4.7 local type or the full S₅ quotient. -/
theorem source_single_a5_involution_centralizer_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    F.U = F.H.pCoreIn 2 ∧
      ∃ z : G, orderOf z = 2 ∧ F.H = centralizer ({z} : Set G) ∧
        Janko23.ambientCore z = F.U ∧
        Nonempty (Janko23.localCore z ≃* MinusExtraspecial.Model) ∧
        (∃ t ∈ F.U, IsConj z t ∧ t ≠ z) ∧
        ((Janko23.HTypeAt z ∧ (Janko23.J2Type G ∨ Janko23.J3Type G)) ∨ Nonempty
          ((Janko23.involutionCentralizer z ⧸ Janko23.localCore z) ≃* Equiv.Perm (Fin 5))) := by
  have hfull := source_single_a5_full_core_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨eU⟩ := source_single_a5_minus_model_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,_,hfit⟩ := source_single_a5_full_parabolic_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,_,hker⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hzcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z,hzo⟩ := exists_prime_orderOf_dvd_card' (G := F.Vi 1) 2 (by rw [hzcard])
  have hz : orderOf (z:G) = 2 := (orderOf_coe z).trans hzo
  have hZ : zpowers (z:G) = F.Vi 1 := eq_of_le_of_card_ge (zpowers_le.mpr z.property)
    (by rw [Nat.card_zpowers,hz,hzcard])
  have hHz : F.H = centralizer ({(z:G)} : Set G) := by
    change normalizer (F.Vi 1 : Set G) = _
    exact (congrArg (fun S : Subgroup G => normalizer (S : Set G)) hZ.symm).trans
      (normalizer_zpowers_eq_centralizer_of_order_two (z:G) hz)
  have hecore : Nonempty (Janko23.localCore (z:G) ≃* MinusExtraspecial.Model) := by
    change Nonempty ((generalizedFitting (centralizer ({(z:G)} : Set G))) ≃* MinusExtraspecial.Model)
    rw [←hHz,hfit]
    exact ⟨((pCore 2 F.H).equivMapOfInjective F.H.subtype F.H.subtype_injective).trans
      ((MulEquiv.subgroupCongr hfull.symm).trans eU)⟩
  have hamb : Janko23.ambientCore (z:G) = F.U := by
    change (generalizedFitting (centralizer ({(z:G)} : Set G))).map
      (centralizer ({(z:G)} : Set G)).subtype = F.U
    rw [←hHz,hfit]
    exact hfull.symm
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let t : G := g*(z:G)*g⁻¹
  have htV : t ∈ rankTwoSeed T M :=
    (mem_normalizer_iff.mp (F.P_le_seed_normalizer (sourceResidual M Mc)
      h.L_normalizes_seed hgP) (z:G)).mp (F.le_seed 1 z.property)
  have htU : t ∈ F.U := le_conjugateSpanBy _ _ htV
  have htconj : IsConj (z:G) t := isConj_iff.mpr ⟨g,rfl⟩
  have htne : t ≠ (z:G) := by
    intro he
    apply hgH
    rw [hHz]
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have hweak : ¬ ∀ x ∈ Janko23.ambientCore (z:G), IsConj (z:G) x → x = (z:G) := by
    intro hh
    exact htne (hh t (hamb.symm ▸ htU) htconj)
  have hq : Nonempty ((Janko23.involutionCentralizer (z:G) ⧸ Janko23.localCore (z:G)) ≃*
      alternatingGroup (Fin 5)) ∨
      Nonempty ((Janko23.involutionCentralizer (z:G) ⧸ Janko23.localCore (z:G)) ≃*
        Equiv.Perm (Fin 5)) := by
    change Nonempty (((centralizer ({(z:G)} : Set G)) ⧸ generalizedFitting
      (centralizer ({(z:G)} : Set G))) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (((centralizer ({(z:G)} : Set G)) ⧸ generalizedFitting
      (centralizer ({(z:G)} : Set G))) ≃* Equiv.Perm (Fin 5))
    rw [←hHz]
    let q := QuotientGroup.quotientMulEquivOfEq (hfit.trans hker.symm)
    rcases source_single_a5_whole_group_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd with ha | ha
    · exact Or.inl (ha.map q.trans)
    · exact Or.inr (ha.map q.trans)
  refine ⟨hfull,z,hz,hHz,hamb,hecore,⟨t,htU,htconj,htne⟩,?_⟩
  rcases hq with he | he
  · have hlocal : Janko23.HTypeAt (z:G) := ⟨hz,hecore,he,hweak⟩
    have hT : (T : Subgroup G) ≤ Janko23.involutionCentralizer (z:G) := by
      change (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G)
      rw [←hHz]
      exact F.invariant 1
    exact Or.inl ⟨hlocal,hlocal.janko_types_of_sylow_le T hT⟩
  · exact Or.inr he

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
