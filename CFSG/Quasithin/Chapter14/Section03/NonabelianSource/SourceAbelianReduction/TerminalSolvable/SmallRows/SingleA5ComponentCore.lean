module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5CorePair
public import Theory.SpecificGroups.SymmetricFive.ThreeCentralizer
public import Theory.SpecificGroups.Alternating.FiveSylowNormalizerCard
public import Theory.SpecificGroups.AlternatingFiveSquareGeneratorKernel

/-!
# The exact two-core of the original normalized A₅ component

The original Borel contains an actor of order three in the dotted group
and normalizes the opposite core R. If R∩K had trivial image, its
commutators with this actor would vanish in the dotted group, putting the
order-four image of R in a three-cycle centralizer of order six. Thus
R∩K has nontrivial image. The elementary opposite quotient supplies its
square bound, and [O₂(K),R∩K]≤U follows from the core-pair calculation.
Normal generation and the A₅ central-cover involution obstruction give
U=O₂(K) on the same selected component.

The whole dotted group is A₅ or S₅. The join KT therefore has index at
most two in H and contains a Sylow two-subgroup, so H=KT. Its original
minimal-parabolic and two-residual statements now apply to the actual H.
These conclusions do not identify O₂(H) with U or establish the ambient
J₂/J₃ recognition needed for the Borel contradiction.

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

/-- The opposite core and the actual Borel eliminate the central two-cover
of the selected A₅ component above U. -/
theorem source_single_a5_component_core_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) : F.U = K.pCoreIn 2 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let dg := Recognition.rankTwo_closure_geometry h F hne
  obtain ⟨_,hUK⟩ := source_single_a5_closure_component_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨hZ,hex,_,hker⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨hRT,hsplit,_,hRQ,_,_,_,hRc⟩ := source_single_a5_core_pair_of_four hG T hempty hM hu hmany
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
  have hjker : j.ker = pCore 2 (K.subgroupOf F.H) := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk',hker]
    exact (pCore_subnormal_eq_comap 2 hK.component.subnormal).symm
  have hfker : f.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e5.injective]
    change (j.comp a.toMonoidHom).ker = pCore 2 K
    rw [←MonoidHom.comap_ker,hjker,←pCore_map_iso 2 a,
      comap_map_eq_self_of_injective a.injective]
  let N := R.subgroupOf K
  have hN : N.map f ≠ ⊥ := by
    intro hz
    have hNk : N ≤ f.ker := (map_eq_bot_iff N).mp hz
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
    let pR : F.terminalDot R →* Equiv.Perm (Fin 5) := p.comp (F.terminalDot R).subtype
    have hpR : Function.Injective pR := hp.comp Subtype.val_injective
    have hcentral (r : F.terminalDot R) : pR r * p (q bH) = p (q bH) * pR r := by
      obtain ⟨rH,hr,hrq⟩ := r.property
      have hrR : (rH : G) ∈ R := hr
      have hbR := hMR hbM
      have hrK := hHNK rH.property
      have hwR : ⁅(rH : G),(b : G)⁆ ∈ R := by
        have hv := (mem_normalizer_iff.mp hbR ((rH : G)⁻¹)).mp (R.inv_mem hrR)
        simpa only [commutatorElement_def,mul_assoc] using R.mul_mem hrR hv
      have hwK : ⁅(rH : G),(b : G)⁆ ∈ K := by
        have hv := (mem_normalizer_iff.mp hrK (b : G)).mp b.property
        exact K.mul_mem hv (K.inv_mem b.property)
      let w : K := ⟨⁅(rH : G),(b : G)⁆,hwK⟩
      have hwf : f w = 1 := hNk hwR
      change e5 (π w) = 1 at hwf
      have hwπ : π w = 1 := e5.injective (by simpa only [map_one] using hwf)
      have hwq : q ⁅rH,bH⁆ = 1 := congrArg Subtype.val hwπ
      have hcq : ⁅p (q rH),p (q bH)⁆ = 1 := by
        rw [←map_commutatorElement,←map_commutatorElement,hwq,map_one]
      change p (r : F.TerminalHdot) * p (q bH) = p (q bH) * p (r : F.TerminalHdot)
      rw [←hrq]
      exact commutatorElement_eq_one_iff_mul_comm.mp hcq
    have hdvd := Theory.SpecificGroups.SymmetricFive.card_dvd_six_of_centralizes_three
      (p (q bH)) hb3 pR hpR hcentral
    rw [hRc] at hdvd
    norm_num at hdvd
  have hsq : ∀ r ∈ R, r^2 ∈ F.U := by
    let L := sourceResidual M Mc
    let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
    have hPhi : (frattini F.U).map F.U.subtype=F.Vi 1 := by
      rw [dg.frattini_point]
      exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
    have hcomm : ⁅F.U,F.U⁆≤F.Vi 1 := by
      rw [←F.U.map_subtype_commutator]
      exact (map_mono (f:=F.U.subtype) (commutator_le_frattini_of_isPGroup (p:=2))).trans hPhi.le
    have hsquare : ∀u∈F.U,u^2∈F.Vi 1 := fun u hu=>
      hPhi ▸ mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨u,hu⟩:F.U))
    have hUspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
    obtain ⟨e₀,_,hgen,_,_,_,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
      F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
        h.centralizer hcomm hsquare hUspan hne g hgP hgH
    let := F.binary_source_E_normal_in_core L h.L_normalizes_seed g hgP hgen.symm hcomm
    let := F.binary_source_quotient_elementary L h.L_normalizes_seed g hgP hgen.symm hcore
      (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
    intro r hr
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ (F.E g).subgroupOf R))
      (QuotientGroup.mk' ((F.E g).subgroupOf R) ⟨r,hr⟩)
    rw [←map_pow] at hh
    have hh' := (QuotientGroup.eq_one_iff _).mp hh
    have hrE : r ^ 2 ∈ F.E g := hh'
    exact (show F.E g ≤ F.U from inf_le_left.trans inf_le_left) hrE
  let A := F.U.subgroupOf K
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer
    (hUK.trans (pCoreIn_le 2 K))).mpr
    (hK.le_pointNormalizer.trans (le_normalizer_conjugateSpanBy _ _))
  have hA : A ≤ f.ker := by
    rw [hfker]
    intro u hu
    obtain ⟨v,hv,he⟩ := hUK hu
    exact (show v=u from Subtype.ext he) ▸ hv
  have hKNQ : K.pCoreIn 2 ≤ F.H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hK.le_pointNormalizer hHNK
  have hcomm : ⁅f.ker,N⁆ ≤ A := by
    intro x hx
    have hm := mem_map_of_mem K.subtype hx
    rw [map_commutator,hfker] at hm
    have hnR : N.map K.subtype ≤ R := by
      rw [subgroupOf_map_subtype]
      exact inf_le_left
    have hh := (commutator_mono hKNQ hnR) hm
    rw [commutator_comm] at hh
    exact hRQ hh
  let : Group.IsPerfect (K.subgroupOf F.H) := hK.component.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f:=a.symm.toMonoidHom) a.symm.surjective
  have hpK : IsPPerfect 2 K := by
    intro D hD hp
    let := hD
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ D)
  have he := alternatingGroup.kernel_eq_of_square_normal_generator f hf
    (hfker ▸ pCore_isPGroup) hpK A N hA hN hcomm (fun r hr => hsq r hr)
  have hm := congrArg (Subgroup.map K.subtype) he
  rw [hfker,map_subgroupOf_eq_of_le (hUK.trans (pCoreIn_le 2 K))] at hm
  exact hm.symm

/-- The whole point normalizer is the actual minimal outside parabolic KT,
with its original selected component as embedded two-residual. -/
theorem source_single_a5_full_parabolic_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    F.H = K ⊔ (T : Subgroup G) ∧
      (pResidual 2 F.H).map F.H.subtype = K ∧
      F.H ∈ Chapter3.HStar (T : Subgroup G) M ∧
      generalizedFitting F.H = pCore 2 F.H := by
  obtain ⟨_,_,_,hker⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  let J := K ⊔ (T : Subgroup G)
  have hJH : J ≤ F.H := sup_le hK.le_pointNormalizer (F.invariant 1)
  let A := J.subgroupOf F.H
  let S : Sylow 2 F.H := T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)
  have hSA : (S : Subgroup F.H) ≤ A := by
    intro t ht
    exact (show (T : Subgroup G) ≤ J from le_sup_right) ht
  have hodd : ¬2 ∣ A.index := fun hh => S.not_dvd_index (hh.trans (index_dvd_of_le hSA))
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hqA : q.ker ≤ A := by
    rw [QuotientGroup.ker_mk',hker]
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSA
  have hkc : Nat.card (F.terminalDot K) = 60 := by
    rw [Nat.card_congr e5.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hfull : Nat.card F.TerminalHdot = 60 ∨ Nat.card F.TerminalHdot = 120 := by
    rcases source_single_a5_whole_group_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd with hl | hr
    · obtain ⟨d⟩ := hl
      left
      rw [Nat.card_congr d.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · obtain ⟨d⟩ := hr
      right
      rw [Nat.card_congr d.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
      norm_num [Nat.factorial]
  have hkindex : (F.terminalDot K).index = 1 ∨ (F.terminalDot K).index = 2 := by
    have hc := (F.terminalDot K).card_mul_index
    rw [hkc] at hc
    rcases hfull with hcH|hcH <;> rw [hcH] at hc <;> omega
  have hdot : F.terminalDot K ≤ A.map q := by
    apply map_mono
    intro k hk
    exact (show K ≤ J from le_sup_left) hk
  have hAi : A.index = 1 := by
    have hh := index_dvd_of_le hdot
    rw [A.index_map_eq (QuotientGroup.mk'_surjective _) hqA] at hh
    rcases hkindex with hi|hi
    · rw [hi] at hh
      exact Nat.eq_one_of_dvd_one hh
    · rw [hi] at hh
      rcases (Nat.dvd_prime Nat.prime_two).mp hh with h1|h2
      · exact h1
      · exact (hodd (by rw [h2])).elim
  have hHJ : F.H = J := by
    apply le_antisymm ?_ hJH
    intro x hx
    exact (show (⟨x,hx⟩ : F.H) ∈ A from (index_eq_one.mp hAi) ▸ mem_top _)
  obtain ⟨_,hstar,hres,_,_,hfit,_⟩ := source_terminal_single_a5_parabolic_of_large_actor_degrees
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hK e5
    (fun _ => Or.inl hd) hnot hspan
  refine ⟨hHJ,?_,?_,?_⟩
  · exact (congrArg (fun X : Subgroup G => (pResidual 2 X).map X.subtype) hHJ).trans hres
  · exact (congrArg (fun X : Subgroup G => X ∈ Chapter3.HStar (T : Subgroup G) M) hHJ).mpr hstar
  · exact (congrArg (fun X : Subgroup G => generalizedFitting X = pCore 2 X) hHJ).mpr hfit

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
