module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionCore
public import Theory.GroupTheory.PGroup.UniqueInvolution
public import Theory.GroupTheory.CyclicFourQuotientTransfer
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.AmbientAction
public import Theory.SpecificGroups.SymmetricSix.CubicCentralizerOrder

/-!
# The two-core of the actual opposite centralizer

The preceding residual-centralizer calculation embeds N = O₂(C_G(w)) in
the original four-element quotient H/(O²(H)R). Its unique involution is w,
so N is cyclic of order two or four. The faithful marked six-letter action
also gives N ∩ N_G(A) = ⟨w⟩ for every source elementary factor A.

If N had order four, the transfer quotient would be cyclic. Order-four
transfer then conjugates its generator to an element of T whose square
lies in RU. Every involution there is conjugate to z, contradicting the
already established nonfusion of z and w. Thus N = ⟨w⟩, for the literal
constructed w and the original Sylow subgroup T.

Source: Aschbacher--Smith 14.3.22, printed p.999. The final cyclic-four
exclusion uses Thompson transfer. Global quotient recognition and the RQ
marking remain obligations of the core-collapse assembly.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs


include hc s
/-- The global two-core embeds in the original four-element transfer quotient. -/
theorem source_triple_twoCore_transfer_embedding
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let N := (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2
    let B := localResidual F ⊔ (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    ∃ hB : (B.subgroupOf F.H).Normal, letI := hB;
      ∃ f : N →* (F.H ⧸ B.subgroupOf F.H), Function.Injective f ∧
        Nat.card (F.H ⧸ B.subgroupOf F.H)=4 := by
  intro N B
  let C := centralizer ({tripleProduct d a}:Set G)
  have hlocal := source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨S,hS⟩ := source_triple_global_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hNT : N≤(T:Subgroup G) := ((pCoreIn_le_sylow C S).trans_eq hS).trans inf_le_left
  have hNH : N≤F.H := hNT.trans (F.invariant 1)
  have hNI := (source_triple_twoCore_parabolic_centralizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).1
  have hBT := (source_transfer_subgroup_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2
  have hNB : N⊓B=⊥ := by
    apply bot_unique
    intro x hx
    have hi : x∈F.I₂ (sourceResidual M Mc) :=
      (sup_le (le_conjugateSpanBy _ _) (pCoreIn_le 2 _))
        (hBT ▸ (show x∈B⊓(T:Subgroup G) from ⟨hx.2,hNT hx.1⟩))
    exact hNI ▸ (show x∈N⊓F.I₂ (sourceResidual M Mc) from ⟨hx.1,hi⟩)
  let hB : (B.subgroupOf F.H).Normal := hlocal.quotient_normal
  let f : N →* (F.H ⧸ B.subgroupOf F.H) :=
    (QuotientGroup.mk' (B.subgroupOf F.H)).comp (inclusion hNH)
  refine ⟨hB,f,?_,hlocal.quotient_index⟩
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  have hxB : (x:G)∈B := (QuotientGroup.eq_one_iff (inclusion hNH x)).mp hx
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hNB ▸ ⟨x.property,hxB⟩)))

/-- The actual two-core has order dividing four. -/
theorem source_triple_twoCore_card_dvd_four
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    Nat.card ((centralizer ({tripleProduct d a}:Set G)).pCoreIn 2) ∣ 4 := by
  obtain ⟨hB,f,hf,hcard⟩ := source_triple_twoCore_transfer_embedding
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  exact hcard ▸ card_dvd_of_injective f hf

/-- Its unique involution is the literal opposite product. -/
theorem source_triple_twoCore_unique_involution
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    ∀ x ∈ (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2,
      orderOf x=2 → x=tripleProduct d a := by
  let C := centralizer ({tripleProduct d a}:Set G)
  let N := C.pCoreIn 2
  let P := (T:Subgroup G)⊓C
  have hcentral := source_triple_twoCore_central_in_point_centralizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨S,hS⟩ := source_triple_global_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hNP : N≤P := (pCoreIn_le_sylow C S).trans_eq hS
  have hNQ := source_triple_twoCore_inf_Q hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hWQ : zpowers (tripleProduct d a)≤F.H.pCoreIn 2 := hNQ ▸ inf_le_right
  have hJQ : closure ({z,tripleProduct d a}:Set G)≤F.H.pCoreIn 2 := by
    apply (closure_le _).mpr
    intro y hy
    rcases Set.mem_insert_iff.mp hy with hy|hy
    · exact hy.symm ▸ ((hc.strict.le (s.point.symm ▸ mem_zpowers z)).1)
    · exact (Set.mem_singleton_iff.mp hy).symm ▸ hWQ (mem_zpowers _)
  intro x hx hx2
  have hxO : x∈omegaCenterIn P := (mem_omegaCenterIn_iff P x).mpr
    ⟨hNP hx,fun p hp => (hcentral hx).2 p ⟨F.invariant 1 hp.1,hp.2⟩,
      hx2 ▸ pow_orderOf_eq_one x⟩
  have hxQ := hJQ ((source_triple_omega_center hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s) ▸ hxO)
  have hxW : x∈zpowers (tripleProduct d a) := hNQ ▸ ⟨hx,hxQ⟩
  have hw2 := (source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x:=⟨x,hxW⟩) (y:=⟨tripleProduct d a,mem_zpowers _⟩)
    ((orderOf_coe _).symm.trans hx2) ((orderOf_coe _).symm.trans hw2))

/-- The remaining two-core is cyclic of order at most four. -/
theorem source_triple_twoCore_cyclic
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    IsCyclic ((centralizer ({tripleProduct d a}:Set G)).pCoreIn 2) := by
  let N := (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2
  have hcentral := source_triple_twoCore_central_in_point_centralizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  let : IsMulCommutative N := ⟨⟨fun x y => Subtype.ext ((hcentral y.property).2 x (hcentral x.property).1)⟩⟩
  have hNQ := source_triple_twoCore_inf_Q hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hwN : tripleProduct d a∈N := (hNQ.symm ▸ mem_zpowers (tripleProduct d a)).1
  have hw2 := (source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
  apply (isPGroup_pCoreIn 2 _).isCyclic_of_unique_involution_of_isMulCommutative
  refine ⟨⟨tripleProduct d a,hwN⟩,(orderOf_coe _).symm.trans hw2,?_⟩
  intro x hx
  exact Subtype.ext (source_triple_twoCore_unique_involution hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself x x.property ((orderOf_coe x).trans hx))

/-- On the literal marked elementary-factor normalizer, the two-core is
exactly W. The faithful six-letter action reduces its order to two. -/
theorem source_triple_twoCore_inf_factor_normalizer
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAR : A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA : rankTwoSeed T M≤A) (hAc : Nat.card A=16)
    (hc8 : Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN : F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2⊓normalizer (A:Set G)=
      zpowers (tripleProduct d a) := by
  let C := centralizer ({tripleProduct d a}:Set G)
  let N := C.pCoreIn 2
  let P := N⊓normalizer (A:Set G)
  let H₀ := F.H⊓normalizer (A:Set G)
  let K := sourceResidual M Mc⊔(pResidual 2 H₀).map H₀.subtype
  have h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hselfA := hself A inferInstance hAR hVA hAc hc8 hAN
  have hNK := (factor_block_normalizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).2
  obtain ⟨hAK,qA,eK,_,heA⟩ := factor_block_split_model_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  let π : normalizer (K:Set G) →* Equiv.Perm (Fin 6) :=
    SemidirectProduct.rightHom.comp
      (BinaryPermutation.SixNaturalSplit.ambientAction K eK natural_block_normalizer)
  have hπ (x : normalizer (K:Set G)) : π x=1 ↔ (x:G)∈A := by
    change (BinaryPermutation.SixNaturalSplit.ambientAction K eK natural_block_normalizer x).right=1 ↔ _
    rw [BinaryPermutation.SixNaturalSplit.ambientAction_right_eq_one K A hAK eK heA natural_block_normalizer,←hselfA]
  have hPN : P≤normalizer (K:Set G) := inf_le_right.trans hNK.le
  let f : P →* Equiv.Perm (Fin 6) := π.comp (inclusion hPN)
  have hNI := (source_triple_twoCore_parabolic_centralizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).1
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxA : (x:G)∈A := (hπ (inclusion hPN x)).mp hx
    have hxI := (hAR.trans (pCoreIn_le 2 _)) hxA
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hNI ▸ ⟨x.property.1,hxI⟩)))
  have haK : a∈K := mem_sup_left s.actor_mem
  let aa : normalizer (K:Set G) := ⟨a,K.le_normalizer haK⟩
  have ha3 : aa^3=1 := Subtype.ext (s.actor_order ▸ pow_orderOf_eq_one a)
  have haπ : orderOf (π aa)=3 := by
    apply orderOf_eq_prime
    · rw [←map_pow,ha3,map_one]
    · intro hh
      have haA := (hπ aa).mp hh
      have hd : orderOf a∣2 := orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian a haA)
      rw [s.actor_order] at hd
      norm_num at hd
  have hLI : sourceResidual M Mc≤F.I₂ (sourceResidual M Mc) :=
    (source_parabolic_residual_core_structure_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1.symm.le.trans (map_subtype_le _)
  have hNa : N≤centralizer ({a}:Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (((source_triple_twoCore_parabolic_centralizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).2 hx)
        a ⟨hLI s.actor_mem,s.actor_centralizes_product hc⟩).symm
  have hcP : Nat.card P≤2 := Theory.SpecificGroups.SymmetricSix.twoGroup_card_le_two_of_centralizes_cubic
    ((isPGroup_pCoreIn 2 C).to_le inf_le_left) f hf (π aa) haπ (fun x => by
      have hh : Commute (inclusion hPN x) aa := Subtype.ext
        (mem_centralizer_singleton_iff.mp (hNa x.property.1))
      exact hh.map π)
  have hNQ := source_triple_twoCore_inf_Q hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hWP : zpowers (tripleProduct d a)≤P := le_inf
    (hNQ ▸ inf_le_left) ((hNQ ▸ inf_le_right).trans (le_sup_right.trans hAN))
  have hw2 := (source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
  exact (eq_of_le_of_card_ge hWP (by rw [Nat.card_zpowers,hw2];exact hcP)).symm

/-- The sole possible obstruction to W being the whole two-core is a
cyclic four generated by a square root of w outside every marked factor
normalizer. This is a reduction, not an assertion that the obstruction exists. -/
private theorem source_triple_twoCore_eq_or_four
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let N := (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2
    N=zpowers (tripleProduct d a) ∨
      ∃ x : G, zpowers x=N ∧ orderOf x=4 ∧ x^2=tripleProduct d a ∧
        ∀ A : Subgroup G, IsElementaryAbelian 2 A →
          A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2 → rankTwoSeed T M≤A →
          Nat.card A=16 → Nat.card (A⊓F.U:Subgroup G)=8 →
          F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G) →
          x∉normalizer (A:Set G) := by
  intro N
  have hNQ := source_triple_twoCore_inf_Q hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hWN : zpowers (tripleProduct d a)≤N := hNQ ▸ inf_le_left
  have hw2 := (source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
  by_cases heq : N=zpowers (tripleProduct d a)
  · exact Or.inl heq
  right
  have hdiv := source_triple_twoCore_card_dvd_four hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  change Nat.card N ∣ 4 at hdiv
  have hbound := Nat.le_of_dvd (by decide : 0<4) hdiv
  have hlow : 2≤Nat.card N := by
    have hh := Nat.card_le_card_of_injective (inclusion hWN) (inclusion_injective hWN)
    rwa [Nat.card_zpowers,hw2] at hh
  have hcardN : Nat.card N=4 := by
    have hne2 : Nat.card N≠2 := by
      intro hh
      exact heq (eq_of_le_of_card_ge hWN (by rw [Nat.card_zpowers,hw2,hh])).symm
    have hne3 : Nat.card N≠3 := by intro hh;rw [hh] at hdiv;norm_num at hdiv
    omega
  let hcyc : IsCyclic N := source_triple_twoCore_cyclic hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨x,hx⟩ := N.isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hxN : x∈N := hx ▸ mem_zpowers x
  have hx4 : orderOf x=4 := by rw [←Nat.card_zpowers,hx,hcardN]
  have hx2 : x^2=tripleProduct d a := source_triple_twoCore_unique_involution
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
    (x^2) (N.pow_mem hxN 2) (by rw [orderOf_pow,hx4];decide)
  refine ⟨x,hx,hx4,hx2,?_⟩
  intro A hEA hAR hVA hAc hc8 hAN hxA
  let := hEA
  have hi := source_triple_twoCore_inf_factor_normalizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself A hAR hVA hAc hc8 hAN
  have hxW : x∈zpowers (tripleProduct d a) := hi ▸ ⟨hxN,hxA⟩
  have hd : orderOf (⟨x,hxW⟩ : zpowers (tripleProduct d a)) ∣
      Nat.card (zpowers (tripleProduct d a)) :=
    _root_.orderOf_dvd_natCard (⟨x,hxW⟩ : zpowers (tripleProduct d a))
  rw [←orderOf_coe,Nat.card_zpowers,hx4,hw2] at hd
  norm_num at hd

/-- The actual opposite centralizer has two-core W. If the cyclic-four
alternative occurred, transfer through H/(O²(H)R) would conjugate its generator
to an element whose square is an involution in RU, contradicting nonfusion. -/
theorem source_triple_twoCore_eq
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2=zpowers (tripleProduct d a) := by
  rcases source_triple_twoCore_eq_or_four hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself with heq|⟨x,hx,hx4,hx2,_⟩
  · exact heq
  exfalso
  let C := centralizer ({tripleProduct d a}:Set G)
  let N := C.pCoreIn 2
  let B := localResidual F⊔(F.I₂ (sourceResidual M Mc)).pCoreIn 2
  have hcN : Nat.card N=4 := by
    have hh : Nat.card (zpowers x) = 4 := by rw [Nat.card_zpowers, hx4]
    simpa [N, C, hx] using hh
  let : IsCyclic N := source_triple_twoCore_cyclic hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨hB,f,hf,hcB⟩ := source_triple_twoCore_transfer_embedding hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  let := hB
  have hsurj : Function.Surjective f := (hf.bijective_of_nat_card_le (by rw [hcB,hcN])).2
  let : IsCyclic (F.H⧸B.subgroupOf F.H) := isCyclic_of_surjective f hsurj
  obtain ⟨S,hS⟩ := source_triple_global_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hNT : N≤(T:Subgroup G) := ((pCoreIn_le_sylow C S).trans_eq hS).trans inf_le_left
  have hxT := hNT (hx ▸ mem_zpowers x)
  have hno : ∀ K : Subgroup G, K.Normal → K.index≠2 := by
    intro K hK
    let := hG.simple
    rcases hK.eq_bot_or_eq_top with hh|hh
    · rw [hh,index_bot]
      intro hcardG
      let : IsCyclic G := isCyclic_of_prime_card hcardG
      exact hG.nonabelian inferInstance
    · simp [hh]
  obtain ⟨y,hxy,hysq⟩ := T.exists_isConj_square_mem_of_cyclic_four_quotient hno F.H
    (F.invariant 1) (B.subgroupOf F.H) hcB ⟨x,hxT⟩ ((orderOf_coe _).symm.trans hx4)
  have hyB : (y:G)^2∈B := hysq
  have hyBT : (y:G)^2∈B⊓(T:Subgroup G) :=
    ⟨hyB,(T:Subgroup G).pow_mem y.property 2⟩
  have hyRU : (y:G)^2∈(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U := by
    rw [source_transfer_subgroup_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs |>.2] at hyBT
    simpa [sup_comm] using hyBT
  have hwConj : IsConj (tripleProduct d a) ((y:G)^2) := by
    simpa [hx2] using hxy.pow 2
  have hlocal := source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hy2 : orderOf ((y:G)^2)=2 := by
    obtain ⟨c,hc⟩ := hwConj
    exact (SemiconjBy.orderOf_eq (↑c) hc).symm.trans hlocal.involution
  have hzV : z∈F.Vi 1 := s.point.symm ▸ mem_zpowers z
  have hz1 : z≠1 := by
    have hz2 : orderOf z=2 := by
      rw [←Nat.card_zpowers,←s.point]
      simpa using F.card 1 (by decide)
    intro hh
    simp [hh] at hz2
  have hzConj := source_ru_involutions_fused_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs z hzV hz1 ((y:G)^2) hyRU hy2
  exact hlocal.nonfusion (hzConj.trans hwConj.symm)

omit s in
/-- The literal opposite involution with its complete local geometry and
its exact global two-core. Global quotient recognition remains separate. -/
theorem source_opposite_core_eq_of_cyclicTI
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    ∃ z w : G, LocalGeometry F (sourceResidual M Mc) z w ∧
      (centralizer ({w}:Set G)).pCoreIn 2=zpowers w := by
  obtain ⟨z,d,a,s,_,_⟩ := source_triple_involution hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc
  exact ⟨z,tripleProduct d a,
    source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself,
    source_triple_twoCore_eq hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
