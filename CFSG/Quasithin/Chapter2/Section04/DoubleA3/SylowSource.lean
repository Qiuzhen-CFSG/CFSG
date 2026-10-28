module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.CubicPairThompsonSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.CubicPairGlobalSource
public import CFSG.Quasithin.Chapter2.Section04.CoreElementarySource

/-!
# The original paired-cubic Sylow geometry

Each adjacent mixed elementary product is normalized by an original escaping
cubic block. Its relative normalizer therefore lies in the original Γ family.
The elementary-core source theorem excludes the larger C.6 Sylow alternative.
Consequently S has index two in T, and its Baumann and Thompson subgroups
agree with J(T). All indices, family identities and core spans retain the
original selected subgroup and ambient Sylow subgroup.

Source: Aschbacher–Smith 2.4.27 and 2.4.30, printed pp.545–547.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_join_of_commutator (K U V : Subgroup G)
    (hn : K ≤ normalizer (U : Set G)) (hc : ⁅K,V⁆ ≤ U) :
    K ≤ normalizer ((U ⊔ V : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro k hk w hw
  have hU : U ≤ (U ⊔ V).comap (MulAut.conj k).toMonoidHom := by
    intro u hu
    exact (show U ≤ U ⊔ V from le_sup_left) ((mem_normalizer_iff.mp (hn hk) u).mp hu)
  have hV : V ≤ (U ⊔ V).comap (MulAut.conj k).toMonoidHom := by
    intro v hv
    change k * v * k⁻¹ ∈ U ⊔ V
    have hh := (U ⊔ V).mul_mem ((show U ≤ U ⊔ V from le_sup_left) (hc (commutator_mem_commutator hk hv)))
      ((show V ≤ U ⊔ V from le_sup_right) hv)
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
  exact (sup_le hU hV) hw

private theorem pair_mixed_escape
    {H M₀ K L R M : Subgroup G}
    (c : OriginalHypotheses H M₀ (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hK : ChapterC.IsAlternatingBlock K 3) (hL : ChapterC.IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M₀, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) = H.pCoreIn 2)
    (hi : R.relIndex M₀ = 2) (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (houtK : ¬ K ≤ M) (houtL : ¬ L ≤ M)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups R)
    (hindex : (H.pCoreIn 2).relIndex A = 2) :
    ¬ H ⊓ normalizer ((H.pCoreIn 2 ⊔ A : Subgroup G) : Set G) ≤ M := by
  let Q := H.pCoreIn 2
  let U₁ := RankOne.U K
  let U₂ := RankOne.U L
  let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
  let D := R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  have hf := ChapterC.Section06.rankOne_pair_family_from_original c h h' hKL hpair ht hfull hi x hx hnc
  obtain ⟨P,P',_,hg,_⟩ := ChapterC.Section06.cubic_pair_geometry_from_original
    c h h' hK hL hKL hpair ht hfull hi x hx hnc
  have hAQ : A ≠ Q := by
    intro he
    rw [he,relIndex_self] at hindex
    omega
  have hAQx : A ≠ Q.map (MulAut.conj x⁻¹).toMonoidHom := by
    intro he
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ A) A bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,hindex] at hc
    have hAcard : Nat.card A = Nat.card Q := by rw [he,card_map_of_injective (MulAut.conj x⁻¹).injective]
    rw [hAcard] at hc
    have hb := hg.core_card
    change 4 * Nat.card (Q ⊓ Q.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) ≤ Nat.card Q at hb
    rw [←he] at hb
    have hp : 0 < Nat.card (Q ⊓ A : Subgroup G) := Nat.card_pos
    omega
  have hnQ : H ≤ normalizer (Q : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.residual_sup_sylow
  have hLH : L ≤ H := (le_sup_right.trans le_sup_left).trans_eq c.residual_sup_sylow
  have hi₄ := h.fourModuleSourceInputs hKL h'.module_le M₀ R x hx (c.R_normal hx) hi hpair ht hnc
  have hcross := ChapterC.Section05.ConjugateSource.FourModuleOrbit.cross_commutators hi₄.toInputs
  have hV₂ : V₂ ≤ RankOne.Q R K := by
    rw [h.core]
    exact le_inf (h'.conjugate_le (c.R_normal hx))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross.2.1))
  have hV₁ : V₁ ≤ RankOne.Q R L := by
    rw [h'.core]
    exact le_inf (h.conjugate_le (c.R_normal hx))
      (commutator_eq_bot_iff_le_centralizer.mp hcross.2.2.1)
  have hKD : K ≤ centralizer (D : Set G) := le_centralizer_iff.mp
    (inf_le_right.trans (centralizer_le (show K ≤ K ⊔ L from le_sup_left)))
  have hLD : L ≤ centralizer (D : Set G) := le_centralizer_iff.mp
    (inf_le_right.trans (centralizer_le (show L ≤ K ⊔ L from le_sup_right)))
  have hKN : K ≤ normalizer (((U₁ ⊔ V₂) ⊔ D : Subgroup G) : Set G) := by
    have hnU : K ≤ normalizer (U₁ : Set G) := K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))
    have hc : ⁅K,V₂⁆ ≤ U₁ := (commutator_mono le_rfl hV₂).trans
      (h.core_commutator_le (c.R_normal hx) hnc)
    have hnUV : K ≤ normalizer ((U₁ ⊔ V₂ : Subgroup G) : Set G) :=
      normalizes_join_of_commutator K U₁ V₂ hnU hc
    exact (le_inf hnUV (hKD.trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hLN : L ≤ normalizer (((V₁ ⊔ U₂) ⊔ D : Subgroup G) : Set G) := by
    have hnU : L ≤ normalizer (U₂ : Set G) := L.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
    have hc : ⁅L,V₁⁆ ≤ U₂ := (commutator_mono le_rfl hV₁).trans
      (h'.core_commutator_le (c.R_normal hx) (RankOne.second_noncommuting hi₄))
    have hnUV : L ≤ normalizer ((V₁ ⊔ U₂ : Subgroup G) : Set G) :=
      (sup_comm U₂ V₁) ▸ normalizes_join_of_commutator L U₂ V₁ hnU hc
    exact (le_inf hnUV (hLD.trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rw [hf.2.2.2.2.2.2] at hA
  rcases Set.mem_insert_iff.mp hA with he | hA
  · exact (hAQ he).elim
  rcases Set.mem_insert_iff.mp hA with he | hA
  · exact (hAQx he).elim
  rcases Set.mem_insert_iff.mp hA with he | he
  · intro hm
    apply houtK
    apply le_trans (le_inf hKH _) hm
    rw [he]
    exact (le_inf (hKH.trans hnQ) hKN).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · have he := Set.mem_singleton_iff.mp he
    intro hm
    apply houtL
    apply le_trans (le_inf hLH _) hm
    rw [he]
    exact (le_inf (hLH.trans hnQ) hLN).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

end CFSG.Quasithin.Chapter2.DoubleA3

namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The relative normalizer of an adjacent elementary product escapes M.
One of the two original cubic blocks normalizes the mixed product. -/
theorem MinimalBlockSetup.paired_cubic_mixed_normalizer_escape
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (hL : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups
      ((d.S : Subgroup d.H).map d.H.subtype))
    (hiA : (twoCore d.H).relIndex A = 2) :
    ¬ d.H ⊓ normalizer ((twoCore d.H ⊔ A : Subgroup G) : Set G) ≤ M := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨L,c,F,F',hF,hF',h,h',hL',hKL,hjoin,hperm,ht,x,hx,hnc⟩ :=
    d.cubic_pair_configuration hG T hST.le hpair hL M₀ hSM hMT hi
  have ht' : ∃ t ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy t = L := by
    obtain ⟨t,ht,he⟩ := ht
    exact ⟨t,ht,he⟩
  have hcl := d.two_block_closures L hperm ht'
  have hfull := d.two_block_core_centralizer L h.short h'.short hKL hperm ht'
  rw [hcl.2] at hfull
  have houtL : ¬ L ≤ M := by
    intro hLM
    obtain ⟨t,ht,he⟩ := ht'
    have htM : t ∈ M := d.full_pair.1.1.2.1 ht
    apply d.outside
    intro k hk
    have hkL : t*k*t⁻¹ ∈ L := he ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hk
    have hh := M.mul_mem (M.mul_mem (M.inv_mem htM) (hLM hkL)) htM
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  exact DoubleA3.pair_mixed_escape c h h' hL hL' hKL hperm ht hfull hi x hx hnc
    d.outside houtL A hA hiA

/-- Source 2.4.27(1), with the C.6 mixed-normalizer alternative excluded
using the actual paired cubic blocks and the elementary-core theorem. -/
theorem MinimalBlockSetup.paired_cubic_sylow_index_two
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (hL : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) :
    ((d.S : Subgroup d.H).map d.H.subtype).relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) = elementaryAbelianMaxJ T := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let N₀ := (T : Subgroup G) ⊓ normalizer (S : Set G)
  have hg := d.cubic_pair_global_source hG T hST hpair hL
  have hf := d.cubic_pair_family_action hG T hST hpair hL
  have hQ := (d.core_source hG T hST).2.2
  have hN₀ : N₀ = (T : Subgroup G) := by
    rcases hg.2.2.2.2.2 with he | ⟨hn,he,A,hA,hiA,hcard⟩
    · exact he
    have hRN : R ≤ normalizer ((twoCore d.H ⊔ A : Subgroup G) : Set G) := by
      have hRS : R ≤ S := sSup_le (fun _ h => h.1)
      intro r hr
      have hfix := (hf.2 r (hST.le (hRS hr))).mpr hr
      exact normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hfix _ hQ,hfix _ hA⟩
    have hout := d.paired_cubic_mixed_normalizer_escape hG T hST hpair hL A hA hiA
    exact (Nat.not_lt_of_ge hcard
      (d.mixed_normalizer_card_lt hG T hM hTM hu hST hf.1 A hA hiA hRN hout)).elim
  refine ⟨?_,?_⟩
  · exact hN₀ ▸ hg.1
  · exact hg.2.2.1.symm.trans (congrArg elementaryAbelianMaxJ hN₀)

/-- The original paired cubic Sylow and Thompson geometry in 2.4.27–30.
The three indices, both starred selection and all outside core spans refer
to the original ambient Sylow subgroup. -/
theorem MinimalBlockSetup.paired_cubic_source_sylow_geometry
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (hL : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := elementaryAbelianMaxJ S
    S.relIndex (T : Subgroup G) = 2 ∧ R.relIndex S = 2 ∧
      R.relIndex (T : Subgroup G) = 4 ∧ ChapterB.baumann S = R ∧
      R = elementaryAbelianMaxJ T ∧ R ∈ beta M ∧
      d.H ∈ gammaMax (Chapter1.He G) M ∧
      elementaryAbelianMaxSubgroups S = elementaryAbelianMaxSubgroups T ∧
      ∀ x ∈ (T : Subgroup G), x ∉ S →
        R = twoCore d.H ⊔ (twoCore d.H).map (MulAut.conj x⁻¹).toMonoidHom := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  have hi := d.paired_cubic_sylow_index_two hG T hM hTM hu hST hpair hL
  have hf := d.cubic_pair_family_action hG T hST hpair hL
  have hg := d.cubic_pair_global_source hG T hST hpair hL
  have hRS : R ≤ S := sSup_le (fun _ h => h.1)
  have hRT : R.relIndex (T : Subgroup G) = 4 := by
    have hh := relIndex_mul_relIndex R S (T : Subgroup G) hRS hST.le
    rw [hi.1,hf.1] at hh
    exact hh.symm
  have hnormal : (S.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hi.1
  have hTN : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST.le).mp hnormal
  have hgamma : d.H ∈ gamma (Chapter1.He G) M :=
    d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)
  refine ⟨hi.1,hf.1,hRT,hg.2.1,hi.2,
    d.thompson_beta_of_index_two hG T hM hTM hu hST hf.1,
    (lemma_2_3_7_1 T hTM hu hgamma d.S hST.le hi.1).1,?_,?_⟩
  · rw [←maxFamily_thompson S,hi.2,maxFamily_thompson]
  · intro x hx hxS
    exact (hg.2.2.2.2.1 x ⟨hx,hTN hx⟩ hxS).1

end CFSG.Quasithin.Chapter2
