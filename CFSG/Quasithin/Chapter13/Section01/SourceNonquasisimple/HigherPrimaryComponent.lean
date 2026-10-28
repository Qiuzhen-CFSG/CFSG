module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.RadicalCentralizationReduction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Normalization
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.OutsideSelection.Reduction

/-!
# The actual higher-primary escaping component

An active primary radical I_p at p>5 has an escaping maximal two-local H
by the original reduced-action and guarded cubic-bound argument. The complete
intrinsic embedding theorem applied to Ξ_p(L) inside this same H excludes
relative normality. Its noncyclic automizer leaves exactly a swapped rank-one
component or a T-invariant linear-three component.

The component lies outside N_G(L): otherwise its solvable intersection with
Ξ_p(L) would be central modulo O₂, contradicting the nontrivial odd plane
intersection. The global characteristic-two bridge supplies F*(K)=O₂(K).
The original Frattini factorization of T then proves normalization by both
O₂(Ξ_p(L)T) and the larger O₂(I_pT). In the swapped case, an element
centralizing the odd plane fixes K because distinct simple components commute.

The final theorem applies this construction to the literal failure of
O∞(L) centralizing [R₂(N_G(L)),L], retaining the actual higher homocyclic
quotient. No universal A.3.12 or C.2.7 premise is used. Characteristic-normalizer
control and the remaining model exclusion are still source obligations;
these theorems do not assert radical centralization or Theorem13.1.7.

Source: Aschbacher--Smith13.1.4(5), printed p.867;3.2.14, p.585;
1.3.4 and the component reduction in1.3.8, pp.509--514.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter1.XiEmbedding
open Chapter1.RadicalExclusions Chapter1.RadicalExclusions.ModelReduction Chapter12.Section02 ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

private structure RadicalComponentData (κ : GroupClass.{u}) (p : ℕ)
    (T X P M H₀ K : Subgroup G) : Prop where
  overgroup : H₀ ∈ HOver G (T : Set G)
  local_input : LocalInput p T X P H₀
  sylow_two : IsSylowIn 2 T H₀
  component : K ∈ cComponentsIn H₀
  quasisimple : IsQuasisimple (XiQuotient K)
  containment : X ≤ componentOrbit K T
  alternatives : SurvivingAlternatives p T P K

private theorem center_bot {D : Type*} [Group D] [Group.IsPerfect D]
    [IsSimpleGroup D] : center D = ⊥ := by
  rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with hz | hz
  · exact hz
  · exact (Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp hz)).elim

omit [Finite G] in
private theorem fixed_nonidentity_normalizes {K : Subgroup G}
    (hK : IsComponent G K) (hz : center K = ⊥) {x g : G}
    (hx : x ∈ K) (hne : x ≠ 1) (hg : Commute g x) : g ∈ normalizer K := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra he
  have hc := hK.commutator_eq_bot_of_ne (hK.map_conj g) (Ne.symm he)
  have hf : MulAut.conj g x = x := by
    change g * x * g⁻¹ = x
    rw [hg.eq]
    simp
  have hxg : x ∈ K.map (MulAut.conj g).toMonoidHom :=
    hf ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  have hxc : (⟨x, hx⟩ : K) ∈ center K := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (((commutator_eq_bot_iff_le_centralizer.mp hc) y.property) x hxg).symm
  have hxx : (⟨x, hx⟩ : K) = 1 := mem_bot.mp (hz ▸ hxc)
  exact hne (congrArg ((↑) : K → G) hxx)

private theorem centralizer_odd_le_normalizer {p : ℕ} [Fact p.Prime]
    {A K : Subgroup G} (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hs : IsSimpleGroup (K ⧸ pCore 2 K))
    (hp : Odd p) (hA : IsPGroup p A) (hne : A ≠ ⊥) (hAK : A ≤ K) :
    centralizer (A : Set G) ≤ normalizer K := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let e := cComponentTwoCoreQuotientEquiv hK
  let _ := hs
  let _ := hq
  have hB : IsComponent (G ⧸ pCore 2 G) B :=
    ⟨hK.subnormal.quotient, IsQuasisimple.of_mulEquiv e⟩
  let _ : IsSimpleGroup B := e.symm.isSimpleGroup
  let _ := hB.2
  have hAB : Disjoint A (pCore 2 G) :=
    hA.disjoint_of_coprime pCore_isPGroup (Nat.coprime_two_right.mpr hp)
  let _ : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hne
  obtain ⟨x, hx, hx1⟩ := A.exists_ne_one_of_nontrivial
  intro g hg
  rw [← normalizer_cComponent_quotient hK (pCore 2 G)]
  change q g ∈ normalizer B
  have hxq : q x ≠ 1 := by
    intro he
    have hxc : x ∈ pCore 2 G := (QuotientGroup.eq_one_iff x).mp he
    exact hx1 (hAB.le_bot ⟨hx, hxc⟩)
  exact fixed_nonidentity_normalizes hB (center_bot (D := B))
    (mem_map_of_mem q (hAK hx)) hxq
    ((show Commute g x from (mem_centralizer_iff.mp hg x hx).symm).map q)


private theorem simple_of_linear_model {Q : Type*} [Group Q]
    (hq : IsQuasisimple Q) {q : ℕ} (hm : ClassicalGroup.IsPSL Q 2 q) :
    IsSimpleGroup Q := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
  let _ := hq
  let _ : Group.IsPerfect PSL(2, F) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hs : IsSimpleGroup PSL(2, F) :=
    MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
      PSL2.Iwasawa inferInstance
  exact e.isSimpleGroup_congr.mpr hs

/-- Every rank-one quotient in the swapped alternative is simple.
Perfectness rules out the small nonsimple projective groups. -/
private theorem swappedModel_simple_local {Q : Type*} [Group Q] {p : ℕ}
    (hq : IsQuasisimple Q) (hm : SwappedModel p Q) : IsSimpleGroup Q := by
  rcases hm with ⟨n, _, _, hm⟩ | ⟨q, _, _, hm⟩
  · exact simple_of_linear_model hq hm
  · exact simple_of_linear_model hq hm

/-- Centralizing P fixes the selected swapped component, through its
nontrivial odd intersection and its actual simple core quotient. -/
private theorem RadicalComponentData.centralizer_normalizes_of_swapped
    {κ : GroupClass} {p : ℕ} {T X P M H₀ K : Subgroup G}
    (h : RadicalComponentData κ p T X P M H₀ K)
    (hswap : SwappedFactors T P K) (hm : SwappedModel p (XiQuotient K)) :
    H₀ ⊓ centralizer (P : Set G) ≤ normalizer K := by
  let _ : Fact p.Prime := ⟨h.local_input.prime⟩
  let A := (P ⊓ K).subgroupOf H₀
  let B := K.subgroupOf H₀
  have hAH : P ⊓ K ≤ H₀ := inf_le_right.trans h.component.1
  let e := (subgroupOfEquivOfLe h.component.1).symm
  let eqv := QuotientGroup.congr (pCore 2 K) (pCore 2 B) e (pCore_map_iso 2 e)
  let _ := h.quasisimple
  have hq : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eqv
  have hs : IsSimpleGroup (B ⧸ pCore 2 B) := eqv.isSimpleGroup_congr.mp
    (swappedModel_simple_local h.quasisimple hm)
  have ha : A ≠ ⊥ := by
    intro ha
    have hac : Nat.card A = 1 := by rw [ha]; exact Subgroup.card_bot
    have he := Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv
    have hc := swapped_intersection_card h.alternatives.1 hswap
    have hp := h.local_input.prime.one_lt
    change Nat.card A = Nat.card (P ⊓ K : Subgroup G) at he
    omega
  have hnorm := centralizer_odd_le_normalizer h.component.2 hq hs
    h.local_input.odd (h.local_input.odd_complement.isPGroup.to_le inf_le_left).comap_subtype
    ha (comap_mono inf_le_right)
  intro g hg
  have hc : (⟨g, hg.1⟩ : H₀) ∈ centralizer (A : Set H₀) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    exact Subtype.ext ((mem_centralizer_iff.mp hg.2) a ha.1)
  have hn := B.le_normalizer_map H₀.subtype (mem_map_of_mem H₀.subtype (hnorm hc))
  simpa only [B, map_subgroupOf_eq_of_le h.component.1, Subgroup.subtype_apply] using hn

private theorem RadicalComponentData.xi_normalizes {κ : GroupClass.{u}} {p : ℕ}
    {T X P M H₀ K : Subgroup G} (h : RadicalComponentData κ p T X P M H₀ K) :
    X ≤ normalizer K := by
  let D := (cComponentLayer H₀).map H₀.subtype
  let _ := cComponentLayer_characteristic (G := H₀)
  have hKD : K ≤ D := by
    simpa only [map_subgroupOf_eq_of_le h.component.1] using
      map_mono (f := H₀.subtype) (le_cComponentLayer h.component.2)
  have hTD : T ≤ normalizer (D : Set G) :=
    h.overgroup.2.trans (H₀.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H₀ (cComponentLayer H₀)))
  have hDN : D ≤ normalizer (K : Set G) := by
    have hh := (map_mono (f := H₀.subtype)
      (cComponentLayer_le_normalizer h.component.2)).trans
        ((K.subgroupOf H₀).le_normalizer_map H₀.subtype)
    simpa only [map_subgroupOf_eq_of_le h.component.1] using hh
  exact h.containment.trans
    ((iSup_conjugates_le_of_le_normalizer K T D hKD hTD).trans hDN)


private theorem RadicalComponentData.two_group_normalizes
    {κ : GroupClass.{u}} {p : ℕ} {T X P M H K R : Subgroup G}
    (h : RadicalComponentData κ p T X P M H K)
    (hR : IsPGroup 2 R) (hRT : R ≤ T) (hCR : X.pCoreIn 2 ≤ R)
    (hPR : P ≤ normalizer (R : Set G)) : R ≤ normalizer K := by
  let : Fact p.Prime := ⟨h.local_input.prime⟩
  rcases h.alternatives.2 with ⟨hs,hm⟩ | ⟨ht,_⟩
  swap
  · exact hRT.trans ht
  have hc := h.centralizer_normalizes_of_swapped hs hm
  have hRH : R ≤ H := hRT.trans h.overgroup.2
  have hdis : Disjoint R P := hR.disjoint_of_coprime
    h.local_input.odd_complement.isPGroup (Nat.coprime_two_left.mpr h.local_input.odd)
  have hcentral : R ⊓ normalizer P ≤ centralizer (P : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply hdis.le_bot.trans' (le_inf ?_ ?_)
    · exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hPR)
    · exact le_normalizer_iff_commutator_le_right.mp inf_le_right
  have hfactor : (X.pCoreIn 2 : Set G) *
      ((T ⊓ normalizer P : Subgroup G) : Set G) = T := by
    have hn : T ⊓ normalizer P ≤ normalizer (X.pCoreIn 2 : Set G) :=
      inf_le_left.trans (h.local_input.invariant.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn, ← h.local_input.normalizer_factor]
  intro r hr
  have hrT : r ∈ (T : Set G) := hRT hr
  rw [← hfactor] at hrT
  obtain ⟨c,hcX,s,hs,he⟩ := hrT
  have hsR : s ∈ R := by
    have hh := R.mul_mem (R.inv_mem (hCR hcX)) hr
    rwa [← he,inv_mul_cancel_left] at hh
  rw [← he]
  exact (normalizer (K : Set G)).mul_mem
    (h.xi_normalizes (pCoreIn_le 2 X hcX))
    (hc ⟨hRH hsR,hcentral ⟨hsR,hs.2⟩⟩)

private theorem solvable_normal_le_center {Q : Type*} [Group Q]
    [IsQuasisimple Q] (B : Subgroup Q) [B.Normal] [Group.IsSolvable B] :
    B ≤ center Q := by
  rcases IsQuasisimple.normal_le_center_or_eq_top B with hc | ht
  · exact hc
  · let _ : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
    let _ : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
    have hs : Group.IsSolvable Q := Group.isSolvable_of_surjective
      (f := B.subtype) (by rw [ht]; exact topEquiv.surjective)
    exact (Group.IsPerfect.not_isSolvable Q hs).elim

private theorem intersection_eq_bot {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {X P K : Subgroup G}
    [Group.IsSolvable X] (hPK : P ≤ X) (hpP : IsPGroup p P) (hp : Odd p)
    (hq : IsQuasisimple (XiQuotient K))
    (hcenter : ¬ p ∣ Nat.card (center (XiQuotient K)))
    (hKX : K ≤ normalizer X) : P ⊓ K = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := X.subgroupOf K
  let A := (P ⊓ K).subgroupOf K
  let _ := hq
  let _ : B.Normal := normal_subgroupOf_of_le_normalizer hKX
  let f : B →* X :=
    { toFun := fun b => ⟨b.val.val, b.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let _ : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := f) (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : X => (x : G)) hab)
  let _ : Group.IsSolvable (B.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective B)
  have hb : B.map q ≤ center (XiQuotient K) := solvable_normal_le_center (B.map q)
  have ha : A.map q ≤ center (XiQuotient K) := (map_mono (f := q)
    (comap_mono (inf_le_left.trans hPK))).trans hb
  have hpA : IsPGroup p A := (hpP.to_le inf_le_left).comap_subtype
  have hzero : A.map q = ⊥ := by
    rcases (hpA.map q).card_eq_or_dvd with hc | hd
    · exact Subgroup.card_eq_one.mp hc
    · exact (hcenter (hd.trans (card_dvd_of_le ha))).elim
  have hcore : A ≤ pCore 2 K := by
    simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hzero
  have hdis : Disjoint A (pCore 2 K) := hpA.disjoint_of_coprime pCore_isPGroup
    (Nat.coprime_two_right.mpr hp)
  have hA : A = ⊥ := le_bot_iff.mp (fun a ha => hdis.le_bot ⟨ha, hcore ha⟩)
  simpa only [A, map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_bot] using
    congrArg (map K.subtype) hA

/-- The actual escaping maximal overgroup contains a quasisimple component
outside N_G(L), with only the two surviving source models. The larger core
O₂(I_p T), not merely O₂(Ξ_p(L)T), normalizes this same component. -/
theorem active_large_primary_escaping_component
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp5 : 5 < p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hi : intrinsicSignalizerModule (Chapter3.RadicalCentralization.primaryRadical p L) ≠ ⊥)
    (P : Sylow p (XiP p L)) :
    let I := Chapter3.RadicalCentralization.primaryRadical p L
    let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
    ∃ H K : Subgroup G, IsMaximalTwoLocal H ∧ I ⊔ (T : Subgroup G) ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ K ∈ cComponentsIn H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ IsQuasisimple (XiQuotient K) ∧
      XiP p L ≤ componentOrbit K (T : Subgroup G) ∧
      LocalInput p T (XiP p L) P₀ H ∧
      SurvivingAlternatives p T P₀ K ∧ ¬ K ≤ normalizer (L : Set G) ∧
      generalizedFitting K = pCore 2 K ∧
      (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (K : Set G) ∧
      (I ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (K : Set G) := by
  let I := Chapter3.RadicalCentralization.primaryRadical p L
  let X := XiP p L
  let P₀ := (P : Subgroup X).map X.subtype
  obtain ⟨hshape,hNX,_⟩ :=
    RadicalConjugateRigidity.maximal_radical_structure h.simpleQTKE T hL hn ho hd
  have hXI : X ≤ I := Chapter3.RadicalCentralization.XiP_le_primaryRadical L hshape
  obtain ⟨H,hH,hIH,hout⟩ := active_large_primary_escaping_maximal h hmany hL hn ho hp5 hd hi
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hIH
  have hXH : X ⊔ (T : Subgroup G) ≤ H := (sup_le_sup_right hXI _).trans hIH
  have hSH : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  have hHOver : H ∈ HOver G (T : Set G) := ⟨mem_H_of_isTwoLocal hH.1,hTH⟩
  have hX : X ∈ Xi G (T : Subgroup G) :=
    (XiP_mem_XiPlus_source h.simpleQTKE T hL.1 hn ho hd).1
  have d : LocalInput p T X P₀ H := localInput_of_mem_Xi hX hSH hXH ho hshape P
  have hnotnormal : ¬ (X.subgroupOf H).Normal := by
    intro hnorm
    apply hout
    rw [← hNX]
    exact (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hXH)).mp hnorm
  obtain ⟨K,hK,hq,hXK,ha⟩ :=
    (d.adequate_knownSimple (h.simpleQTKE.twoLocal_sqtk hH.1) hSH).resolve_left hnotnormal
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hQ := uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.2.2
  have hnon := RadicalActions.XiP_automizer_not_isCyclic_of_A36 h36 hL.1 hQ hn ho hd P
  have hs : SurvivingAlternatives p T P₀ K := by
    rcases ha with ha | ha
    · exact surviving_alternatives (by omega) hnon ha
    · have hh := ha.1
      omega
  have hKL : K ∈ Chapter1.L G (T : Subgroup G) := (lemma_1_2_6 T hHOver).1 hK |>.2
  have c : RadicalComponentData KnownSimple.IsKnownSimple p T X P₀ (normalizer L) H K :=
    ⟨hHOver,d,hSH,hK,hq,hXK,hs⟩
  have hKout : ¬ K ≤ normalizer (L : Set G) := by
    intro hKM
    let C := radicalLocalImage (T : Subgroup G) K
    let e : XiQuotient K ≃* C := radicalLocalQuotientEquiv hKL
    let : IsQuasisimple C := hq.of_mulEquiv e
    have hc : A36Common C := (proposition_1_2_1_four_earlier_conclusion h36
      (uniqueness_local_quotient_sqtk h.simpleQTKE hKL.2.2) hKL.1).2
    have hz := center_card_of_quasisimple_A36Common hc
    have hpf : ¬ p ∣ Nat.card (center (XiQuotient K)) := by
      rw [Nat.card_congr (centerCongr e).toEquiv]
      rcases hz with hz | hz
      · rw [hz]; exact (Fact.out : p.Prime).not_dvd_one
      · rw [hz]
        intro hp
        have := Nat.le_of_dvd (by decide : 0 < 3) hp
        omega
    let : Group.IsSolvable X := hX.isSolvable
    have hzero : P₀ ⊓ K = ⊥ := intersection_eq_bot d.complement_le
      d.odd_complement.isPGroup ho hq hpf (hKM.trans hNX.ge)
    rcases hs.2 with ⟨hswap,_⟩ | ⟨hTK,_⟩
    · have hc := swapped_intersection_card hs.1 hswap
      rw [hzero,Subgroup.card_bot] at hc
      omega
    · have hXle : X ≤ K := hXK.trans
        (iSup_conjugates_le_of_le_normalizer K T K le_rfl hTK)
      have hPbot : P₀ = ⊥ :=
        (inf_eq_left.mpr (d.complement_le.trans hXle)).symm.trans hzero
      have hc : Nat.card P₀ = p^2 :=
        (Nat.card_congr hs.1.some.toEquiv).trans (plane_card p)
      rw [hPbot,Subgroup.card_bot] at hc
      nlinarith
  have hcore_norm (J : Subgroup G) (hXJ : X ≤ J) (hJL : J ≤ L) :
      (J ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (K : Set G) := by
    let U := J ⊔ (T : Subgroup G)
    apply c.two_group_normalizes (isPGroup_pCoreIn 2 U)
    · have hTU : (T : Subgroup G) ≤ U := le_sup_right
      have hh := pCoreIn_le_sylow U (T.subtype hTU)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTU] using hh
    · apply pCoreIn_mono_of_normalizes (hXJ.trans le_sup_left)
      exact sup_le (hJL.trans (L.le_normalizer.trans
        (normalizer_le_normalizer_XiP p L))) hX.invariant
    · exact (d.complement_le.trans (hXJ.trans le_sup_left)).trans
        (U.le_normalizer.trans (normalizer_le_normalizer_characteristic_image U (pCore 2 U)))
  exact ⟨H,K,hH,hIH,hout,hK,hKL,hq,hXK,d,hs,hKout,
    component_fitting_of_global_He (lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T))
      hHOver hK,hcore_norm X le_rfl (XiP_le p L),hcore_norm I hXI (map_subtype_le _)⟩

/-- The original failure of O∞(L) centralizing [R₂(N_G(L)),L] now has an
actual escaping component in its higher-primary branch. All source data for
the reduced embedding are constructed; no C.2.7 conclusion is assumed. -/
theorem radical_moved_action_component_obstruction
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (ha : ¬ (solvableRadical L).map L.subtype ≤
      centralizer (normalizerMoved L : Set G)) :
    (∃ K : Subgroup G, Hypothesis1221 KnownSimple.IsKnownSimple T K ∧
      ¬ (T : Subgroup G) ≤ normalizer (K : Set G)) ∨
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 5 < p ∧
      p ∣ Nat.card (fittingSubgroup (XiQuotient L)) ∧
      intrinsicSignalizerModule (Chapter3.RadicalCentralization.primaryRadical p L) ≠ ⊥ ∧
      ∃ a : ℕ, 2 ≤ a ∧
        Nonempty ((Chapter3.RadicalCentralization.primaryRadical p L ⧸
          pCore 2 (Chapter3.RadicalCentralization.primaryRadical p L)) ≃*
          Multiplicative (Fin 2 → ZMod (p^a))) ∧
        ∃ (P : Sylow p (XiP p L)) (H K : Subgroup G),
          IsMaximalTwoLocal H ∧
          Chapter3.RadicalCentralization.primaryRadical p L ⊔ (T : Subgroup G) ≤ H ∧
          ¬ H ≤ normalizer (L : Set G) ∧ K ∈ cComponentsIn H ∧
          K ∈ Chapter1.L G (T : Subgroup G) ∧ IsQuasisimple (XiQuotient K) ∧
          XiP p L ≤ componentOrbit K (T : Subgroup G) ∧
          LocalInput p T (XiP p L) ((P : Subgroup (XiP p L)).map (XiP p L).subtype) H ∧
          SurvivingAlternatives p T ((P : Subgroup (XiP p L)).map (XiP p L).subtype) K ∧
          ¬ K ≤ normalizer (L : Set G) ∧ generalizedFitting K = pCore 2 K ∧
          (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (K : Set G) ∧
          (Chapter3.RadicalCentralization.primaryRadical p L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
            normalizer (K : Set G) := by
  rcases radical_moved_action_obstruction h hmany hL hn ha with
    he | ⟨p,hp,ho,hp5,hd,hi,a,ha,e,_⟩
  · exact Or.inl he
  · let : Fact p.Prime := ⟨hp⟩
    let P : Sylow p (XiP p L) := default
    exact Or.inr ⟨p,hp,ho,hp5,hd,hi,a,ha,e,P,
      active_large_primary_escaping_component h hmany hL.1 hn ho hp5 hd hi P⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
