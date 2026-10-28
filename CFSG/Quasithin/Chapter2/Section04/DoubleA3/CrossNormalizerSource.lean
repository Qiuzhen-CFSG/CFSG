module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CoreFusion
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.PriorCaseReduction

/-!
# Reselecting the mixed elementary core in source 2.4.37

The first mixed member of the actual cubic four-family is normalized by an
original escaping A₄. The full Sylow group preserves the complementary pair,
so its normalizer intersection has index two. The original central Sylow
involution belongs to the mixed member, making its full normalizer an even
characteristic local subgroup. The Thompson beta base and half-Sylow order
put this normalizer in Γₑ₀ with the literal Sylow intersection.

The earlier block-case reduction then reselects a paired-cubic group while
preserving that Sylow subgroup. Normality of the mixed elementary subgroup
and maximal elementary abelianness identify it with the new two-core. The
last theorem applies the existing six-point core-fusion bound to this actual
reselected core and the original involution centralizer.

The earlier linear and A₅ exclusions remain the original prior-case inputs;
no paired-cubic exclusion or additional fusion classification is used.
Source: Aschbacher–Smith, 2.4.37, printed p.550.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private theorem join_normalized_of_commutator (K U V : Subgroup G)
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

omit [Finite G] in
/-- A normalizer of S preserves the complementary pair to its two invariant
maximum elementary subgroups. This is applied only to the actual cubic family. -/
private theorem cross_pair_preserved (S Q W A B : Subgroup G)
    (hf : elementaryAbelianMaxSubgroups S = {Q,W,A,B})
    (hi : {D ∈ elementaryAbelianMaxSubgroups S | S ≤ normalizer (D : Set G)} = {Q,W})
    (hAQ : A ≠ Q) (hAW : A ≠ W)
    (t : G) (ht : t ∈ normalizer (S : Set G)) :
    A.map (MulAut.conj t).toMonoidHom = A ∨ A.map (MulAut.conj t).toMonoidHom = B := by
  let e := MulAut.conj t
  have hA : A ∈ elementaryAbelianMaxSubgroups S := by rw [hf]; simp
  have hm := (maxFamily_map_injective_iff e.toMonoidHom e.injective S A).mpr hA
  have hS : S.map e.toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp ht
  rw [hS,hf] at hm
  have hback (C : Subgroup G) (hC : C = Q ∨ C = W) :
      C.map (MulAut.conj t⁻¹).toMonoidHom = Q ∨ C.map (MulAut.conj t⁻¹).toMonoidHom = W := by
    rcases hC with hC | hC
    · subst C
      exact Theory.GroupTheory.normalizer_preserves_invariant_maxFamily_pair S Q W hi
        ((normalizer (S:Set G)).inv_mem ht)
    · subst C
      exact (Theory.GroupTheory.normalizer_preserves_invariant_maxFamily_pair S W Q
        (hi.trans (Set.pair_comm _ _)) ((normalizer (S:Set G)).inv_mem ht)).symm
  have hnot (C : Subgroup G) (hC : C = Q ∨ C = W)
      (he : A.map e.toMonoidHom = C) : False := by
    have hh : A = C.map (MulAut.conj t⁻¹).toMonoidHom := by
      rw [←he,map_map]
      have hcomp : (MulAut.conj t⁻¹).toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
        ext a
        simp [e,MulAut.conj_apply,mul_assoc]
      rw [hcomp,map_id]
    exact (hback C hC).elim (fun h => hAQ (hh.trans h)) (fun h => hAW (hh.trans h))
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hm
  exact hm.elim (fun h => (hnot Q (Or.inl rfl) h).elim)
    (fun h => h.elim (fun h => (hnot W (Or.inr rfl) h).elim) id)

namespace SourcePairCoordinates
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} (c : SourcePairCoordinates d T)

/-- The literal first mixed elementary subgroup in the original four-family. -/
noncomputable abbrev cross : Subgroup G := (c.U₁ ⊔ c.V₂) ⊔ c.D

 theorem cross_normalizer_geometry :
    c.cross ∈ elementaryAbelianMaxSubgroups ((d.S : Subgroup d.H).map d.H.subtype) ∧
      sourceR d ≤ normalizer (c.cross : Set G) ∧
      d.block.map d.H.subtype ≤ normalizer (c.cross : Set G) ∧
      ((T : Subgroup G) ⊓ normalizer (c.cross : Set G) : Subgroup G).relIndex T = 2 := by
  classical
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  let Q := twoCore d.H
  let W := Q.map (MulAut.conj c.x⁻¹).toMonoidHom
  let B := (c.V₁ ⊔ c.U₂) ⊔ c.D
  have hf := ChapterC.Section06.rankOne_pair_family_from_original c.original c.first c.second
    c.commute c.pair ⟨⟨c.s,c.original.T_le c.s_mem⟩,c.s_mem,c.exchange⟩ c.core c.index c.x c.x_mem c.noncommuting
  have hfamily : elementaryAbelianMaxSubgroups S = {Q,W,c.cross,B} := c.four_family
  have hinv : {A ∈ elementaryAbelianMaxSubgroups S | S ≤ normalizer (A:Set G)} = {Q,W} := hf.2.2.2.2.2.1
  have hA : c.cross ∈ elementaryAbelianMaxSubgroups S := by rw [hfamily]; simp
  have hQ : Q ∈ elementaryAbelianMaxSubgroups S := by rw [hfamily]; simp
  have hW : W ∈ elementaryAbelianMaxSubgroups S := by rw [hfamily]; simp
  let : IsElementaryAbelian 2 Q := hQ.2.1
  let : IsElementaryAbelian 2 W := hW.2.1
  have hU₁Q : c.U₁ ≤ Q := by
    change c.U₁ ≤ twoCore d.H
    rw [c.product.1]
    exact le_sup_left.trans le_sup_left
  have hU₂Q : c.U₂ ≤ Q := by
    change c.U₂ ≤ twoCore d.H
    rw [c.product.1]
    exact le_sup_right.trans le_sup_left
  have hV₁W : c.V₁ ≤ W := map_mono hU₁Q
  have hAQ : c.cross ≠ Q := by
    intro he
    have hV₂Q : c.V₂ ≤ Q := he ▸ (le_sup_right.trans (show c.U₁ ⊔ c.V₂ ≤ c.cross from le_sup_left))
    exact RankOne.second_noncommuting c.orbit (hV₂Q.trans ((le_centralizer Q).trans (centralizer_le hU₂Q)))
  have hAW : c.cross ≠ W := by
    intro he
    have hU₁W : c.U₁ ≤ W := he ▸ (le_sup_left.trans (show c.U₁ ⊔ c.V₂ ≤ c.cross from le_sup_left))
    exact c.noncommuting (hV₁W.trans ((le_centralizer W).trans (centralizer_le hU₁W)))
  have hRN : sourceR d ≤ normalizer (c.cross:Set G) := by
    obtain ⟨P,P',hf',hg',hn⟩ := ChapterC.Section06.cubic_pair_geometry_from_original
      c.original c.first c.second c.cubic_first c.cubic_second c.commute c.pair
      ⟨⟨c.s,c.original.T_le c.s_mem⟩,c.s_mem,c.exchange⟩ c.core c.index c.x c.x_mem c.noncommuting
    rw [c.baumann] at hn
    exact hn c.cross hA
  have hcross := FourModuleOrbit.cross_commutators c.orbit.toInputs
  have hV₂ : c.V₂ ≤ RankOne.Q S K := by
    rw [c.first.core]
    exact le_inf (c.second.conjugate_le (c.original.R_normal c.x_mem))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross.2.1))
  have hKD : K ≤ centralizer (c.D : Set G) := le_centralizer_iff.mp
    (inf_le_right.trans (centralizer_le (show K ≤ K ⊔ c.L from le_sup_left)))
  have hKN : K ≤ normalizer (c.cross:Set G) := by
    have hnU : K ≤ normalizer (c.U₁:Set G) := K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))
    have hc : ⁅K,c.V₂⁆ ≤ c.U₁ := (commutator_mono le_rfl hV₂).trans
      (c.first.core_commutator_le (c.original.R_normal c.x_mem) c.noncommuting)
    exact (le_inf (join_normalized_of_commutator K c.U₁ c.V₂ hnU hc)
      (hKD.trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hmove : ∃ s ∈ S, s ∉ normalizer (c.cross:Set G) := by
    by_contra! hh
    have hm : c.cross ∈ {A ∈ elementaryAbelianMaxSubgroups S | S ≤ normalizer (A:Set G)} := ⟨hA,hh⟩
    rw [hinv] at hm
    exact (Set.mem_insert_iff.mp hm).elim hAQ (fun h => hAW (Set.mem_singleton_iff.mp h))
  obtain ⟨s,hs,hsn⟩ := hmove
  have hi := normalizer_relIndex_eq_two_of_pair (T : Subgroup G) c.cross B
    (fun t ht => cross_pair_preserved S Q W c.cross B hfamily hinv hAQ hAW t (c.original.R_normal ht))
    s (c.original.T_le hs) (fun he => hsn (mem_normalizer_iff_map_conj_eq.mpr he))
  exact ⟨hA,hRN,hKN,by simpa only [inf_relIndex_left] using hi⟩

end SourcePairCoordinates
namespace SourceCentralizerGeometry
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)

include g

/-- The actual mixed maximum elementary subgroup has an even-characteristic
normalizer in Γ₀, with its literal ambient Sylow intersection of index two. -/
theorem cross_normalizer_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block) :
    normalizer (c.cross : Set G) ∈ gammaEvenZero (Chapter1.He G) M ∧
      ∃ P : Sylow 2 (normalizer (c.cross:Set G)),
        (P : Subgroup _).map (normalizer (c.cross:Set G)).subtype =
          (T : Subgroup G) ⊓ normalizer (c.cross:Set G) ∧
        ((P : Subgroup _).map (normalizer (c.cross:Set G)).subtype).relIndex T = 2 ∧
        ((P : Subgroup _).map (normalizer (c.cross:Set G)).subtype,
          normalizer (c.cross:Set G)) ∈ localPairsIn (Chapter1.He G) M
            (normalizer (c.cross:Set G)) ∧
        (P : Subgroup _).map (normalizer (c.cross:Set G)).subtype < (T : Subgroup G) := by
  let A := c.cross
  let N := normalizer (A:Set G)
  let J := d.H ⊓ N
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := sourceR d
  let P₀ := (T : Subgroup G) ⊓ N
  obtain ⟨hA,hRN,hKN,hidx⟩ := c.cross_normalizer_geometry
  let : IsElementaryAbelian 2 A := hA.2.1
  have hAp : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  have hAT : A ≤ (T : Subgroup G) := hA.1.trans hST.le
  have hAH : A ≤ d.H := hA.1.trans (map_subtype_le _)
  have hz₂V : g.z₂ ∈ c.V₂ := by
    have hh : g.z₂ ∈ c.U₂ ⊓ centralizer (sourceR d:Set G) := ⟨g.second_mem,g.second_fixed⟩
    rw [c.second_fixed_line.2.1] at hh
    exact hh.2
  have hzA : g.z₁*g.z₂ ∈ A := (A).mul_mem
    (mem_sup_left (mem_sup_left g.first_mem)) (mem_sup_left (mem_sup_right hz₂V))
  have hz1 : g.z₁*g.z₂ ≠ 1 := by
    intro he
    have hh := g.product_order
    rw [he,orderOf_one] at hh
    omega
  have hAne : A ≠ ⊥ := fun he => hz1 (show g.z₁*g.z₂ ∈ (⊥:Subgroup G) from he ▸ hzA)
  have hzZ : g.z₁*g.z₂ ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype := by
    refine ⟨⟨g.z₁*g.z₂,hAT hzA⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro t
    exact Subtype.ext (g.product_centralizes_sylow t t.property)
  have hNe : N ∈ Chapter1.He G := (Chapter1.lemma_1_1_4_3 T (hG.evenCharacteristic T)
    hAne hAp (by intro he; exact hz1 (show g.z₁*g.z₂ ∈ (⊥:Subgroup G) from he ▸ ⟨hzZ,hzA⟩))).2.2
  have hJe : J ∈ Chapter1.He G := Chapter1.normalizer_mem_He_of_isPGroup
    d.mem_gammaEvenZero.2 hAp hAH
  have hAJ : A ≤ J := le_inf hAH A.le_normalizer
  have hQJ : A ≤ twoCore J := le_pCoreIn_of_normalizes hAp hAJ inf_le_right
  have hQN : A ≤ twoCore N := le_pCoreIn_of_normalizes hAp A.le_normalizer le_rfl
  have hJN : J ≤ N := inf_le_right
  have hJout : ¬ J ≤ M := fun hm => d.outside ((le_inf (map_subtype_le _) hKN).trans hm)
  have hgeo := d.paired_cubic_source_sylow_geometry hG T hM hTM hu hST hpair c.cubic_first
  have hRb : R ∈ beta M := hgeo.2.2.2.2.2.1
  have hHmax : d.H ∈ gammaMax (Chapter1.He G) M := hgeo.2.2.2.2.2.2.1
  have hRS : R ≤ S := sSup_le (fun _ h => h.1)
  have hRJ : R ≤ J := le_inf (hRS.trans (map_subtype_le _)) hRN
  have hNcore : twoCore N ≠ ⊥ := fun he => hAne (bot_unique (he ▸ hQN))
  have hNg : N ∈ gamma (Chapter1.He G) M :=
    ⟨hNcore,(R,J),⟨hRb,hJe,fun he => hAne (bot_unique (he ▸ hQJ)),hRJ,hJout⟩,hJN⟩
  have hRP : R ≤ P₀ := le_inf (hRS.trans hST.le) hRN
  have hPb : P₀ ∈ beta M := beta_mono hRb hRP (T.isPGroup'.to_le inf_le_left)
  have hcard : Nat.card P₀ = Nat.card S := by
    have hp := relIndex_mul_relIndex (⊥:Subgroup G) P₀ (T:Subgroup G) bot_le inf_le_left
    have hs := relIndex_mul_relIndex (⊥:Subgroup G) S (T:Subgroup G) bot_le hST.le
    rw [relIndex_bot_left,relIndex_bot_left,hidx] at hp
    rw [relIndex_bot_left,relIndex_bot_left,c.index] at hs
    omega
  have hmax := gammaMax_of_twoPart_le hHmax hNg (by
    rw [←sylow_image_card d.H d.S,←hcard]
    exact beta_card_le_twoPart hPb inf_le_right)
  obtain ⟨P,hP⟩ := exists_sylow_of_card (show P₀ ≤ N from inf_le_right)
    (hcard.trans ((sylow_image_card d.H d.S).trans hmax.2.symm))
  refine ⟨⟨Or.inr hmax.1,hNe⟩,P,hP,hP.symm ▸ hidx,?_,?_⟩
  · exact ⟨⟨hP.symm ▸ hPb,hNe,hNcore,map_subtype_le _,gamma_not_le hNg⟩,le_rfl⟩
  · rw [hP]
    apply lt_of_le_of_ne inf_le_left
    intro he
    rw [he,relIndex_self] at hidx
    omega

end SourceCentralizerGeometry

 theorem exists_paired_cubic_setup_with_normalized_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n → False)
    (hfive : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups T)
    (hN : normalizer (A : Set G) ∈ gammaEvenZero (Chapter1.He G) M)
    (S : Sylow 2 (normalizer (A : Set G)))
    (hpair : ((S : Subgroup _).map (normalizer (A : Set G)).subtype,normalizer (A : Set G)) ∈
      localPairsIn (Chapter1.He G) M (normalizer (A : Set G)))
    (hST : (S : Subgroup _).map (normalizer (A : Set G)).subtype < (T : Subgroup G))
:
    ∃ d : MinimalBlockSetup M, d.H ≤ normalizer (A:Set G) ∧
      (d.S : Subgroup d.H).map d.H.subtype = (S : Subgroup _).map (normalizer (A:Set G)).subtype ∧
      d.L0 ≠ d.block ∧ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3 ∧
      twoCore d.H = A := by
  have hAp : IsPGroup 2 A := by let := hA.2.1; exact IsElementaryAbelian.isPGroup 2 A
  have hAN : A ≤ (normalizer (A : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hAp A.le_normalizer le_rfl
  have hAS : A ≤ (S : Subgroup _).map (normalizer (A : Set G)).subtype :=
    hAN.trans (pCoreIn_le_sylow _ S)
  obtain ⟨d,hd,he,hdpair,hdcubic⟩ := exists_paired_cubic_setup_of_prior_cases
    hG T hM hTM hu hdelta hcounter hlinear hfive hN S hpair hST
  have hdt : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) := he ▸ hST
  have hAd : A ≤ d.H := hAS.trans (he ▸ (map_subtype_le _))
  have hAQ : A ≤ twoCore d.H := le_pCoreIn_of_normalizes hAp hAd hd
  have hQe : IsElementaryAbelian 2 (twoCore d.H) := (d.core_source hG T hdt).2.2.2.1
  have hQT : twoCore d.H ≤ (T : Subgroup G) := (pCoreIn_le_sylow d.H d.S).trans hdt.le
  have hQeq : twoCore d.H = A := (eq_of_le_of_card_ge hAQ (hA.2.2 _ hQT hQe)).symm
  exact ⟨d,hd,he,hdpair,hdcubic,hQeq⟩

 theorem maximum_elementary_fusion_bound_of_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n → False)
    (hfive : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups T) (hAcard : Nat.card A = 16)
    (hN : normalizer (A : Set G) ∈ gammaEvenZero (Chapter1.He G) M)
    (S : Sylow 2 (normalizer (A : Set G)))
    (hpair : ((S : Subgroup _).map (normalizer (A : Set G)).subtype,normalizer (A : Set G)) ∈
      localPairsIn (Chapter1.He G) M (normalizer (A : Set G)))
    (hST : (S : Subgroup _).map (normalizer (A : Set G)).subtype < (T : Subgroup G))
    (i : G) (hi : i ≠ 1) (P : Sylow 2 (centralizer ({i} : Set G)))
    (hPT : (P : Subgroup _).map (centralizer ({i} : Set G)).subtype ≤ (T : Subgroup G))
    (hindex : ((P : Subgroup _).map (centralizer ({i} : Set G)).subtype).relIndex
      (T : Subgroup G) = 2) : Nat.card {a : A // IsConj i (a : G)} ≤ 6 := by
  obtain ⟨d,hd,he,hdpair,hdcubic,hQeq⟩ := exists_paired_cubic_setup_with_normalized_core
    hG T hM hTM hu hdelta hcounter hlinear hfive A hA hN S hpair hST
  have hdt : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) := he ▸ hST
  obtain ⟨c⟩ := d.paired_cubic_coordinates hG T hM hTM hu hdt hdpair hdcubic
  obtain ⟨g⟩ := c.exists_centralizer_geometry hG hM hTM hu hdt hdpair
  have hh := g.core_fusion_bound_of_half_sylow_centralizer (hQeq ▸ hAcard) i hi P hPT hindex
  subst A
  exact hh

/-- The first mixed member has the actual six-point bound after source36.
Its normalizer and the new paired-cubic core are reconstructed from the
original hypotheses; no normalizer or fusion-classification input remains. -/
theorem SourceCentralizerGeometry.cross_fusion_bound
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n → False)
    (hfive : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block) (hR64 : Nat.card (sourceR d) = 64) :
    Nat.card {a : c.cross // IsConj g.z₂ (a:G)} ≤ 6 := by
  have hgeo := d.paired_cubic_source_sylow_geometry hG T hM hTM hu hST hpair c.cubic_first
  have hA := c.cross_normalizer_geometry.1
  have hAT : c.cross ∈ elementaryAbelianMaxSubgroups T := hgeo.2.2.2.2.2.2.2.1 ▸ hA
  have hQ : twoCore d.H ∈ elementaryAbelianMaxSubgroups ((d.S : Subgroup d.H).map d.H.subtype) := by
    rw [c.four_family]
    simp
  have hD : Nat.card c.D = 1 := by
    have hh := c.thompson_card
    rw [hR64] at hh
    omega
  have hQcard : Nat.card (twoCore d.H) = 16 := by
    rw [c.core_card,hD,one_mul]
  have hAcard : Nat.card c.cross = 16 :=
    (le_antisymm (hQ.2.2 _ hA.1 hA.2.1) (hA.2.2 _ hQ.1 hQ.2.1)).trans hQcard
  obtain ⟨hN,P,hP,hi,hfull,hPT⟩ := g.cross_normalizer_source hG hM hTM hu hST hpair
  apply maximum_elementary_fusion_bound_of_normalizer hG T hM hTM hu hdelta hcounter
    hlinear hfive c.cross hAT hAcard hN P hfull hPT g.z₂ _ g.P₂
    (g.second_intersection ▸ inf_le_left) g.second_sylow_index
  intro he
  have hh := g.order_second
  rw [he,orderOf_one] at hh
  omega

end CFSG.Quasithin.Chapter2.DoubleA3
