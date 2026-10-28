module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.JankoFourMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel

/-!
# Placing the original A₆ local section in a J₄ involution centralizer

The nontrivial two-core yields a common maximal two-local overgroup of the
original local component and its normalizing full Sylow. The actual J₄
normal-elementary catalogue then gives max1 or a nontrivial common invariant
elementary subgroup of order at most eight. The genuine max1 quotient M₂₄
excludes the first alternative by its full A₆ section theorem. An A₆
extension acts trivially on the small elementary subgroup, since every
nontrivial image still has order at least 360 while its automorphism group
has order at most 168. Thus the centralizer is even, and the original Sylow
fixes an involution in it.

The two actual involution classes place the same pair in the first
centralizer: the second centralizer lies in max1. All restrictions and
conjugations retain the full two-core quotient.
Source: Aschbacher–Smith A.3.12 and 8.2.13, pp.47–48,722–723;
GLS3 Table 5.3i and the imported native J₄ Sylow certificates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.JankoFour
open Janko4 Janko4.Cardinality Janko4.LocalStructure Janko4.OuterReduction.OddIndex
open FiveLocalFF.SolvableQuotients
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four
local notation "K" => localKernel matrixA_mul_self matrixB_pow_four

private theorem max1_not_section (S : Sylow 2 M) (B : Subgroup M)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup M) ≤ normalizer (B : Set M))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let q := (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
    (QuotientGroup.mk' K)
  have hq : Function.Surjective q :=
    (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).surjective.comp
      (QuotientGroup.mk'_surjective K)
  have hk : q.ker = K := by
    rw [MonoidHom.ker_comp_of_injective _ _
      (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).injective,
      QuotientGroup.ker_mk']
  have hp : IsPGroup 2 q.ker := by
    rw [hk]
    let := localKernel_elementary matrixA_mul_self matrixB_pow_four
    exact IsElementaryAbelian.isPGroup 2 K
  let : Group.IsNilpotent q.ker := hp.isNilpotent
  have hkb : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hp.comap_subtype
  let b := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hkb
  exact mathieu_not_six_section (S.mapSurjective hq) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    ((map_mono hn).trans (B.le_normalizer_map q)) (b.symm.trans eB)

private theorem not_pair_le_max1 (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hBM : B ≤ M) (hSM : (S : Subgroup Model) ≤ M) : False := by
  let d := subgroupOfEquivOfLe hBM
  apply max1_not_section (S.subtype hSM) (B.subgroupOf M)
    (local_restrict hl hBM) _
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eB)
  rw [←subgroupOf_normalizer_eq hBM]
  exact comap_mono hn

private theorem normal_le_core {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    [IsSimpleGroup (B ⧸ pCore 2 B)] (N : Subgroup B) [N.Normal] (hne : N ≠ ⊤) :
    N ≤ pCore 2 B := by
  let Q := pCore 2 B
  let q := QuotientGroup.mk' Q
  have hN : (N.map q).Normal :=
    (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective Q)
  rcases hN.eq_bot_or_eq_top with hz | ht
  · simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp hz
  · have hsur : Function.Surjective ((QuotientGroup.mk' N).comp Q.subtype) := by
      intro y
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N y
      obtain ⟨n,hn,he⟩ := mem_map.mp (show q x ∈ N.map q by rw [ht]; trivial)
      have hnx : n⁻¹*x ∈ Q := QuotientGroup.eq.mp he
      refine ⟨⟨n⁻¹*x,hnx⟩,?_⟩
      change QuotientGroup.mk' N (n⁻¹*x) = QuotientGroup.mk' N x
      have hn' : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_mul,map_inv,hn',inv_one,one_mul]
    have hp : IsPGroup 2 (B ⧸ N) := pCore_isPGroup.of_surjective _ hsur
    let : Group.IsNilpotent (B ⧸ N) := hp.isNilpotent
    let : Group.IsPerfect (B ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Nontrivial (B ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    exact (Group.IsPerfect.not_isSolvable (B ⧸ N) inferInstance).elim

private theorem small_action_trivial {B A : Type*} [Group B] [Finite B]
    [Group.IsPerfect B] [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hA : Nat.card A ≤ 8) (f : B →* MulAut A) : f = 1 := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  by_contra hf
  have hne : f.ker ≠ ⊤ := by
    intro ht
    apply hf
    apply MonoidHom.ext
    intro b
    exact MonoidHom.mem_ker.mp (ht ▸ mem_top b)
  have hk := normal_le_core f.ker hne
  let : Group.IsNilpotent f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact (pCore_isPGroup.to_le hk).isNilpotent
  let e := PerfectCoreTwoExtension.solvableKernelQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective
  have h360 : Nat.card (f.range ⧸ pCore 2 f.range) = 360 := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hle : 360 ≤ Nat.card (MulAut A) :=
    (Nat.le_of_dvd Nat.card_pos (h360 ▸ card_quotient_dvd_card (pCore 2 f.range))).trans
      (card_le_card_group f.range)
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by simpa [←hk] using hA)
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow A k hk] at hle
  interval_cases k <;> norm_num [Fin.prod_univ_succ] at hle

private def markedSylow : Sylow 2 Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

private theorem fixed_even_centralizer (B E : Subgroup Model)
    (hl : B ∈ localCComponents markedSylow)
    (hnB : twoSubgroup ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hES : E ≤ twoSubgroup) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E)
    (hBE : B ≤ normalizer (E : Set Model))
    (hSE : twoSubgroup ≤ normalizer (E : Set Model)) :
    2 ∣ Nat.card (centralizer (B : Set Model)) := by
  rcases FiveLocalFF.JankoFour.fixed_pair_minimal_alternative (B ⊔ twoSubgroup) E hES hne he
    le_sup_right (sup_le hBE hSE) with hmax | ⟨A,hA,hAE,heA,hcard,hHA⟩
  · exact (not_pair_le_max1 markedSylow B hl hnB eB
      (le_sup_left.trans hmax) (le_sup_right.trans hmax)).elim
  · let := heA
    let := local_perfect hl
    have hBA := le_sup_left.trans hHA
    let f := A.normalizerMonoidHom.comp (inclusion hBA)
    have hf : f = 1 := small_action_trivial eB hcard f
    have hBC : B ≤ centralizer (A : Set Model) := by
      intro b hb
      have hk : inclusion hBA ⟨b,hb⟩ ∈ A.normalizerMonoidHom.ker := by
        change f ⟨b,hb⟩ = 1
        rw [hf]
        rfl
      rwa [normalizerMonoidHom_ker] at hk
    have hAC : A ≤ centralizer (B : Set Model) := le_centralizer_iff.mp hBC
    have h2 : 2 ∣ Nat.card A := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
      have hn0 : n ≠ 0 := by
        intro hn0
        rw [hn0,pow_zero] at hn
        exact hA (A.eq_bot_of_card_eq hn)
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact h2.trans (card_dvd_of_le hAC)

private theorem even_centralizer (S : Sylow 2 Model) (B E : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hnB : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hES : E ≤ (S : Subgroup Model)) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E)
    (hBE : B ≤ normalizer (E : Set Model))
    (hSE : (S : Subgroup Model) ≤ normalizer (E : Set Model)) :
    2 ∣ Nat.card (centralizer (B : Set Model)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S markedSylow
  let f := MulAut.conj g
  have hS : (S : Subgroup Model).map f.toMonoidHom = twoSubgroup :=
    congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hnB).trans (B.le_normalizer_map f.toMonoidHom)
  have hSE' := (map_mono (f := f.toMonoidHom) hSE).trans (E.le_normalizer_map f.toMonoidHom)
  have hES' := map_mono (f := f.toMonoidHom) hES
  rw [hS] at hl' hn' hSE' hES'
  let b := f.subgroupMap B
  let := he
  have h := fixed_even_centralizer (B.map f.toMonoidHom) (E.map f.toMonoidHom)
    hl' hn' ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB) hES'
    (fun hz => hne ((map_eq_bot_iff_of_injective _ f.injective).mp hz))
    (IsElementaryAbelian.map f.toMonoidHom)
    ((map_mono (f := f.toMonoidHom) hBE).trans (E.le_normalizer_map f.toMonoidHom)) hSE'
  have hc : (centralizer (B : Set Model)).map f.toMonoidHom =
      centralizer (B.map f.toMonoidHom : Set Model) := by
    rw [map_centralizer_equiv]
    rfl
  rw [←hc,card_map_of_injective f.injective] at h
  exact h

/-- The original local A6 section and its full normalizing Sylow lie in an
actual involution centralizer. The initial nontrivial two-core suffices. -/
theorem involution_placement (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hc : pCore 2 B ≠ ⊥) :
    ∃ z : Model, orderOf z = 2 ∧ B ⊔ (S : Subgroup Model) ≤ centralizer ({z} : Set Model) := by
  obtain ⟨N,hN,hBN,hSN⟩ := exists_maximal_two_local S B hn hc
  obtain ⟨R,hR,hnR,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le S hN hSN
  let E := R.map (S : Subgroup Model).subtype
  have he : IsElementaryAbelian 2 E := by
    let := heR
    exact IsElementaryAbelian.map _
  have hne : E ≠ ⊥ := fun hz => hR ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz)
  exact exists_involution_centralizing_normalizing_two_group B (S : Subgroup Model) S.isPGroup'
    hn (even_centralizer S B E hl hn eB (map_subtype_le R) hne he (hNR ▸ hBN) (hNR ▸ hSN))

private theorem second_seed_conjugacy :
    IsConj (InvolutionCentralizers.Second.seed : Model) ((a*b*a*b*b)^5) := by
  obtain ⟨g,hg⟩ := Simplicity.Max1Fusion.seed_fuses_second matrixA_mul_self matrixB_pow_four
  have ha : Simplicity.a matrixA_mul_self = a := by apply toMatrix_injective; rfl
  have hb : Simplicity.b matrixB_pow_four = b := by apply toMatrix_injective; rfl
  rw [ha,hb] at hg
  have hw : Simplicity.word a b "ababb" = a*b*a*b*b := by simp [Simplicity.word,mul_assoc]
  rw [hw] at hg
  exact isConj_iff.mpr ⟨g,hg.symm⟩

private theorem centralizer_map_of_conj {x y : Model} (g : Model)
    (hg : g*x*g⁻¹=y) :
    (centralizer ({x} : Set Model)).map (MulAut.conj g).toMonoidHom =
      centralizer ({y} : Set Model) := by
  rw [map_centralizer_equiv,Set.image_singleton]
  exact congrArg (fun z => centralizer ({z} : Set Model)) hg

/-- Ambient conjugation places the same local subgroup and full Sylow in
the literal first involution centralizer; the second class lies in max1. -/
theorem first_centralizer_placement (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hc : pCore 2 B ≠ ⊥) :
    ∃ g : Model,
      B.map (MulAut.conj g).toMonoidHom ≤ InvolutionCentralizers.First.centralizer ∧
      (S : Subgroup Model).map (MulAut.conj g).toMonoidHom ≤
        InvolutionCentralizers.First.centralizer := by
  obtain ⟨z,hz,hpair⟩ := involution_placement S B hl hn eB hc
  rcases OuterReduction.involution_isConj_of_max1_odd_index
    OuterReduction.max1_odd_index_unconditional hz with h | h
  · obtain ⟨g,hg⟩ := isConj_iff.mp h.symm
    have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hpair
    rw [centralizer_map_of_conj g hg,Subgroup.map_sup] at hmap
    exact ⟨g,le_sup_left.trans hmap,le_sup_right.trans hmap⟩
  · obtain ⟨g,hg⟩ := isConj_iff.mp (second_seed_conjugacy.trans h).symm
    let f := MulAut.conj g
    have hmap := map_mono (f := f.toMonoidHom) hpair
    rw [centralizer_map_of_conj g hg,Subgroup.map_sup] at hmap
    let : Group.IsSolvable f.toMonoidHom.ker := by
      rw [f.toMonoidHom.ker_eq_bot f.injective]
      infer_instance
    let b := f.subgroupMap B
    exact (not_pair_le_max1 (S.mapSurjective f.surjective) (B.map f.toMonoidHom)
      (Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom)
      ((map_mono hn).trans (B.le_normalizer_map f.toMonoidHom))
      ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB)
      ((le_sup_left.trans hmap).trans InvolutionCentralizers.Second.ambient_le_max1)
      ((le_sup_right.trans hmap).trans InvolutionCentralizers.Second.ambient_le_max1)).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.JankoFour
