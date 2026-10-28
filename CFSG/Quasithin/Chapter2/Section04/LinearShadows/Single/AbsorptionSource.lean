module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DerivedSource
public import Theory.GroupTheory.ConjugateTorusCommutator
/-!
# Absorption of the two-core into the original natural block

The original joint Hall construction supplies D and Dˣ normalizing R,
with Dˣ also normalizing L. The derived-center calculation makes
[S∩L,Dˣ]=S∩L. Comparing conjugate orders gives [R,B]≤L. The already
proved C_R(B)=1 and coprime decomposition force R≤L, hence O₂(L)=Q=O₂(H).
The actual block core was previously identified with U, completing (2).

Source: Aschbacher–Smith, Lemma 2.4.8(2),(3),(5), printed pp.529–530.
-/
public section

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Subgroup
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_core_absorption
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    Stellmacher.elementaryAbelianMaxJ S ≤ L ∧ twoCore L = twoCore d.H := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let P := S ⊓ L
  obtain ⟨D,B,hDM,hDB,_hcyc,_hcard,hD,hodd,_hHall,_hTB,hBR,_hTBn,_hSn,hfrat,hfixed,
    _hcompl,x,hxT,hxS,hxB,hpair,hBD,_hBE,hEL⟩ :=
    source_fixed_free_torus d hG T hST hsingle hL hM hTM hunique
  let a := MulAut.conj x⁻¹
  let E := D.map a.toMonoidHom
  have hEB : E ≤ B := le_sup_right.trans_eq hpair.symm
  have hDR : D ≤ normalizer (R : Set G) := hDB.trans hBR
  have hER : E ≤ normalizer (R : Set G) := hEB.trans hBR
  have hDL : D ≤ L := hDM.trans inf_le_right
  have hDodd : Odd (Nat.card D) := Odd.of_dvd_nat hodd (card_dvd_of_le hDB)
  have hEodd : Odd (Nat.card E) := by
    change Odd (Nat.card (D.map a.toMonoidHom))
    rw [card_map_of_injective a.injective]
    exact hDodd
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hRtwo : IsPGroup 2 R := T.isPGroup'.to_le (hRS.trans hST.le)
  have hPtwo : IsPGroup 2 P := T.isPGroup'.to_le (inf_le_left.trans hST.le)
  have hcop : Nat.Coprime (Nat.card B) (Nat.card R) := by
    obtain ⟨k,hk⟩ := hRtwo.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hodd).pow_right k
  have hcopE : Nat.Coprime (Nat.card E) (Nat.card P) := by
    obtain ⟨k,hk⟩ := hPtwo.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hEodd).pow_right k
  have hd := source_thompson_decomposition d hG T hST hsingle hL
  change R = P ⊔ (S ⊓ centralizer (L : Set G)) ∧ R ⊓ L = P ∧
    S ⊓ centralizer (L : Set G) ≤ centralizer (R : Set G) at hd
  have hPR : P ≤ R := le_sup_left.trans_eq hd.1.symm
  have hDP : D ≤ normalizer (P : Set G) := by
    rw [←hd.2.1]
    exact (le_inf hDR (hDL.trans L.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hEP : E ≤ normalizer (P : Set G) := by
    rw [←hd.2.1]
    exact (le_inf hER hEL).trans inf_normalizer_le_normalizer_inf
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  have hRa : R.map a.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp
    (ht.2.2 (T.inv_mem hxT))
  have hcent : R ⊓ centralizer (R : Set G) ⊓ P ≤ ⁅P,P⁆ :=
    (le_inf inf_le_right ((inf_le_left.trans inf_le_right).trans (centralizer_le hPR))).trans
      (source_sylow_center_le_derived d hG T hST hsingle hL)
  have hRD := source_thompson_odd_commutator d hG T hST hsingle hL D hDL hDodd hD hDR
  have hDF : R ⊓ centralizer (D : Set G) ≤ centralizer (R : Set G) :=
    (source_odd_fixed_centralizes_block d hG T hST hsingle hL D hDL hDodd hD).trans
      (centralizer_le (show R ≤ L ⊔ R from le_sup_right))
  have hcomm : ⁅R,B⁆ ≤ L := by
    rw [hpair]
    exact (conjugate_torus_commutator_le R P D a hRa hPR hcent hRD hDF hEP hDP
      (@IsNilpotent.to_isSolvable P _ hPtwo.isNilpotent) hcopE).trans inf_le_right
  have hQ : twoCore d.H ≤ R := le_sSup (d.core_source hG T hST).2.2
  have hfixedL := (inf_le_inf_left R (centralizer_le hDB)).trans
    (source_odd_fixed_centralizes_block d hG T hST hsingle hL D hDL hDodd hD)
  exact core_absorption_of_torus_geometry d hsingle T hST.le R B hRS
    (hST.le.trans ht.2.2) (source_frattini_generation d T R B hST.le hRS hfrat)
    hfixedL hBR hcop hcomm hQ hxT hxS (ht.2.2 hxT) hxB

/-- Original 2.4.8(2), with the literal source module and both two-cores. -/
theorem lemma_2_4_8_2
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    twoCore (d.block.map d.H.subtype) = sourceModule (d.block.map d.H.subtype) ∧
      sourceModule (d.block.map d.H.subtype) = twoCore d.H := by
  have hc : twoCore (d.block.map d.H.subtype) = sourceModule (d.block.map d.H.subtype) :=
    congrArg (Subgroup.map (d.block.map d.H.subtype).subtype)
      (source_block_core_eq_module d hG T hST hsingle)
  exact ⟨hc,hc.symm.trans (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2⟩

/-- The actual source Sylow and maximum families after core absorption. -/
theorem source_absorbed_sylow_family
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let U := sourceModule L
    R = S ⊓ L ∧ ChapterB.baumann S = R ∧
      (∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = R) ∧
      ∀ x ∈ T, x ∉ S →
        R = U ⊔ U.map (MulAut.conj x⁻¹).toMonoidHom ∧
        Stellmacher.elementaryAbelianMaxSubgroups S = {U,U.map (MulAut.conj x⁻¹).toMonoidHom} ∧
        Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) =
          {U,U.map (MulAut.conj x⁻¹).toMonoidHom} := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  have ha := source_core_absorption d hG T hST hsingle hL hM hTM hunique
  have hRL : R = S ⊓ L := by
    have he : R ⊓ L = S ⊓ L := (source_thompson_decomposition d hG T hST hsingle hL).2.1
    rwa [inf_eq_left.mpr ha.1] at he
  let e := equivMapOfInjective d.block d.H.subtype d.H.subtype_injective
  have hK := hL.of_mulEquiv e
  have hg := d.single_natural_global_source hG T hST hsingle hK
  have hU := (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  obtain ⟨P₀,hP₀,_⟩ := source_intersection_borel d hsingle hL
  let P : Sylow 2 L := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup L).map L.subtype = R := by
    rw [hRL]
    change ((P₀ : Subgroup d.block).map e.toMonoidHom).map L.subtype = _
    rw [Subgroup.map_map]
    have hf : L.subtype.comp e.toMonoidHom = d.H.subtype.comp d.block.subtype := rfl
    rw [hf,←Subgroup.map_map,hP₀,map_inf _ _ _ d.H.subtype_injective]
  refine ⟨hRL,hg.2.2.1,⟨P,hP⟩,?_⟩
  intro x hx hxS
  simpa only [hU] using hg.2.2.2.2 x hx hxS

/-- Original 2.4.11(1): the full core normalizer is the block normalizer. -/
theorem lemma_2_4_11_1
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    normalizer (twoCore d.H : Set G) = normalizer (d.block.map d.H.subtype : Set G) := by
  have h3 : ¬ ChapterC.IsAlternatingBlock d.block 3 := by
    intro ha
    obtain ⟨e⟩ := ha.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable d.block := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    exact hL.not_solvable
  have hn := d.coreNormalizer_normalizes_L0_source_of_not_three hG T hM hTM hunique h3
  rw [hsingle] at hn
  exact coreNormalizer_eq_blockNormalizer d
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2 hn

end CFSG.Quasithin.Chapter2.LinearShadows.Single
