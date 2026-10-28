module
public import Theory.ElementaryAbelian.SingerNormalizer
public import Theory.GroupTheory.NormalizerAction
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.TorusAlternativesSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ElementarySource

/-!
# The center action in the single linear case

For a centerless block, the source torus acts regularly on the nonidentity
central elements of the Thompson subgroup. The actual torus-normalizer
supplement to the Sylow subgroup therefore places its center action in a binary
Singer normalizer. This proves that the action image, and hence the quotient by
the center centralizer, is cyclic. These are the literal ambient groups of
Aschbacher–Smith, Volume I, 2.4.17(2).
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_centerless_center_action_normalizer
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    ∃ hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G),
      IsElementaryAbelian 2 Z ∧ ∃ C : Subgroup (MulAut Z), IsCyclic C ∧
        (∀ v w : Z, v ≠ 1 → w ≠ 1 → ∃! a : C, a.val v = w) ∧
        (Z.normalizerMonoidHom.comp (inclusion hTZ)).range ≤ normalizer (C : Set _) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := R ⊓ centralizer (R : Set G)
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hRT := hRS.trans hST.le
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRT).mp c.normal_in_sylow
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) :=
    (le_inf hTR (hTR.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hBZ : c.hall ≤ normalizer (Z : Set G) :=
    (le_inf c.hall_normalizes (c.hall_normalizes.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hEA : IsElementaryAbelian 2 Z := by
    obtain ⟨x,hxT,hxS,_⟩ := c.outside
    have hh := lemma_2_4_8_3 d hG T hST hsingle hL hM hTM hunique
    have he := (hh.2.2.2 x hxT hxS).2.1
    let U := ChapterC.Section05.ConjugateSource.sourceModule (d.block.map d.H.subtype)
    have hU : IsElementaryAbelian 2 U := by
      let : IsElementaryAbelian 2 (twoCore d.H) := (d.core_source hG T hST).2.2.2.1
      exact IsElementaryAbelian.of_le
        (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2.le
    let := hU
    exact IsElementaryAbelian.of_le (he ▸ (show U ⊓ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ U from inf_le_left))
  let := hEA
  let := c.hall_abelian
  have ho : Odd (Nat.card c.torus) := c.hall_odd.of_dvd_nat (card_dvd_of_le c.torus_le_hall)
  obtain ⟨hBZ',hrange,hinj,hequiv,hreg⟩ := lemma_2_4_8_6b_of_choice d hG T hST hsingle hL
    hM hTM hunique hZ c.torus c.hall (c.torus_le.trans inf_le_right) ho c.torus_card
    c.torus_le_hall c.hall_normalizes
  let ρ := Z.normalizerMonoidHom
  let β := ρ.comp (inclusion hBZ)
  let α := ρ.comp (inclusion hTZ)
  let C := β.range
  let P := α.range
  let := c.torus_cyclic
  let : IsCyclic C := hequiv.some.isCyclic.mp inferInstance
  have hC : C = (c.hall.subgroupOf (normalizer (Z : Set G))).map ρ := by
    change (ρ.comp (inclusion hBZ)).range = _
    rw [MonoidHom.range_comp, inclusion_range]
  have hPn : P ≤ normalizer (C : Set (MulAut Z)) := by
    rintro a ⟨t,rfl⟩
    obtain ⟨⟨r,b⟩,ht⟩ := c.split_ambient.2 t
    have hr : α (r:T) = 1 := by
      ext z
      exact mul_inv_eq_iff_eq_mul.mpr (z.property.2 _ r.property)
    have hb : (⟨(b:T),hTZ (b:T).property⟩ : normalizer (Z : Set G)) ∈
        normalizer (c.hall.subgroupOf (normalizer (Z : Set G)) : Set _) := by
      rw [←subgroupOf_normalizer_eq hBZ]
      exact b.property
    have hb' : α (b:T) ∈ normalizer (C : Set (MulAut Z)) := by
      rw [hC]
      exact (c.hall.subgroupOf (normalizer (Z : Set G))).le_normalizer_map ρ
        (mem_map_of_mem ρ hb)
    rw [←ht,map_mul,hr,one_mul]
    exact hb'
  have hregular : ∀ v w : Z, v ≠ 1 → w ≠ 1 → ∃! a : C, a.val v = w := by
    intro v w hv hw
    obtain ⟨a,ha,hu⟩ := hreg v v.property (fun he => hv (Subtype.ext he))
      w w.property (fun he => hw (Subtype.ext he))
    let z : C := ⟨β (inclusion c.torus_le_hall a),⟨inclusion c.torus_le_hall a,rfl⟩⟩
    refine ⟨z,Subtype.ext ha,?_⟩
    intro b hb
    have hbD : b.val ∈ (β.comp (inclusion c.torus_le_hall)).range := hrange ▸ b.property
    obtain ⟨a',ha'⟩ := hbD
    have he : a'=a := hu a' (by
      have hc := congrArg Subtype.val hb
      rw [←ha'] at hc
      exact hc)
    exact Subtype.ext (ha'.symm.trans (congrArg (β.comp (inclusion c.torus_le_hall)) he))
  exact ⟨hTZ,hEA,C,inferInstance,hregular,hPn⟩

theorem source_centerless_center_action_cyclic
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    ∃ hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G),
      IsCyclic ((Z.normalizerMonoidHom.comp (inclusion hTZ)).range) := by
  obtain ⟨hTZ,hEA,C,hC,hreg,hn⟩ := source_centerless_center_action_normalizer
    d hG T hST hsingle hL hM hTM hunique c hZ
  let := hEA
  let := hC
  let α := (Stellmacher.elementaryAbelianMaxJ
      ((d.S : Subgroup d.H).map d.H.subtype) ⊓ centralizer
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)).normalizerMonoidHom.comp
    (inclusion hTZ)
  exact ⟨hTZ,regular_cyclic_automorphism_normalizer_two_subgroup C α.range hreg
    (T.isPGroup'.of_surjective α.rangeRestrict α.rangeRestrict_surjective) hn⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_centerless_center_quotient_cyclic
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    ∃ hN : ((centralizer (Z : Set G)).subgroupOf (T : Subgroup G)).Normal,
      letI := hN
      IsCyclic (T ⧸ (centralizer (Z : Set G)).subgroupOf (T : Subgroup G)) := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Z := R ⊓ centralizer (R : Set G)
  obtain ⟨hTZ,hcyc⟩ := source_centerless_center_action_cyclic d hG T hST hsingle hL
    hM hTM hunique c hZ
  let α := Z.normalizerMonoidHom.comp (inclusion hTZ)
  have hk : α.ker = (centralizer (Z : Set G)).subgroupOf (T : Subgroup G) := by
    change (Z.normalizerMonoidHom.comp (inclusion hTZ)).ker = _
    rw [←MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  let hN : ((centralizer (Z : Set G)).subgroupOf (T : Subgroup G)).Normal :=
    hk ▸ inferInstance
  refine ⟨hN,?_⟩
  let : IsCyclic α.range := hcyc
  exact ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange α)).isCyclic.mpr inferInstance
end CFSG.Quasithin.Chapter2.LinearShadows.Single
