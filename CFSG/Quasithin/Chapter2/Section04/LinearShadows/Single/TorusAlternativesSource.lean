module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterTorusSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.HallSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModelSource.Geometry
/-!
# Both original torus alternatives in 2.4.8(6)

The Hall construction chooses actual D and B. If the block center is nontrivial,
the faithful action of Dˣ on it makes D∩Dˣ trivial, giving B=D×Dˣ.
If the block is centerless, D acts faithfully and regularly on Z(R)#,
and the abelian overgroup B has the same automorphism image.

The final wrapper constructs the tori and discharges every action premise.
Source: Aschbacher–Smith, Lemma 2.4.8(6), printed pp.529–531.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem lemma_2_4_8_6a_of_choice
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (D B : Subgroup G) [IsMulCommutative B] (x : G) (hxT : x ∈ T)
    (hDL : D ≤ d.block.map d.H.subtype) (hodd : Odd (Nat.card D))
    (hDcard : Nat.card D = 2^n-1)
    (hB : B = D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom)
    (hfix : Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (B : Set G) = ⊥)
    (hEL : D.map (MulAut.conj x⁻¹).toMonoidHom ≤ normalizer (d.block.map d.H.subtype : Set G))
    (hZ : center (d.block.map d.H.subtype) ≠ ⊥) :
    Disjoint D (D.map (MulAut.conj x⁻¹).toMonoidHom) ∧
      Nonempty (B ≃* D × D.map (MulAut.conj x⁻¹).toMonoidHom) := by
  let L := d.block.map d.H.subtype
  let Z := (center L).map L.subtype
  let E := D.map (MulAut.conj x⁻¹).toMonoidHom
  have hr := (source_center_torus_of_choice d hG T hST hsingle hL hM hTM hunique
    D B x hxT hDL hodd hDcard hB hfix hEL).resolve_left hZ
  have hZn : Z ≠ ⊥ := fun he => hZ
    ((map_injective L.subtype_injective) (he.trans (Subgroup.map_bot _).symm))
  refine torus_directProduct_of_free_centralized_subgroup B D E Z hB.symm ?_ hZn ?_
  · intro a ha
    apply mem_centralizer_iff.mpr
    rintro z ⟨l,hl,rfl⟩
    exact (congrArg Subtype.val (mem_center_iff.mp hl (⟨a,hDL ha⟩ : L))).symm
  · intro e he z hz hz1 hfixe
    have hz1' : (⟨z,hz⟩ : Z) ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
    obtain ⟨a,ha,hu⟩ := hr.2.2 ⟨z,hz⟩ hz1' ⟨z,hz⟩ hz1'
    have hone : ((1:E):G)*z*((1:E):G)⁻¹=z := by simp
    exact congrArg Subtype.val ((hu ⟨e,he⟩ hfixe).trans (hu 1 hone).symm)

/-- The original chosen Hall tori satisfy both alternatives of 2.4.8(6). -/
theorem lemma_2_4_8_6
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let Z := R ⊓ centralizer (R : Set G)
    ∃ D B : Subgroup G, ∃ hDB : D ≤ B,
      D ≤ M ⊓ L ∧ IsCyclic D ∧ Nat.card D = 2^n-1 ∧ IsMulCommutative B ∧ Odd (Nat.card B) ∧
      IsHallSubgroup OddHall.oddPrimes (B.subgroupOf ((T : Subgroup G) ⊔ D)) ∧
      (∃ x ∈ T, x ∉ S ∧ x ∈ normalizer (B : Set G)) ∧
      (∀ x ∈ T, x ∉ S → x ∈ normalizer (B : Set G) →
        B = D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom) ∧
      (center L ≠ ⊥ → ∀ x ∈ T, x ∉ S → x ∈ normalizer (B : Set G) →
        Disjoint D (D.map (MulAut.conj x⁻¹).toMonoidHom) ∧
        Nonempty (B ≃* D × D.map (MulAut.conj x⁻¹).toMonoidHom)) ∧
      (center L = ⊥ → ∃ hBZ : B ≤ normalizer (Z : Set G),
        let ρ : B →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hBZ)
        ρ.range = (ρ.comp (inclusion hDB)).range ∧
        Function.Injective (ρ.comp (inclusion hDB)) ∧ Nonempty (D ≃* ρ.range) ∧
        ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃! a : D, (a:G)*z*(a:G)⁻¹=w) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  obtain ⟨D,B,hDM,hDB,hcyc,hcard,_hD,hcomm,hodd,hHall,_hTB,_hprod,_hSn,hRn,_hRBn,
    hfixed,_hRTn,_hcompl,hout,hpair⟩ := lemma_2_4_8_5 d hG T hST hsingle hL hM hTM hunique
  let := hcomm
  have hDL : D ≤ L := hDM.trans inf_le_right
  have hBR : B ≤ normalizer (R : Set G) := le_sup_right.trans
    ((normal_subgroupOf_iff_le_normalizer (show R ≤ R ⊔ B from le_sup_left)).mp hRn)
  have hDo : Odd (Nat.card D) := Odd.of_dvd_nat hodd (card_dvd_of_le hDB)
  refine ⟨D,B,hDB,hDM,hcyc,hcard,hcomm,hodd,hHall,hout,hpair,?_,?_⟩
  · intro hZ x hxT hxS hxB
    exact lemma_2_4_8_6a_of_choice d hG T hST hsingle hL hM hTM hunique D B x hxT hDL hDo
      hcard (hpair x hxT hxS hxB) hfixed
      (source_conjugate_torus_normalizes_block d hG T hST hsingle hL hM hTM hunique
        D hDo (hDB.trans hBR) x hxT hxS).2.2 hZ
  · intro hZ
    exact lemma_2_4_8_6b_of_choice d hG T hST hsingle hL hM hTM hunique hZ D B hDL hDo hcard hDB hBR
end CFSG.Quasithin.Chapter2.LinearShadows.Single
