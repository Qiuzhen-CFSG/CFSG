module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.SylowSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverBounds
public import Theory.GroupTheory.ConjugateTorusFixed
public import Theory.GroupAction.RegularComplementBound
public import Theory.GroupTheory.GaschutzElementaryPair
/-!
# The original center and splitting in 2.4.8(4)

The natural-cover bound gives |Z(L)|≤q. Every nonidentity element of Dˣ
acts freely on Z(L), since conjugating a fixed point back puts it in
C_R(D₀)≤Z(L) for a nontrivial cyclic D₀≤D. It then centralizes both
tori, contradicting C_R(B)=1. Counting gives a trivial center or a
regular orbit of size q−1. The elementary pair U,Uˣ splits the actual
Sylow subgroup over U; Gaschütz splits L over its original two-core.
Source: Aschbacher–Smith, Lemma 2.4.8(4), printed p.530.
-/
public section
open scoped IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]

lemma source_nontrivial_odd_element_fixed
    {M : Subgroup G} (d : MinimalBlockSetup M)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (D : Subgroup G) (hDL : D ≤ d.block.map d.H.subtype) (hodd : Odd (Nat.card D)) :
    ∀ a ∈ D, a ≠ 1 →
      ∀ r ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype),
      Commute a r → r ∈ centralizer (d.block.map d.H.subtype : Set G) := by
  intro a ha ha1 r hr har
  have heD : zpowers a ≤ D := zpowers_le.mpr ha
  have hne : zpowers a ≠ ⊥ := by
    intro he
    exact ha1 (mem_bot.mp (he ▸ mem_zpowers a))
  have hrc : r ∈ centralizer (zpowers a : Set G) := by
    apply mem_centralizer_iff.mpr
    rintro b ⟨k,rfl⟩
    exact (har.zpow_left k).eq
  exact centralizer_le (show d.block.map d.H.subtype ≤ d.block.map d.H.subtype ⊔ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) from le_sup_left)
    (source_odd_fixed_centralizes_block d hG T hST hsingle hL (zpowers a)
      (heD.trans hDL) (Odd.of_dvd_nat hodd (card_dvd_of_le heD)) hne ⟨hr,hrc⟩)
lemma source_center_torus_of_choice
    {M : Subgroup G} (d : MinimalBlockSetup M)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (D B : Subgroup G) (x : G) (hxT : x ∈ T)
    (hDL : D ≤ d.block.map d.H.subtype) (hodd : Odd (Nat.card D))
    (hDcard : Nat.card D = 2^n-1)
    (hB : B = D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom)
    (hfix : Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (B : Set G) = ⊥)
    (hEL : D.map (MulAut.conj x⁻¹).toMonoidHom ≤
      normalizer (d.block.map d.H.subtype : Set G)) :
    let L := d.block.map d.H.subtype
    let Z := (center L).map L.subtype
    let E := D.map (MulAut.conj x⁻¹).toMonoidHom
    center L = ⊥ ∨
      Nat.card (center L) = 2^n ∧ E ≤ normalizer (Z : Set G) ∧
      ∀ z : Z, z ≠ 1 → ∀ w : Z, w ≠ 1 →
        ∃! a : E, (a:G)*(z:G)*(a:G)⁻¹ = (w:G) := by
  let L := d.block.map d.H.subtype
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := (center L).map L.subtype
  let E := D.map (MulAut.conj x⁻¹).toMonoidHom
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hcore := source_block_core_eq_module d hG T hST hsingle
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  obtain ⟨P,hP⟩ := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.1
  have hZR : Z ≤ R := by
    change (center L).map L.subtype ≤ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    rw [←hP]
    apply map_mono
    exact (hK.center_le_module hcore).trans
      (hcore ▸ (pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal P)
  have heZ : E ≤ normalizer (Z : Set G) :=
    hEL.trans (normalizer_le_normalizer_characteristic_image L (center L))
  have hfree0 := conjugate_torus_free_on_center L R D B x (ht.2.2 hxT) hZR hDL hB hfix
    (source_nontrivial_odd_element_fixed d hG T hST hsingle hL D hDL hodd)
  let act : E →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion heZ)
  let : MulDistribMulAction E Z := MulDistribMulAction.compHom Z act
  have hfree (a : E) (z : Z) (hz : z ≠ 1) (he : a • z = z) : a = 1 := by
    by_contra ha
    have ha1 : (a:G) ≠ 1 := fun he => ha (Subtype.ext he)
    have he' : (a:G)*(z:G)*(a:G)⁻¹ = (z:G) := congrArg Subtype.val he
    have hc : Commute (a:G) (z:G) := mul_inv_eq_iff_eq_mul.mp he'
    exact hz (Subtype.ext (hfree0 a a.property ha1 z z.property hc))
  have hcardZ : Nat.card Z = Nat.card (center L) := card_map_of_injective L.subtype_injective
  have hcardE : Nat.card E = 2^n-1 :=
    (card_map_of_injective (MulAut.conj x⁻¹).injective).trans hDcard
  have hbound : Nat.card Z ≤ Nat.card E + 1 := by
    rw [hcardZ,hcardE]
    have hb : Nat.card (center L) ≤ 2^n := hK.center_card_le hcore
    have hp : 0 < 2^n := pow_pos (by decide) _
    omega
  change center L = ⊥ ∨ _
  by_cases hz : center L = ⊥
  · exact Or.inl hz
  · have hzZ : Z ≠ ⊥ := by
      intro he
      exact hz ((map_injective L.subtype_injective) (he.trans (Subgroup.map_bot _).symm))
    have hcard := MulAction.card_eq_of_free_complement_of_le (1 : Z) (fun _ => smul_one _)
      hfree hbound (ne_bot_iff_exists_ne_one.mp hzZ)
    have hcenter : Nat.card (center L) = 2^n := by
      rw [hcardZ,hcardE] at hcard
      have hp : 0 < 2^n := pow_pos (by decide) _
      omega
    refine Or.inr ⟨hcenter,heZ,?_⟩
    intro z hz w hw
    obtain ⟨a,ha,hu⟩ := MulAction.existsUnique_smul_eq_of_free_complement
      (1 : Z) (fun _ => smul_one _) hfree hcard hz hw
    refine ⟨a,congrArg Subtype.val ha,?_⟩
    intro b hb
    exact hu b (Subtype.ext hb)

lemma source_core_splits_of_outside {M : Subgroup G}
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let L := d.block.map d.H.subtype
    ∃ K : Subgroup L, (pCore 2 L).IsComplement' K := by
  let L := d.block.map d.H.subtype
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule L
  let A := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hcore := source_block_core_eq_module d hG T hST hsingle
  let : IsElementaryAbelian 2 (pCore 2 L) := hcore.symm ▸ hK.2.1.elementary
  let : IsElementaryAbelian 2 U := by
    change IsElementaryAbelian 2 ((ChapterC.blockU L).map L.subtype)
    let := hK.2.1.elementary
    exact IsElementaryAbelian.map L.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hf := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  obtain ⟨P,hP⟩ := hf.2.2.1
  have hpair : U ⊔ A = R := (hf.2.2.2 x hxT hxS).1.symm
  have hRL : R ≤ L := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1
  let : IsElementaryAbelian 2 (A.subgroupOf L) :=
    IsElementaryAbelian.subgroupOf ((le_sup_right.trans_eq hpair).trans hRL)
  apply exists_complement_of_sylow_elementary (pCore 2 L) pCore_isPGroup P (A.subgroupOf L)
  apply map_injective L.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le ((le_sup_right.trans_eq hpair).trans hRL), hP, hcore]
  exact hpair


/-- The original source constructs the regular conjugate torus and a complement
of O₂(L), without any recognition or torus-action premise. -/
theorem source_center_torus_and_splitting
    {M : Subgroup G} (d : MinimalBlockSetup M)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let L := d.block.map d.H.subtype
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let Z := (center L).map L.subtype
    (∃ K : Subgroup L, (pCore 2 L).IsComplement' K) ∧
      ∃ D : Subgroup G, D ≤ M ⊓ L ∧ IsCyclic D ∧ Nat.card D = 2^n-1 ∧
      ∃ x ∈ T, x ∉ S ∧
      let E := D.map (MulAut.conj x⁻¹).toMonoidHom
      E ≤ normalizer (L : Set G) ∧
      (center L = ⊥ ∨ Nat.card (center L) = 2^n ∧ E ≤ normalizer (Z : Set G) ∧
        ∀ z : Z, z ≠ 1 → ∀ w : Z, w ≠ 1 →
          ∃! a : E, (a:G)*(z:G)*(a:G)⁻¹ = (w:G)) := by
  obtain ⟨D,B,hDM,hDB,hcyc,hcard,_hD,hodd,_hHall,_hTB,_hBR,_hTBn,_hSn,_hfrat,hfixed,
    _hcompl,x,hxT,hxS,_hxB,hpair,_hBD,_hBE,hEL⟩ :=
    source_fixed_free_torus d hG T hST hsingle hL hM hTM hunique
  refine ⟨source_core_splits_of_outside d hG T hST hsingle hL hM hTM hunique x hxT hxS,
    D,hDM,hcyc,hcard,x,hxT,hxS,hEL,?_⟩
  exact source_center_torus_of_choice d hG T hST hsingle hL hM hTM hunique
    D B x hxT (hDM.trans inf_le_right) (Odd.of_dvd_nat hodd (card_dvd_of_le hDB))
    hcard hpair hfixed hEL

end CFSG.Quasithin.Chapter2.LinearShadows.Single
