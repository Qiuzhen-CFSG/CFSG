module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.JointHallSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.OddFixedPoints
/-!
# The original Hall torus has no common fixed point

The natural block calculation puts C_R(D) in C_R(L), using the actual
Thompson decomposition. This subgroup is central in R. The checked Frattini
factorization gives H=L R N_S(B), so H normalizes C_R(B). The outside element
normalizing B and R contradicts the original 2.4.4 normalizer barrier unless
C_R(B)=1. Coprime normalizer–centralizer equality then gives the actual
complement N_T(B) to R in T.

All torus and Frattini data are constructed from the original hypotheses
in the final theorem. Joint abelianity and core absorption remain separate.
Source: Aschbacher–Smith, Lemma 2.4.8(5), printed p.530.
-/
public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_block_core_eq_module
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) :
    pCore 2 (d.block.map d.H.subtype) = ChapterC.blockU (d.block.map d.H.subtype) := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hn : (d.S : Subgroup d.H).map d.H.subtype ≤
      normalizer (d.block.map d.H.subtype : Set G) :=
    (map_mono (show (d.S : Subgroup d.H) ≤ normalizer (d.block : Set d.H) from
      le_normalizer_of_normal)).trans (d.block.le_normalizer_map d.H.subtype)
  have hc := d.single_block_closures hn
  have hu := congrArg (Subgroup.map d.H.subtype) (d.core_source hG T hST).1
  rw [hsingle,map_pCoreIn_of_injective 2 d.block d.H.subtype d.H.subtype_injective,hc.2] at hu
  exact Subgroup.map_injective (d.block.map d.H.subtype).subtype_injective hu.symm

private theorem ambient_sylow_fixed
    (L D : Subgroup G) {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (hcore : pCore 2 L = ChapterC.blockU L) (P : Sylow 2 L)
    (hDL : D ≤ L) (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥) :
    (P : Subgroup L).map L.subtype ⊓ centralizer (D : Set G) ≤ centralizer (L : Set G) := by
  have ho : Odd (Nat.card (D.subgroupOf L)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv]
  have hne : D.subgroupOf L ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map L.subtype) he
    rw [map_subgroupOf_eq_of_le hDL,Subgroup.map_bot] at hh
    exact hD hh
  rintro x ⟨⟨y,hy,rfl⟩,hx⟩
  have hyc : y ∈ centralizer (D.subgroupOf L : Set L) := by
    apply mem_centralizer_iff.mpr
    intro z hz
    exact Subtype.ext ((mem_centralizer_iff.mp hx) z hz)
  have hyz := hL.sylow_odd_fixed_le_center hcore P (D.subgroupOf L) ho hne ⟨hy,hyc⟩
  apply mem_centralizer_iff.mpr
  intro z hz
  exact congrArg Subtype.val (mem_center_iff.mp hyz (⟨z,hz⟩ : L))

theorem source_odd_fixed_centralizes_block
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (D : Subgroup G) (hDL : D ≤ d.block.map d.H.subtype)
    (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    R ⊓ centralizer (D : Set G) ≤ centralizer ((L ⊔ R : Subgroup G) : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let C := S ⊓ centralizer (L : Set G)
  let e := equivMapOfInjective d.block d.H.subtype d.H.subtype_injective
  have hK := hL.of_mulEquiv e
  obtain ⟨P,hP,_⟩ := source_intersection_borel d hsingle hL
  let P' : Sylow 2 L := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP' : (P' : Subgroup L).map L.subtype = S ⊓ L := by
    change ((P : Subgroup d.block).map e.toMonoidHom).map L.subtype = _
    rw [Subgroup.map_map]
    have hf : L.subtype.comp e.toMonoidHom = d.H.subtype.comp d.block.subtype := rfl
    rw [hf,←Subgroup.map_map,hP,map_inf _ _ _ d.H.subtype_injective]
  have hfix : (S ⊓ L) ⊓ centralizer (D : Set G) ≤ centralizer (L : Set G) :=
    hP' ▸ ambient_sylow_fixed L D hK (source_block_core_eq_module d hG T hST hsingle)
      P' hDL hodd hD
  have hd := source_thompson_decomposition d hG T hST hsingle hL
  change R = (S ⊓ L) ⊔ C ∧ R ⊓ L = S ⊓ L ∧ C ≤ centralizer (R : Set G) at hd
  have hCD : C ≤ centralizer (D : Set G) := inf_le_right.trans (centralizer_le hDL)
  have hCP : C ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    ((show C ≤ centralizer (L : Set G) from inf_le_right).trans
      (centralizer_le inf_le_right)).trans (centralizer_le_normalizer _)
  change R ⊓ centralizer (D : Set G) ≤ centralizer ((L ⊔ R : Subgroup G) : Set G)
  rintro r ⟨hr,hDr⟩
  have hrprod : r ∈ ((S ⊓ L : Subgroup G) : Set G) * (C : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hCP,←hd.1]
    exact hr
  obtain ⟨p,hp,c,hc,rfl⟩ := hrprod
  have hpD : p ∈ centralizer (D : Set G) := by
    have hh := (centralizer (D : Set G)).mul_mem hDr
      ((centralizer (D : Set G)).inv_mem (hCD hc))
    simpa only [mul_inv_cancel_right] using hh
  have hrL : p*c ∈ centralizer (L : Set G) :=
    (centralizer (L : Set G)).mul_mem (hfix ⟨hp,hpD⟩) hc.2
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hrC : p*c ∈ C := ⟨hRS hr,hrL⟩
  have hboth : C ≤ centralizer ((L ⊔ R : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp hd.2.2))
  exact hboth hrC

omit [Finite G] in
theorem source_frattini_generation
    (d : MinimalBlockSetup M) (T : Sylow 2 G) (R B : Subgroup G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hRS : R ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hfrat : (T : Set G) = (R : Set G) *
      (((T : Subgroup G) ⊓ normalizer (B : Set G) : Subgroup G) : Set G)) :
    d.H = (d.block.map d.H.subtype ⊔ R) ⊔
      ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (B : Set G)) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  have hS : S = R ⊔ (S ⊓ normalizer (B : Set G)) := by
    apply le_antisymm
    · intro s hs
      have ht : s ∈ (T : Set G) := hST hs
      rw [hfrat] at ht
      obtain ⟨r,hr,b,hb,rfl⟩ := ht
      have hbS : b ∈ S := by
        have hh := S.mul_mem (S.inv_mem (hRS hr)) hs
        simpa only [inv_mul_cancel_left] using hh
      exact mul_mem_sup hr ⟨hbS,hb.2⟩
    · exact sup_le hRS inf_le_left
  have hH : d.H = d.block.map d.H.subtype ⊔ S := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [←Subgroup.map_sup,d.generated,←MonoidHom.range_eq_map,range_subtype]
  apply hH.trans
  conv_lhs => rw [hS]
  rw [sup_assoc]


theorem source_joint_hall_fixed_free
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (D B : Subgroup G) (hDL : D ≤ d.block.map d.H.subtype)
    (hDB : D ≤ B) (hD : D ≠ ⊥) (hodd : Odd (Nat.card B))
    (hfrat : (T : Set G) =
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G) *
      (((T : Subgroup G) ⊓ normalizer (B : Set G) : Subgroup G) : Set G))
    {x : G} (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hxB : x ∈ normalizer (B : Set G)) :
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (B : Set G) = ⊥ := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  have hDodd : Odd (Nat.card D) := Odd.of_dvd_nat hodd (card_dvd_of_le hDB)
  have hfixed := (inf_le_inf_left R (centralizer_le hDB)).trans
    (source_odd_fixed_centralizes_block d hG T hST hsingle hL D hDL hDodd hD)
  exact fixedCentralizer_eq_bot d T hST.le R B hRS (hST.le.trans ht.2.2)
    (source_frattini_generation d T R B hST.le hRS hfrat) hfixed hxT hxS
    (ht.2.2 hxT) hxB

/-- The original Hall torus acts without common fixed points and supplies
an actual complement to the Thompson group in the ambient Sylow subgroup. -/
theorem source_fixed_free_torus
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    ∃ D B : Subgroup G, D ≤ M ⊓ L ∧ D ≤ B ∧ IsCyclic D ∧ Nat.card D = 2^n-1 ∧ D ≠ ⊥ ∧
      Odd (Nat.card B) ∧ IsHallSubgroup OddHall.oddPrimes (B.subgroupOf ((T : Subgroup G) ⊔ D)) ∧
      (T : Subgroup G) ⊔ D = (T : Subgroup G) ⊔ B ∧
      B ≤ normalizer (R : Set G) ∧
      ((T : Subgroup G) ⊔ B) ≤ normalizer ((R ⊔ B : Subgroup G) : Set G) ∧
      S ≤ normalizer ((R ⊔ D : Subgroup G) : Set G) ∧
      (T : Set G) = (R : Set G) * (((T : Subgroup G) ⊓ normalizer (B : Set G) : Subgroup G) : Set G) ∧
      R ⊓ centralizer (B : Set G) = ⊥ ∧
      IsComplement' (R.subgroupOf (T : Subgroup G))
        ((normalizer (B : Set G)).subgroupOf (T : Subgroup G)) ∧
      ∃ x ∈ T, x ∉ S ∧ x ∈ normalizer (B : Set G) ∧
        B = D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom ∧ B ≤ normalizer (D : Set G) ∧
        B ≤ normalizer (D.map (MulAut.conj x⁻¹).toMonoidHom : Set G) ∧
        D.map (MulAut.conj x⁻¹).toMonoidHom ≤ normalizer (L : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  obtain ⟨D,B,hDM,hDB,hcyc,hcard,hD,hodd,hHall,hTB,hBR,hTBn,hSn,hfrat,
    x,hxT,hxS,hxB,hpair⟩ := source_joint_hall_torus d hG T hST hsingle hL hM hTM hunique
  have hfixed := source_joint_hall_fixed_free d hG T hST hsingle hL D B
    (hDM.trans inf_le_right) hDB hD hodd hfrat hxT hxS hxB
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  have hR : IsPGroup 2 R := T.isPGroup'.to_le (hRS.trans hST.le)
  have hcop : Nat.Coprime (Nat.card B) (Nat.card R) := by
    obtain ⟨k,hk⟩ := hR.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hodd).pow_right k
  have hgen : R ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G)) = (T : Subgroup G) := by
    apply le_antisymm (sup_le (hRS.trans hST.le) inf_le_left)
    intro t ht
    have hh : t ∈ (T : Set G) := ht
    rw [hfrat] at hh
    obtain ⟨r,hr,b,hb,rfl⟩ := hh
    exact mul_mem_sup hr hb
  exact ⟨D,B,hDM,hDB,hcyc,hcard,hD,hodd,hHall,hTB,hBR,hTBn,hSn,hfrat,hfixed,
    torusNormalizer_complement (T : Subgroup G) R B (hRS.trans hST.le) ht.2.2
      hBR hcop hfixed hgen,x,hxT,hxS,hxB,hpair⟩

end CFSG.Quasithin.Chapter2.LinearShadows.Single
