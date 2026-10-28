module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.AbsorptionSource
public import CFSG.Quasithin.Chapter2.Section04.QuadraticTorusSource
public import Theory.SpecificGroups.SL2.BorelComplementCard
public import Theory.GroupTheory.Hall.TorusNormalizerExtension
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
/-!
# The complete original joint Hall torus in 2.4.8(5)

On the actual quotient L/O₂(L), conjugation by B induces a canonical
automorphism action. The actual odd subgroup D embeds in the quotient,
and its proved order identifies its image with a Borel complement.
The checked split-torus rigidity theorem makes the two normal cyclic
factors D and Dˣ commute. Every action and quotient premise is constructed
from the selected source subgroups.

The final theorem combines this with the original Hall, Frattini and
fixed-point arguments. It includes the actual set product TB, both normality
steps, the complement N_T(B), and B=DDˣ for every outside element of that
normalizer. No extra model marking or action hypothesis remains.
Source: Aschbacher–Smith 2.4.8(5), printed pp.529–530.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G]

theorem natural_joint_torus_abelian
    (L B D E : Subgroup G) {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (P : Sylow 2 L) (hBL : B ≤ normalizer (L : Set G))
    (hBP : B ≤ normalizer ((P : Subgroup L).map L.subtype : Set G))
    (hDL : D ≤ L) (hDB : D ≤ B) (hEB : E ≤ B) (hgenB : D ⊔ E = B)
    (hBD : B ≤ normalizer (D : Set G)) (hBE : B ≤ normalizer (E : Set G))
    [IsMulCommutative D] [IsMulCommutative E]
    (hodd : Odd (Nat.card D)) (hcard : Nat.card D = 2^n-1) :
    IsMulCommutative B := by
  obtain ⟨hn,_,F,_,_,hF,_,τ,⟨m⟩,_⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let K := L ⧸ pCore 2 L
  let q : L →* K := QuotientGroup.mk' (pCore 2 L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let α : B →* MulAut L := L.normalizerMonoidHom.comp (inclusion hBL)
  let ρ : B →* MulAut K := (quotientAut (pCore 2 L)).comp α
  let ι : D →* K := q.comp (inclusion hDL)
  let D' := D.subgroupOf L
  have hDodd : Odd (Nat.card D') := by
    change Odd (Nat.card (D.subgroupOf L))
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv]
  have hdis : Disjoint (P : Subgroup L) D' := by
    obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.coprime_two_left.mpr hDodd).pow_left k
  have hkP : pCore 2 L ≤ (P : Subgroup L) := pCore_isPGroup.le_sylow_of_normal P
  have hi : Function.Injective ι := by
    apply (MonoidHom.ker_eq_bot_iff ι).mp
    apply eq_bot_iff.mpr
    intro d hd
    apply Subtype.ext
    have hdcore : inclusion hDL d ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp hd
    exact congrArg (fun z : L => (z : G)) (disjoint_def.mp hdis (hkP hdcore) d.property)
  have hρeval (b : B) (l : L) : ρ b (q l) = q (α b l) :=
    quotientAut_apply_mk (pCore 2 L) (α b) l
  have hcompat (b : B) (d : D) :
      ρ b (ι d) = ι (D.normalizerMonoidHom ⟨b,hBD b.property⟩ d) := by
    change ρ b (q (inclusion hDL d)) = q (inclusion hDL
      (D.normalizerMonoidHom ⟨b,hBD b.property⟩ d))
    rw [hρeval]
    congr 1
  have hinner (d : D) : ρ ⟨d,hDB d.property⟩ = MulAut.conj (ι d) := by
    apply MulEquiv.ext
    intro z
    obtain ⟨l,rfl⟩ := hq z
    rw [hρeval]
    change q (α ⟨d,hDB d.property⟩ l) = q (inclusion hDL d) * q l * (q (inclusion hDL d))⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    congr 1
  have hαP (b : B) : (P : Subgroup L).map (α b).toMonoidHom = P := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_map]
    have he : L.subtype.comp (α b).toMonoidHom = (MulAut.conj (b:G)).toMonoidHom.comp L.subtype := by
      ext l
      rfl
    rw [he,←Subgroup.map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (hBP b.property)
  have hDP : D' ≤ normalizer (P : Set L) := by
    intro d hd
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he : MulAut.conj d = α ⟨d,hDB hd⟩ := by
      ext l
      rfl
    rw [he]
    exact hαP ⟨d,hDB hd⟩
  let Q : Sylow 2 K := P.mapSurjective hq
  have hQpre : (Q : Subgroup K).comap q = P := comap_map_eq_self (by
    intro l hl
    exact hkP ((QuotientGroup.eq_one_iff l).mp hl))
  have hNpre : (normalizer (Q : Set K)).comap q = normalizer (P : Set L) := by
    change (normalizer ((Q : Subgroup K) : Set K)).comap q =
      normalizer ((P : Subgroup L) : Set L)
    rw [comap_normalizer_eq_of_surjective _ hq,hQpre]
  have hNmap : (normalizer (P : Set L)).map q = normalizer (Q : Set K) := by
    rw [←hNpre,map_comap_eq_self_of_surjective hq]
  have hιrange : ι.range = D'.map q := by
    ext z
    constructor
    · rintro ⟨d,rfl⟩
      exact ⟨inclusion hDL d,d.property,rfl⟩
    · rintro ⟨d,hd,rfl⟩
      exact ⟨⟨d,hd⟩,rfl⟩
  let qF := m.quotientIso.toMonoidHom.comp q
  have hqF : Function.Surjective qF := m.quotientIso.surjective.comp hq
  have hkF : qF.ker ≤ (P : Subgroup L) := by
    intro l hl
    exact hkP ((QuotientGroup.eq_one_iff l).mp (m.quotientIso.map_eq_one_iff.mp hl))
  have hDcard : Nat.card D' = Nat.card F-1 := by
    change Nat.card (D.subgroupOf L) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv,hcard,hF]
  have hPD : (P : Subgroup L) ⊔ D' = normalizer (P : Set L) :=
    Matrix.SpecialLinearGroup.sylow_normalizer_complement_of_card qF hqF P hkF D' hDP hdis hDcard
  have hQN : ι.range ≤ normalizer (Q : Set K) := by
    rw [hιrange,←hNmap]
    exact map_mono hDP
  have hQgen : (Q : Subgroup K) ⊔ ι.range = normalizer (Q : Set K) := by
    rw [hιrange]
    change (P : Subgroup L).map q ⊔ D'.map q = _
    rw [←Subgroup.map_sup,hPD,hNmap]
  have hQdis : Disjoint (Q : Subgroup K) ι.range := by
    obtain ⟨k,hk⟩ := Q.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    have ho : Odd (Nat.card ι.range) := by
      rw [hιrange]
      exact Odd.of_dvd_nat hDodd (card_map_dvd D' q)
    exact (Nat.coprime_two_left.mpr ho).pow_left k
  have hroot (b : B) (_hb : (b:G) ∈ E) : (Q : Subgroup K).map (ρ b).toMonoidHom = Q := by
    change ((P : Subgroup L).map q).map (ρ b).toMonoidHom = (P : Subgroup L).map q
    rw [Subgroup.map_map]
    have he : (ρ b).toMonoidHom.comp q = q.comp (α b).toMonoidHom := by
      ext l
      exact hρeval b l
    rw [he,←Subgroup.map_map,hαP]
  exact (Section04.abelian_torus_product_of_linear_quotient hn hF m.quotientIso B D E hgenB
    hDB hEB hBD hBE ι hi ρ hcompat hinner Q hQN hQdis hQgen hroot).1
end CFSG.Quasithin.Chapter2.LinearShadows.Single

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem lemma_2_4_8_5
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
      IsMulCommutative B ∧ Odd (Nat.card B) ∧
      IsHallSubgroup OddHall.oddPrimes (B.subgroupOf ((T : Subgroup G) ⊔ D)) ∧
      (T : Subgroup G) ⊔ D = (T : Subgroup G) ⊔ B ∧
      (((T : Subgroup G) ⊔ D : Subgroup G) : Set G) = (T : Set G) * (B : Set G) ∧
      S ≤ normalizer ((R ⊔ D : Subgroup G) : Set G) ∧
      (R.subgroupOf (R ⊔ B)).Normal ∧
      ((R ⊔ B).subgroupOf ((T : Subgroup G) ⊔ B)).Normal ∧
      R ⊓ centralizer (B : Set G) = ⊥ ∧
      (R.subgroupOf (T : Subgroup G)).Normal ∧
      IsComplement' (R.subgroupOf (T : Subgroup G))
        ((normalizer (B : Set G)).subgroupOf (T : Subgroup G)) ∧
      (∃ x ∈ T, x ∉ S ∧ x ∈ normalizer (B : Set G)) ∧
      ∀ x ∈ T, x ∉ S → x ∈ normalizer (B : Set G) →
        B = D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  obtain ⟨D,B,hDM,hDB,hcyc,hcard,hD,hodd,hHall,hTB,hBR,hTBn,hSn,hfrat,hfixed,
    hcompl,x,hxT,hxS,hxB,hpair,hBD,hBE,hEL⟩ :=
    source_fixed_free_torus d hG T hST hsingle hL hM hTM hunique
  let E := D.map (MulAut.conj x⁻¹).toMonoidHom
  have hEB : E ≤ B := le_sup_right.trans_eq hpair.symm
  have hDL : D ≤ L := hDM.trans inf_le_right
  have hBL : B ≤ normalizer (L : Set G) := by
    rw [hpair]
    exact sup_le (hDL.trans L.le_normalizer) hEL
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  obtain ⟨P,hP⟩ := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.1
  let := hcyc
  let eD : D ≃* E := (MulAut.conj x⁻¹).subgroupMap D
  let : IsMulCommutative E := ⟨⟨fun a b => eD.symm.injective (by
    rw [map_mul,map_mul,mul_comm'])⟩⟩
  have hBabelian : IsMulCommutative B := natural_joint_torus_abelian L B D E hK P hBL
    (hP.symm ▸ hBR) hDL hDB hEB hpair.symm hBD hBE
    (Odd.of_dvd_nat hodd (card_dvd_of_le hDB)) hcard
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  have hRtwo : IsPGroup 2 R := T.isPGroup'.to_le (hRS.trans hST.le)
  have hRBle : R ⊔ B ≤ (T : Subgroup G) ⊔ B := sup_le_sup_right (hRS.trans hST.le) B
  have hRn : (R.subgroupOf (R ⊔ B)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le R.le_normalizer hBR)
  have hRBn : ((R ⊔ B).subgroupOf ((T : Subgroup G) ⊔ B)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hRBle).mpr hTBn
  have hprod : (((T : Subgroup G) ⊔ D : Subgroup G) : Set G) = (B : Set G) * (T : Set G) := by
    rw [hTB]
    exact torus_extension_set_product R (T : Subgroup G) B (hRS.trans hST.le) hBR
      (le_sup_left.trans hTBn)
  have hprod' : (((T : Subgroup G) ⊔ D : Subgroup G) : Set G) = (T : Set G) * (B : Set G) := by
    simpa only [inv_coe_set,mul_inv_rev] using congrArg (fun A : Set G => A⁻¹) hprod
  have hRTn : (R.subgroupOf (T : Subgroup G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hRS.trans hST.le)).mpr ht.2.2
  exact ⟨D,B,hDM,hDB,hcyc,hcard,hD,hBabelian,hodd,hHall,hTB,hprod',hSn,hRn,hRBn,
    hfixed,hRTn,hcompl,⟨x,hxT,hxS,hxB⟩,
    odd_joint_torus_pair_for_all S (T : Subgroup G) R D B hST.le ht.1 hRtwo hodd hDB
      ht.2.2 hBR hSn x hxT hxS hpair hBD⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
