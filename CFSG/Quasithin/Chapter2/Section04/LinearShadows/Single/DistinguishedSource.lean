module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OvergroupSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.TorusAlternativesSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ElementarySource

/-!
# The original distinguished elementary subgroup

Define the subgroup of Notation 2.4.15 using its literal two branches.
The source torus calculations give its order, and the original elementary
pair puts it in Z(R). Its normalizer and TI property in the nontrivial-center
branch follow from the complete 2.4.11 source proof.

Source: Aschbacher–Smith, 2.4.15–16 and 2.4.18, printed pp.533–534.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original subgroup Z of Notation 2.4.15, embedded in G. -/
@[expose] noncomputable def distinguishedZ (d : MinimalBlockSetup M) : Subgroup G := by
  classical
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  exact if center L = ⊥ then R ⊓ centralizer (R : Set G) else (center L).map L.subtype

omit [Finite G] in
theorem distinguishedZ_of_centerless (d : MinimalBlockSetup M)
    (hZ : center (d.block.map d.H.subtype) = ⊥) :
    distinguishedZ d =
      let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      R ⊓ centralizer (R : Set G) := by
  simp only [distinguishedZ, hZ, ite_true]

omit [Finite G] in
theorem distinguishedZ_of_center_ne_bot (d : MinimalBlockSetup M)
    (hZ : center (d.block.map d.H.subtype) ≠ ⊥) :
    distinguishedZ d = (center (d.block.map d.H.subtype)).map
      (d.block.map d.H.subtype).subtype := by
  simp only [distinguishedZ, hZ, ite_false]

/-- The distinguished elementary subgroup has order q, lies in Z(R), and
is normalized by S, as in original 2.4.16(1). -/
theorem source_distinguished_elementary
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    IsElementaryAbelian 2 (distinguishedZ d) ∧ Nat.card (distinguishedZ d) = 2^n ∧
      distinguishedZ d ≤ R ⊓ centralizer (R : Set G) ∧
      S ≤ normalizer (distinguishedZ d : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule L
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hcore := source_block_core_eq_module d hG T hST hsingle
  have hRL : R ≤ L := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  have hp := source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS
  have hZU : R ⊓ centralizer (R : Set G) ≤ U := hp.ge.trans inf_le_left
  have hUR : U ≤ R := by
    change sourceModule (d.block.map d.H.subtype) ≤ R
    rw [(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2]
    exact le_sSup (d.core_source hG T hST).2.2
  let : IsElementaryAbelian 2 U := by
    change IsElementaryAbelian 2 ((ChapterC.blockU L).map L.subtype)
    let := hK.2.1.elementary
    exact IsElementaryAbelian.map L.subtype
  by_cases hz : center L = ⊥
  · rw [distinguishedZ_of_centerless d hz]
    obtain ⟨D,B,hDM,hDB,_,hcard,_,hodd,_,_,hBR,_,_,_,_,_,_,_,_,_,_,_,_⟩ :=
      source_fixed_free_torus d hG T hST hsingle hL hM hTM hunique
    have hr := source_centerless_torus_regular d hG T hST hsingle hL hM hTM hunique hz
      D (hDM.trans inf_le_right)
      (hodd.of_dvd_nat (card_dvd_of_le hDB)) hcard (hDB.trans hBR)
    have hSR : S ≤ normalizer (R : Set G) :=
      hST.le.trans (d.lemma_2_4_8_1 hG T hST hsingle hK).2.2
    exact ⟨IsElementaryAbelian.of_injective (inclusion hZU) (inclusion_injective hZU),
      hr.1,le_rfl,(le_inf hSR (hSR.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf⟩
  · rw [distinguishedZ_of_center_ne_bot d hz]
    have hZL : (center L).map L.subtype ≤ U := map_mono (hK.center_le_module hcore)
    have hZR : (center L).map L.subtype ≤ R ⊓ centralizer (R : Set G) := by
      refine le_inf (hZL.trans hUR) ?_
      rintro z ⟨a,ha,rfl⟩ r hr
      exact congrArg Subtype.val (mem_center_iff.mp ha (⟨r,hRL hr⟩ : L))
    let : d.block.Normal := hsingle ▸ d.L0_normal
    have hHL : d.H ≤ normalizer (L : Set G) := by
      have hh := d.block.le_normalizer_map d.H.subtype
      rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    obtain ⟨_,_,_,_,_,_,_,_,_,hc⟩ :=
      source_center_torus_and_splitting d hG T hST hsingle hL hM hTM hunique
    exact ⟨IsElementaryAbelian.of_injective (inclusion hZL) (inclusion_injective hZL),
      (card_map_of_injective L.subtype_injective).trans (hc.resolve_left hz).1,
      hZR,(map_subtype_le _).trans (hHL.trans
        (normalizer_le_normalizer_characteristic_image L (center L)))⟩

/-- In the centerless case every element of T fixes the original Z as a subgroup. -/
theorem source_distinguished_normalized_by_sylow
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hz : center (d.block.map d.H.subtype) = ⊥) :
    (T : Subgroup G) ≤ normalizer (distinguishedZ d : Set G) := by
  rw [distinguishedZ_of_centerless d hz]
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hTR := (d.lemma_2_4_8_1 hG T hST hsingle hK).2.2
  exact (le_inf hTR (hTR.trans (normalizer_le_normalizer_centralizer _))).trans
    inf_normalizer_le_normalizer_inf

/-- Original 2.4.18 in the nontrivial-center branch, retaining the literal
normalizer of Q. -/
theorem source_distinguished_TI_of_center_ne_bot
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥) :
    ChapterI.Section06To08.IsTISubgroup (distinguishedZ d) ∧
      normalizer (distinguishedZ d : Set G) = normalizer (twoCore d.H : Set G) := by
  rw [distinguishedZ_of_center_ne_bot d hz]
  have h := lemma_2_4_11_3 d hG T hST hsingle hL hM hTM hunique hz
  exact ⟨h.1,h.2.symm⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
