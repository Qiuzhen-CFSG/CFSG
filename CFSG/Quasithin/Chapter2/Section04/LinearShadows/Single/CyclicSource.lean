module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldActorSource
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.GroupTheory.NormalQuotientOuterAction

/-!
# Cyclic complements in the original single-block setup

The action of H on L/O₂(L) has kernel in O₂(H), which the original local
argument places inside L. Hence H/L embeds in the cyclic outer automorphism
group of PSL₂(2ⁿ). The complements selected by the original Hall-torus
construction are therefore cyclic. The final record retains those actual
tori and splitting maps for the subsequent involution-fusion argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 2.4.12(1), printed p.532, using Lemma 2.4.8.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_single_quotient_cyclic
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let : d.block.Normal := hsingle ▸ d.L0_normal
    IsCyclic (d.H ⧸ d.block) := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hQL : pCore 2 d.H ≤ d.block := by
    intro a ha
    have hcore := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2
    have ha' : (a:G) ∈ (d.block.map d.H.subtype).pCoreIn 2 := by
      change (a:G) ∈ twoCore (d.block.map d.H.subtype)
      rw [hcore]
      exact mem_map_of_mem d.H.subtype ha
    exact (mem_map_iff_mem d.H.subtype_injective).mp (pCoreIn_le 2 _ ha')
  let K := d.block ⧸ pCore 2 d.block
  obtain ⟨F, _, _, hF, _, _, ⟨m⟩, _⟩ := hL.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e : K ≃* Theory.PSL2.Group F := m.quotientIso.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL
  let : IsCyclic (MulAut.Outer (Theory.PSL2.Group F)) := Theory.PSL2.outer_isCyclic F
  let : IsCyclic (MulAut.Outer K) := (MulAut.outerCongr e).isCyclic.mpr inferInstance
  exact isCyclic_of_injective (normalQuotientOuterAction d.block (pCore 2 d.block))
    (normalQuotientOuterAction_injective d.block (pCore 2 d.block)
      ((source_block_quotient_action_kernel d hsingle hL).trans hQL))

theorem source_torus_normalizer_cyclic_of_choice
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (B : Subgroup G)
    (hcomp : IsComplement'
      ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf (T : Subgroup G))
      ((normalizer (B : Set G)).subgroupOf (T : Subgroup G))) :
    IsCyclic (((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (B : Set G)) : Subgroup G) := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let : IsCyclic (d.H ⧸ d.block) :=
    source_single_quotient_cyclic d hG T hST hsingle hL hM hTM hunique
  let A := ((d.S : Subgroup d.H).map d.H.subtype) ⊓ normalizer (B : Set G)
  let f : A →* d.H ⧸ d.block := (QuotientGroup.mk' d.block).comp
    (inclusion (show A ≤ d.H from inf_le_left.trans (map_subtype_le _)))
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro a ha
    have haL : (a:G) ∈ d.block.map d.H.subtype := mem_map_of_mem d.H.subtype
      ((QuotientGroup.eq_one_iff _).mp ha)
    have hd := (source_torus_normalizer_complements_of_choice d hG T hST hsingle hL hM hTM hunique B hcomp).2.2.2.1
    exact Subtype.ext (disjoint_def.mp hd haL a.property)
  exact isCyclic_of_injective f hf


/-- The fixed original Hall tori and their actual cyclic Sylow complement.
Every field is supplied by 2.4.8 and the faithful outer action of 2.4.12(1). -/
structure CyclicTorusSetup (d : MinimalBlockSetup M) (T : Sylow 2 G) (n : ℕ) where
  torus : Subgroup G
  hall : Subgroup G
  torus_le : torus ≤ M ⊓ d.block.map d.H.subtype
  torus_le_hall : torus ≤ hall
  torus_cyclic : IsCyclic torus
  torus_card : Nat.card torus = 2^n-1
  hall_abelian : IsMulCommutative hall
  hall_odd : Odd (Nat.card hall)
  hall_normalizes : hall ≤ normalizer
    (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)
  hall_fixed : Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
    centralizer (hall : Set G) = ⊥
  normal_in_sylow :
    ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf
      (T : Subgroup G)).Normal
  split_ambient : IsComplement'
    ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf (T : Subgroup G))
    ((normalizer (hall : Set G)).subgroupOf (T : Subgroup G))
  split_sylow :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    IsComplement' ((Stellmacher.elementaryAbelianMaxJ S).subgroupOf S)
      ((S ⊓ normalizer (hall : Set G)).subgroupOf S)
  split_block :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    IsComplement' ((d.block.map d.H.subtype).subgroupOf d.H)
      ((S ⊓ normalizer (hall : Set G)).subgroupOf d.H)
  field_cyclic : IsCyclic (((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (hall : Set G)) : Subgroup G)
  outside : ∃ x ∈ T, x ∉ (d.S : Subgroup d.H).map d.H.subtype ∧
    x ∈ normalizer (hall : Set G)
  conjugate_pair : ∀ x ∈ T, x ∉ (d.S : Subgroup d.H).map d.H.subtype →
    x ∈ normalizer (hall : Set G) → hall = torus ⊔ torus.map (MulAut.conj x⁻¹).toMonoidHom
  sylow_normalizes_borel : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer
    ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊔ torus : Subgroup G) : Set G)

/-- Construct the marked torus setup using only the original single-block hypotheses. -/
theorem source_cyclic_torus_setup
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    Nonempty (CyclicTorusSetup d T n) := by
  obtain ⟨D,B,hDM,hDB,hcyc,hcard,_,habelian,hodd,_,_,_,hSn,hRn,_,hfixed,hRTn,hcomp,hout,hpair⟩ :=
    lemma_2_4_8_5 d hG T hST hsingle hL hM hTM hunique
  have hc := source_torus_normalizer_complements_of_choice d hG T hST hsingle hL hM hTM hunique B hcomp
  have hBR := le_sup_right.trans
    ((normal_subgroupOf_iff_le_normalizer (show
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊔ B from le_sup_left)).mp hRn)
  exact ⟨⟨D,B,hDM,hDB,hcyc,hcard,habelian,hodd,hBR,hfixed,hRTn,hcomp,
    hc.2.2.2.2.1,hc.2.2.2.2.2,
    source_torus_normalizer_cyclic_of_choice d hG T hST hsingle hL hM hTM hunique B hcomp,
    hout,hpair,hSn⟩⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
