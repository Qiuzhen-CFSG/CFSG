module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.NormalBlockRank.A3Contract
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The actual A₃ action and the extended core-quotient map

Automorphisms of a short group act on its literal module U/C_U(L). The
identity [U,L] = U implies that this action is nontrivial. When L/O₂(L)
has order three, its action is consequently faithful. For the A₃ natural
module, the automorphism group has order six. In a three-group extension,
the overgroup image therefore still has order three, giving a homomorphism
extending L → L/O₂(L).

The subgroup and module transport construction follows the existing proofs
in Chapter E, Hyperplanes/Enlargement/BlockInspection/Transport, and the
block automorphism action in Chapter 15, FieldFourCentrality/SourceCubicActor/
Commutation. Their later chapter interfaces are not needed here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), C.1.7--13,
printed pp.123--125, and the normal-block inference in E.6.14, printed p.251.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.NormalBlockRank
open ChapterC

section Transport
variable {A B : Type*} [Group A] [Group B]

private theorem transport_blockU (e : A ≃* B) :
    (blockU A).map e.toMonoidHom = blockU B := by
  rw [blockU, map_commutator, pCore_map_iso,
    map_top_of_surjective _ e.surjective, blockU]

private def blockUEquiv (e : A ≃* B) : blockU A ≃* blockU B :=
  (e.subgroupMap (blockU A)).trans (MulEquiv.subgroupCongr (transport_blockU e))

private theorem transport_blockFixed (e : A ≃* B) :
    (blockFixed A).map (blockUEquiv e).toMonoidHom = blockFixed B := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.centerCongr e ⟨x, hx⟩).property
  · intro x hx
    exact ⟨(blockUEquiv e).symm x,
      (Subgroup.centerCongr e).symm ⟨x, hx⟩ |>.property,
      (blockUEquiv e).apply_symm_apply x⟩

private def blockModuleEquiv (e : A ≃* B) : BlockModule A ≃* BlockModule B :=
  QuotientGroup.congr _ _ (blockUEquiv e) (transport_blockFixed e)

private def blockAut : MulAut A →* MulAut (BlockModule A) where
  toFun := blockModuleEquiv
  map_one' := by
    ext u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed A) u
    rfl
  map_mul' a b := by
    ext u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed A) u
    rfl
end Transport

private theorem intrinsic_action_nontrivial {L : Type*} [Group L]
    (h : IsShort L) (ρ : L →* MulAut (BlockModule L))
    (hρ : ∀ (l : L) (u : blockU L),
      ρ l (QuotientGroup.mk' (blockFixed L) u) =
        QuotientGroup.mk' (blockFixed L) (blockConjugate L l u)) : ρ ≠ 1 := by
  let := h.finite
  have hUU : ⁅blockU L, (⊤ : Subgroup L)⁆ = blockU L :=
    commutator_isPPerfect_idempotent (⊤ : Subgroup L) (pCore 2 L)
      (h.twoPerfect.of_surjective (topEquiv : (⊤ : Subgroup L) ≃* L).symm.toMonoidHom
        (topEquiv : (⊤ : Subgroup L) ≃* L).symm.surjective)
      pCore_isPGroup le_normalizer_of_normal
  intro he
  have hc : ⁅(⊤ : Subgroup L), blockU L⁆ ≤ center L := by
    apply commutator_le.mpr
    intro l _ u hu
    have hh := hρ l ⟨u, hu⟩
    rw [he] at hh
    have hq : QuotientGroup.mk' (blockFixed L) (blockConjugate L l ⟨u, hu⟩) =
        QuotientGroup.mk' (blockFixed L) ⟨u, hu⟩ := hh.symm
    have hh := QuotientGroup.eq_iff_div_mem.mp hq
    change (l * u * l⁻¹) / u ∈ center L at hh
    simpa only [commutatorElement_def, div_eq_mul_inv] using hh
  rw [commutator_comm, hUU] at hc
  have heq : blockU L ⊓ center L = blockU L := inf_eq_left.mpr hc
  exact h.irreducible.1.ne heq

private theorem intrinsic_action_kernel {L : Type*} [Group L]
    (h : IsShort L) (hcard : Nat.card (L ⧸ pCore 2 L) = 3)
    (ρ : L →* MulAut (BlockModule L))
    (hρ : ∀ (l : L) (u : blockU L),
      ρ l (QuotientGroup.mk' (blockFixed L) u) =
        QuotientGroup.mk' (blockFixed L) (blockConjugate L l u)) :
    ρ.ker = pCore 2 L := by
  let f := QuotientGroup.lift (pCore 2 L) ρ (h.core_le_moduleAction_ker ρ hρ)
  let : Fact (Nat.card (L ⧸ pCore 2 L)).Prime := ⟨hcard ▸ Nat.prime_three⟩
  have hi : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases f.ker.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact hbot
    · exfalso
      apply intrinsic_action_nontrivial h ρ hρ
      apply MonoidHom.ext
      intro l
      exact (show f (QuotientGroup.mk' (pCore 2 L) l) = 1 from
        show QuotientGroup.mk' (pCore 2 L) l ∈ f.ker from htop ▸ mem_top _)
  apply le_antisymm
  · intro l hl
    apply (QuotientGroup.eq_one_iff _).mp
    exact hi (hl.trans (map_one f).symm)
  · exact h.core_le_moduleAction_ker ρ hρ


private theorem range_card_three {G B : Type*} [Group G] [Finite G] [Group B]
    [Finite B] (N : Subgroup G) [N.Normal] (f : G →* B)
    (hN : Nat.card (f.comp N.subtype).range = 3)
    (hB : Nat.card B = 6) (hq : IsPGroup 3 (G ⧸ N)) : Nat.card f.range = 3 := by
  let r := f.rangeRestrict
  let M := N.map r
  let : M.Normal := Subgroup.Normal.map inferInstance r f.rangeRestrict_surjective
  have hMr : M.map f.range.subtype = (f.comp N.subtype).range := by
    rw [map_map, MonoidHom.range_comp, range_subtype]
    rfl
  have hcM : Nat.card M = 3 := by
    rw [← card_map_of_injective f.range.subtype_injective, hMr]
    exact hN
  let q := (QuotientGroup.mk' M).comp r
  have hker : N ≤ q.ker := by
    intro n hn
    exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem r hn)
  let t := QuotientGroup.lift N q hker
  have ht : Function.Surjective t := QuotientGroup.lift_surjective_of_surjective N q
    ((QuotientGroup.mk'_surjective M).comp f.rangeRestrict_surjective) hker
  have hqM : IsPGroup 3 (f.range ⧸ M) := hq.of_surjective t ht
  have hi : M.index ∣ 2 := by
    have hd : 3 * M.index ∣ 3 * 2 := by
      have hd := f.range.card_subgroup_dvd_card
      rw [hB, ← M.card_mul_index, hcM] at hd
      exact hd
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hd
  have hi1 : M.index = 1 := by
    obtain ⟨n, hn⟩ := hqM.exists_card_eq
    change Nat.card (f.range ⧸ M) = 1
    exact Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 3 2).pow_left n)
      (hn ▸ dvd_refl _) hi
  have hc := M.card_mul_index
  rw [hcM, hi1, mul_one] at hc
  exact hc.symm

/-- In a three-group extension of a normal short group with core quotient of
order three and natural module of order four, the actual module action extends
the canonical core quotient map. -/
theorem exists_three_quotient_retraction {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : IsShort N)
    (hquot : Nat.card (N ⧸ pCore 2 N) = 3)
    (hmodule : Nat.card (BlockModule N) = 4)
    (hq : IsPGroup 3 (G ⧸ N)) :
    ∃ r : G →* (N ⧸ pCore 2 N), ∀ n : N,
      r (n : G) = QuotientGroup.mk' (pCore 2 N) n := by
  let ρ : G →* MulAut (BlockModule N) := blockAut.comp MulAut.conjNormal
  let a := ρ.comp N.subtype
  have ha (n : N) (u : blockU N) :
      a n (QuotientGroup.mk' (blockFixed N) u) =
        QuotientGroup.mk' (blockFixed N) (blockConjugate N n u) := rfl
  have hk : a.ker = pCore 2 N := intrinsic_action_kernel hN hquot a ha
  have hc : Nat.card a.range = 3 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange a).toEquiv]
    rw [hk]
    exact hquot
  let := hN.module_elementary
  let := hN.module_nontrivial
  let : IsKleinFour (BlockModule N) := ⟨hmodule, IsElementaryAbelian.exponent_eq_prime⟩
  have hcρ : Nat.card ρ.range = 3 :=
    range_card_three N ρ hc (IsKleinFour.card_mulAut (BlockModule N)) hq
  let r := ρ.rangeRestrict
  let b := r.comp N.subtype
  have hkb : b.ker = pCore 2 N := by
    rw [← hk]
    ext n
    exact Subtype.ext_iff
  let c := QuotientGroup.lift (pCore 2 N) b hkb.ge
  have hci : Function.Injective c := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro x hx
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 N) x
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hkb ▸ (show n ∈ b.ker from hx)
  have hcb : Function.Bijective c :=
    (Nat.bijective_iff_injective_and_card c).mpr ⟨hci, hquot.trans hcρ.symm⟩
  let e : (N ⧸ pCore 2 N) ≃* ρ.range := MulEquiv.ofBijective c hcb
  refine ⟨e.symm.toMonoidHom.comp r, ?_⟩
  intro n
  apply e.injective
  change e (e.symm (r (n : G))) = e (QuotientGroup.mk' (pCore 2 N) n)
  rw [MulEquiv.apply_symm_apply]
  rfl

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.NormalBlockRank

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open NormalBlockRank ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The A₃ construction from the literal relative normal subgroup and natural
module; no splitting or rank bound is assumed. -/
theorem alternatingThreeQuotientRetractionInput : AlternatingThreeQuotientRetractionInput G := by
  intro J L hLJ hn hL hq
  let := hn
  let e := subgroupOfEquivOfLe hLJ
  have hN : IsShort (L.subgroupOf J) := hL.2.1.of_mulEquiv e.symm
  have hc : Nat.card ((L.subgroupOf J) ⧸ pCore 2 (L.subgroupOf J)) = 3 := by
    obtain ⟨a⟩ := hL.2.2.quotient_iso
    let eQ := QuotientGroup.congr (pCore 2 (L.subgroupOf J)) (pCore 2 L) e
      (pCore_map_iso 2 e)
    rw [Nat.card_congr (eQ.trans a).toEquiv, nat_card_alternatingGroup]
    norm_num
  have hm : Nat.card (BlockModule (L.subgroupOf J)) = 4 := by
    rw [Nat.card_congr (blockModuleEquiv e).toEquiv, hL.module_card_odd (by decide)]
    rfl
  exact exists_three_quotient_retraction (L.subgroupOf J) hN hc hm hq

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
